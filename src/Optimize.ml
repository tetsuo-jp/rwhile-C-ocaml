(* Optimize.ml -- optimisation passes of the R-WHILE-S -> R-WHILE compiler.
 *
 * The passes here obey one rule: their output is an ordinary R-WHILE program
 * (or an ordinary p2d encoding of one).  Nothing downstream -- the
 * self-interpreter examples/ri.rwhile, the specialiser examples/spec_av.rwhile,
 * the Agda core in proofs/agda -- needs to know that a pass ran.  That is what
 * makes these wins survive compilation, unlike constructs that only pay off
 * while the richer surface language is being executed directly.
 *
 * PASS 1: variable numbering by static access weight.
 *
 *   Program2DataRwhile.program2data renumbers a program's variables to 1..n in
 *   FIRST-OCCURRENCE order, and the self-interpreter's store is a list indexed
 *   by that number -- so reading variable i walks i cells (DLOOKUP/DUPDATE).
 *   Numbering the hot variables first shortens every one of those walks.
 *
 *   Measured on this machine (2026-08-06): with the executed workload held
 *   fixed at 4 commands, self-interpretation costs 387 + 20*k steps in the
 *   number k of declared variables -- exactly linear, and charged even for
 *   variables the run never touches.  Store traversal, not dispatch, is what
 *   the self-interpreter spends its time on.
 *
 *   The weight is the classic static heuristic: one point per occurrence,
 *   multiplied by `loop_weight` for every enclosing loop, since those are the
 *   occurrences that get executed repeatedly.  Conditionals do not scale the
 *   weight (either branch may be taken).  Ties keep first-occurrence order, so
 *   the pass is deterministic and is the identity on programs whose variables
 *   already happen to be sorted by weight. *)

open AbsRwhile

let loop_weight = 10

(* every occurrence of a variable in [xs], each worth [w] *)
let at (w : int) (xs : rIdent list) : (rIdent * int) list =
  List.map (fun x -> (x, w)) xs

let rec wcom (w : int) (c : com) : (rIdent * int) list =
  match c with
  | CSeq (a, b)         -> wcom w a @ wcom w b
  | CMac (_, xs)        -> at w xs
  | CAss (x, e)         -> (x, w) :: at w (Subst.varsExp e)
  | CRep (p, q)         -> at w (Subst.varsPat p @ Subst.varsPat q)
  | CCond (e, t, el, f) -> at w (Subst.varsExp e @ Subst.varsExp f)
                           @ wthen w t @ welse w el
  | CLoop (e, d, l, f)  -> let w' = w * loop_weight in
                           at w' (Subst.varsExp e @ Subst.varsExp f)
                           @ wdo w' d @ wloop w' l
  | CShow e             -> at w (Subst.varsExp e)
  | CLocal (x, b)       -> (x, w) :: wcom w b
  | CAutoFi (e, t, el)  -> at w (Subst.varsExp e) @ wthen w t @ welse w el
  | CArrAss (x, i, e)   -> (x, w) :: at w (Subst.varsExp i @ Subst.varsExp e)
  (* surface sugar: weigh what it expands to, so the pass sees the real
     accesses (a for-loop's counter is touched once per iteration) *)
  | (CCase _ | CSkip | CAssert _ | CSwap _ | CLocalD _ | CFor _
    | CPush _ | CPop _) as c -> wcom w (Desugar.desugar_com c)

and wthen w = function BThen c -> wcom w c | BThenNone -> []
and welse w = function BElse c -> wcom w c | BElseNone -> []
and wdo   w = function BDo   c -> wcom w c | BDoNone   -> []
and wloop w = function BLoop c -> wcom w c | BLoopNone -> []

(* The program's variables, hottest first.  [p] must already be
   macro-expanded: this returns a permutation of EvalRwhile.varProgram p. *)
let weight_of (p : program) : rIdent -> int =
  let Prog (_, x, c, y) = p in
  (* the read and write variables are touched once each, at the very ends *)
  let ws = (x, 1) :: (y, 1) :: wcom 1 c in
  fun v -> List.fold_left (fun a (u, k) -> if u = v then a + k else a) 0 ws

let var_order (p : program) : rIdent list =
  let weight = weight_of p in
  let vs = EvalRwhile.varProgram p in
  (* stable, so variables of equal weight keep first-occurrence order *)
  List.stable_sort (fun a b -> compare (weight b) (weight a)) vs

(* PASS 2: slot sharing (linear-scan register allocation over the store).
 *
 *   Measured on this machine (2026-08-06): with the program TEXT held fixed and
 *   only the number of distinct variables varied, self-interpretation costs
 *   387 + 20*n steps in the number n of distinct variables -- while adding 70
 *   unexecuted commands that reuse one variable costs exactly NOTHING.  So the
 *   store's LENGTH is what is charged, not the program's size.  Giving two
 *   variables the same slot therefore saves 20 steps, every time.
 *
 *   Soundness comes from R-WHILE's own invariant.  Every variable is nil at the
 *   start, must be nil at the end (all_cleared), and can only change value at
 *   one of its own occurrences.  Hence a variable is nil BEFORE its first
 *   occurrence and nil AFTER its last one, and two variables whose occurrence
 *   intervals are disjoint are never both non-nil.  They can share a slot.
 *
 *   Two corrections to that argument:
 *
 *   - LOOPS.  A variable set in one iteration and cleared in the next is
 *     non-nil between them, which is outside its textual interval.  So an
 *     interval that meets a loop is widened to that whole loop (to a fixpoint,
 *     for nesting).
 *   - CONDITIONALS need no correction, and this is where the win is: the arms
 *     are alternatives, so scratch confined to the then-arm and scratch
 *     confined to the else-arm are never live together.  A variable that spans
 *     the arms has an interval covering both and is excluded automatically.
 *
 *   The read variable is live from before the first command, the write variable
 *   until after the last, so they get sentinel occurrences at either end.
 *
 *   Disjoint intervals form an interval graph, where greedy colouring in order
 *   of interval start is optimal -- the colour count equals the largest number
 *   of simultaneously live variables. *)

(* occurrence positions, and the extent of every loop, in pre-order *)
let scan (Prog (_, rd, c, wr) : program)
    : (rIdent * int) list * (int * int) list * int =
  let occs = ref [] and loops = ref [] and pos = ref 0 in
  let add v = occs := (v, !pos) :: !occs in
  let adds vs = List.iter add vs in
  let rec go c =
    incr pos;
    let start = !pos in
    (match c with
     | CSeq (a, b)         -> go a; go b
     | CMac (_, xs)        -> adds xs
     | CAss (v, e)         -> add v; adds (Subst.varsExp e)
     | CRep (p, q)         -> adds (Subst.varsPat p @ Subst.varsPat q)
     | CCond (e, t, el, f) -> adds (Subst.varsExp e @ Subst.varsExp f);
                              gothen t; goelse el
     | CLoop (e, d, l, f)  -> adds (Subst.varsExp e @ Subst.varsExp f);
                              godo d; goloop l;
                              loops := (start, !pos) :: !loops
     | CShow e             -> adds (Subst.varsExp e)
     | CLocal (v, b)       -> add v; go b
     | CAutoFi (e, t, el)  -> adds (Subst.varsExp e); gothen t; goelse el
     | CArrAss (v, i, e)   -> add v; adds (Subst.varsExp i @ Subst.varsExp e)
     | (CCase _ | CSkip | CAssert _ | CSwap _ | CLocalD _ | CFor _
       | CPush _ | CPop _) as c -> go (Desugar.desugar_com c))
  and gothen = function BThen c -> go c | BThenNone -> ()
  and goelse = function BElse c -> go c | BElseNone -> ()
  and godo   = function BDo   c -> go c | BDoNone   -> ()
  and goloop = function BLoop c -> go c | BLoopNone -> () in
  occs := [(rd, 0)];                       (* read: live from before the body *)
  go c;
  let last = !pos + 1 in
  occs := (wr, last) :: !occs;             (* write: live until after it *)
  (!occs, !loops, last)

let live_intervals (p : program) : (rIdent * (int * int)) list =
  let (occs, loops, _) = scan p in
  let vs = EvalRwhile.varProgram p in
  let raw v =
    List.fold_left
      (fun acc (u, i) -> if u = v then match acc with
                                       | None -> Some (i, i)
                                       | Some (lo, hi) -> Some (min lo i, max hi i)
                         else acc)
      None occs in
  (* widen across every loop the interval meets, to a fixpoint (nested loops) *)
  let rec widen iv =
    let iv' =
      List.fold_left
        (fun (lo, hi) (ls, le) ->
           if lo <= le && ls <= hi then (min lo ls, max hi le) else (lo, hi))
        iv loops in
    if iv' = iv then iv else widen iv' in
  List.filter_map
    (fun v -> match raw v with
              | None -> None                       (* cannot happen: v occurs *)
              | Some iv -> Some (v, widen iv))
    vs

(* variable -> the numeral name of its store slot.  Variables with disjoint
   (widened) intervals share a slot. *)
let slot_alloc (p : program) : (rIdent * rIdent) list =
  let ivs = live_intervals p in
  (* greedy by interval start; `ends` records each slot's current last end *)
  let ordered =
    List.stable_sort (fun (_, (a, _)) (_, (b, _)) -> compare a b) ivs in
  let ends : (int * int) list ref = ref [] in     (* slot number -> last end *)
  let assign (lo, hi) =
    let rec pick = function
      | [] -> let n = List.length !ends + 1 in
              ends := !ends @ [(n, hi)]; n
      | (n, e) :: rest -> if e < lo then begin
                            ends := List.map (fun (m, f) -> if m = n then (m, hi) else (m, f)) !ends;
                            n
                          end else pick rest in
    pick !ends in
  let raw = List.map (fun (v, iv) -> (v, assign iv)) ordered in
  (* Numbering the slots in ALLOCATION order throws away pass 1: a hot variable
     can land in a high slot and every lookup then walks past the cold ones.
     Measured before this step: `minus` got 7% SLOWER and `lookup_ppl2015` 13%
     slower, even though both had fewer slots.  So number the slots by the
     access weight of the variables sharing them, hottest first -- passes 1 and
     2 compose instead of fighting. *)
  let weight = weight_of p in
  let slots = List.sort_uniq compare (List.map snd raw) in
  let slot_weight n =
    List.fold_left (fun a (v, m) -> if m = n then a + weight v else a) 0 raw in
  let ranked = List.stable_sort (fun a b -> compare (slot_weight b) (slot_weight a)) slots in
  let number n =
    let rec idx i = function
      | [] -> i
      | m :: rest -> if m = n then i else idx (i + 1) rest in
    idx 1 ranked in
  List.map (fun (v, n) -> (v, RIdent (string_of_int (number n)))) raw
