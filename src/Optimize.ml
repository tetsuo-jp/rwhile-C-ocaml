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
let var_order (p : program) : rIdent list =
  let Prog (_, x, c, y) = p in
  (* the read and write variables are touched once each, at the very ends *)
  let ws = (x, 1) :: (y, 1) :: wcom 1 c in
  let weight v = List.fold_left (fun a (u, k) -> if u = v then a + k else a) 0 ws in
  let vs = EvalRwhile.varProgram p in
  (* stable, so variables of equal weight keep first-occurrence order *)
  List.stable_sort (fun a b -> compare (weight b) (weight a)) vs
