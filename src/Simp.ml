(* Simp: a semantics- and reversibility-preserving simplifier for R-WHILE
 * residual programs (idea 1: optimising specialisation).
 *
 * Two safe transformations:
 *   1. Constant folding of CLOSED (variable-free) expressions, performed by the
 *      real evaluator on the empty store (so it is correct by construction).
 *   2. Dead reversible-branch elimination: a conditional whose entry test AND
 *      exit assertion are both closed constants of matching truth has one dead
 *      branch and trivially-satisfied assertions, so it reduces to the live
 *      branch:
 *        if E then C else D fi F   with  E,F constant TRUE   ==>  C
 *        if E then C else D fi F   with  E,F constant FALSE  ==>  D
 *      This is exactly the dead code a specialiser leaves after resolving a
 *      static dispatch (e.g. `if =? Op 'swap` with Op statically 'swap).
 *
 * Both preserve meaning and reversibility (the dropped branch is never executed
 * forwards OR backwards, and the constant assertions always hold). Truth is
 * R-WHILE's: a value is true iff it is non-nil (EvalRwhile.is_true). *)

open AbsRwhile

let rec closed_exp = function
  | EVal _              -> true
  | EVar _ | EArrGet _  -> false
  | ECons (a, b) | EEq (a, b) -> closed_exp a && closed_exp b
  | EHd a | ETl a | EPair a   -> closed_exp a
  | EList es            -> List.for_all closed_exp es

(* fold a closed expression to a literal via the real evaluator; leave it if the
 * evaluation would be undefined (e.g. hd of nil). *)
let rec simpExp (e : exp) : exp =
  let e' = match e with
    | ECons (a, b)   -> ECons (simpExp a, simpExp b)
    | EHd a          -> EHd (simpExp a)
    | ETl a          -> ETl (simpExp a)
    | EEq (a, b)     -> EEq (simpExp a, simpExp b)
    | EPair a        -> EPair (simpExp a)
    | EList es       -> EList (List.map simpExp es)
    | EArrGet (v, i) -> EArrGet (v, simpExp i)
    | EVar _ | EVal _ -> e
  in
  if closed_exp e' then
    (try EVal (EvalRwhile.evalExp EvalRwhile.RIdentMap.empty e') with _ -> e')
  else e'

(* truth of a folded expression, if it is a closed constant *)
let const_truth (e : exp) : bool option =
  match e with
  | EVal _ when closed_exp e ->
     (try Some (EvalRwhile.is_true (EvalRwhile.evalExp EvalRwhile.RIdentMap.empty e)) with _ -> None)
  | _ -> None

let rec simpCom (c : com) : com =
  match c with
  | CSeq (a, b) -> CSeq (simpCom a, simpCom b)
  | CAss (x, e) -> CAss (x, simpExp e)
  | CRep _      -> c
  | CMac _      -> c
  | CShow e     -> CShow (simpExp e)
  | CLocal (x, c1) -> CLocal (x, simpCom c1)
  | CArrAss (x, i, e) -> CArrAss (x, simpExp i, simpExp e)
  | CAutoFi (e, t, el) -> CAutoFi (simpExp e, simpThen t, simpElse el)
  | (CCase _ | CSkip | CAssert _ | CSwap _ | CLocalD _ | CFor _ | CPush _ | CPop _) -> simpCom (Desugar.desugar_com c)
  | CLoop (e, d, l, f) -> CLoop (simpExp e, simpDo d, simpLoop l, simpExp f)
  | CCond (e, t, el, f) ->
     let e' = simpExp e and f' = simpExp f in
     let t' = simpThen t and el' = simpElse el in
     (match const_truth e', const_truth f' with
      | Some true,  Some true  -> (match t'  with BThen c1 -> c1 | BThenNone -> CCond (e', t', el', f'))
      | Some false, Some false -> (match el' with BElse c1 -> c1 | BElseNone -> CCond (e', t', el', f'))
      | _ -> CCond (e', t', el', f'))

and simpThen = function BThen c -> BThen (simpCom c) | BThenNone -> BThenNone
and simpElse = function BElse c -> BElse (simpCom c) | BElseNone -> BElseNone
and simpDo   = function BDo c -> BDo (simpCom c)     | BDoNone -> BDoNone
and simpLoop = function BLoop c -> BLoop (simpCom c) | BLoopNone -> BLoopNone

(* apply to fixpoint (folds can expose further dead branches) *)
let rec simp_fix (c : com) : com =
  let c' = simpCom c in
  if c' = c then c else simp_fix c'

(* ===== Copy propagation over residual moves =====
 *
 * Fuses  `T <= K ; ... ; <pattern containing T> <= ...`  into the later command,
 * deleting the move.  Motivation (2026-08-08): capture-on-escape in spec_av
 * removes the nested-pattern bound of fp1-via-ri_fp3, but emits `Tmp <= ('var.k)`
 * at EVERY escape, overwhelmingly for slots that are never reused -- a 13x blow-up
 * of the fp1 residual.  Those redundant captures are exactly a copy: a fresh temp
 * written once, read once, with its source untouched in between.
 *
 * Conditions, all checked (each is load-bearing in a reversible language):
 *   - the move is `CRep (PVar t, PVar k)` with t <> k;
 *   - t occurs EXACTLY TWICE in the whole program.  That pins t as a fresh temp
 *     whose only definition is this move and whose only other mention is the use
 *     we are about to rewrite -- no aliasing, nothing else observes it;
 *   - the second occurrence is inside the SOURCE pattern of a later CRep in the
 *     same straight-line spine.  A CRep's source pattern CONSUMES its variables,
 *     so t is dead afterwards.  An expression read (`X ^= T`) is NOT eligible:
 *     `^=` reads without consuming, so removing the move would move the residue
 *     from t to k and change which variables end non-nil;
 *   - k does not occur anywhere between the two, so k still holds the value at
 *     the use (this is what makes the move-chain of an XOR-free residual safe);
 *   - both commands sit on the same top-level CSeq spine, so no branch or loop
 *     boundary separates them.
 *
 * Meaning and reversibility are preserved: `t <= k` moves the value and leaves t
 * dead, so substituting k for its single consuming use computes the same thing
 * with one fewer variable, forwards and backwards alike. *)

let rec occ_pat t = function
  | PVar (Var x) -> if x = t then 1 else 0
  | PCons (a, b) -> occ_pat t a + occ_pat t b
  | PList ps -> List.fold_left (fun n p -> n + occ_pat t p) 0 ps
  | PVal _ -> 0

let rec occ_exp t = function
  | EVar (Var x) -> if x = t then 1 else 0
  | EArrGet (Var x, e) -> (if x = t then 1 else 0) + occ_exp t e
  | ECons (a, b) | EEq (a, b) -> occ_exp t a + occ_exp t b
  | EHd a | ETl a | EPair a -> occ_exp t a
  | EList es -> List.fold_left (fun n e -> n + occ_exp t e) 0 es
  | EVal _ -> 0

let rec occ_com t = function
  | CSeq (a, b) -> occ_com t a + occ_com t b
  | CAss (x, e) -> (if x = t then 1 else 0) + occ_exp t e
  | CRep (p, q) -> occ_pat t p + occ_pat t q
  | CCond (e, th, el, f) ->
     occ_exp t e + occ_exp t f
     + (match th with BThen c -> occ_com t c | BThenNone -> 0)
     + (match el with BElse c -> occ_com t c | BElseNone -> 0)
  | CLoop (e, d, l, f) ->
     occ_exp t e + occ_exp t f
     + (match d with BDo c -> occ_com t c | BDoNone -> 0)
     + (match l with BLoop c -> occ_com t c | BLoopNone -> 0)
  | CShow e -> occ_exp t e
  | CLocal (x, c) -> (if x = t then 1 else 0) + occ_com t c
  | CAutoFi (e, th, el) ->
     occ_exp t e
     + (match th with BThen c -> occ_com t c | BThenNone -> 0)
     + (match el with BElse c -> occ_com t c | BElseNone -> 0)
  | CArrAss (x, i, e) -> (if x = t then 1 else 0) + occ_exp t i + occ_exp t e
  | CMac (_, xs) -> List.fold_left (fun n x -> if x = t then n + 1 else n) 0 xs
  | c -> occ_com t (Desugar.desugar_com c)

let rec subst_pat t k = function
  | PVar (Var x) when x = t -> PVar (Var k)
  | PCons (a, b) -> PCons (subst_pat t k a, subst_pat t k b)
  | PList ps -> PList (List.map (subst_pat t k) ps)
  | p -> p

(* flatten / rebuild the top-level CSeq spine (right-nested as the parser makes it) *)
let rec spine = function CSeq (a, b) -> spine a @ spine b | c -> [c]
let rebuild = function
  | [] -> CSkip
  | c :: cs -> List.fold_left (fun acc x -> CSeq (acc, x)) c cs

let copyprop_com (whole : com) (c : com) : com =
  let cmds = Array.of_list (spine c) in
  let n = Array.length cmds in
  let removed = Array.make n false in
  for i = 0 to n - 1 do
    if not removed.(i) then
      match cmds.(i) with
      | CRep (PVar (Var (RIdent t)), PVar (Var (RIdent k))) when t <> k ->
         (* t must be a write-once read-once temp across the WHOLE program *)
         if occ_com (RIdent t) whole = 2 then begin
           (* find its single other mention on this spine *)
           let j = ref (-1) in
           for x = i + 1 to n - 1 do
             if !j < 0 && not removed.(x) && occ_com (RIdent t) cmds.(x) > 0 then j := x
           done;
           if !j >= 0 then begin
             let j = !j in
             (* the use must consume t: it is the source pattern of a CRep *)
             let consuming = match cmds.(j) with
               | CRep (dst, src) -> occ_pat (RIdent t) src = 1
                                    && occ_pat (RIdent t) dst = 0
               | _ -> false in
             (* k must be untouched in between *)
             let k_clear = ref true in
             for x = i + 1 to j - 1 do
               if occ_com (RIdent k) cmds.(x) > 0 then k_clear := false
             done;
             if consuming && !k_clear then begin
               (match cmds.(j) with
                | CRep (dst, src) ->
                   cmds.(j) <- CRep (dst, subst_pat (RIdent t) (RIdent k) src)
                | _ -> ());
               removed.(i) <- true
             end
           end
         end
      | _ -> ()
  done;
  let kept = ref [] in
  for i = n - 1 downto 0 do
    if not removed.(i) then kept := cmds.(i) :: !kept
  done;
  rebuild !kept

(* ===== identity commands (2026-08-09) =====
 *
 * Attributing the ri_fp3-route residuals command by command (`./measure_proj
 * jones-attr`) showed that the straight-line subjects spend part of their step
 * count on commands that are the IDENTITY on every store:
 *
 *   x <= x     evalPat reads x and clears it, inv_evalPat writes the same value
 *              back into the now-nil x.  It cannot fail (the write-conflict
 *              check is satisfied by the read that precedes it) and it cannot
 *              change the store.  Unconditionally the identity.
 *   x ^= nil   rupdate's third case (`vx = VNil -> vy`), matching the
 *              three-case `rupd` of proofs/agda/RWhileTime.agda.  Also
 *              unconditionally the identity.
 *
 * Both are their OWN syntactic inverses (InvRwhile swaps a CRep's patterns and
 * leaves a CAss alone), so removing them commutes with program inversion, and
 * neither removes a failure case -- which is why only these two shapes are
 * removed and, e.g., an adjacent pair `x <= y; y <= x` is NOT (that one is the
 * identity too, but only when y was already nil, so dropping it would turn an
 * erroring program into a succeeding one).
 *
 * `x ^= x` -- the reversible CLEAR -- is a different command and must survive.
 *
 * Measured effect on `./measure_proj jones-self` (steps of the residual):
 * id 3->1, id2 7->3, id3 11->7, rep 7->3, sx_splitjoin 23->21, sx_three 35->33;
 * id2 and rep thereby move from "above p+" to "at or below p+". *)
let is_noop_com = function
  | CRep (PVar (Var x), PVar (Var y)) -> x = y
  | CAss (_, EVal v) -> EvalRwhile.desugar_val v = VNil
  | _ -> false

(* Drop the identities on one CSeq spine.  Never returns an empty command: a
 * body of nothing but identities keeps one of them, because `rebuild []` is
 * CSkip and CSkip is surface sugar that Program2DataRwhile refuses to encode. *)
let drop_noops_spine (c : com) : com =
  let cmds = spine c in
  match List.filter (fun x -> not (is_noop_com x)) cmds with
  | [] -> (match cmds with [] -> c | x :: _ -> x)
  | kept -> rebuild kept

(* Fuse on this spine, then recurse into every nested block.  comp2 keeps the
 * overwhelming majority of its nodes inside loop bodies, so a spine-only pass
 * cannot reach the part that matters.  Soundness is unchanged: the whole-program
 * "exactly twice" test already forces both occurrences into the same block, and
 * within one execution of that block the reasoning is the straight-line one --
 * the use consumes t, so t is nil again when the block is re-entered.
 *
 * MEASURED 2026-08-08, AND IT CHANGES NOTHING YET.  comp2 stays at 400531 nodes
 * and every fp1 residual is byte-identical with and without the recursion.  This
 * is NOT the mis-sampling that once made -share-slots look worthless (see
 * RWHILE_S.md): the sample here IS the loop-heavy target.  The reason is that
 * comp2's loop-body temps do not satisfy the write-once/read-once test -- they
 * are mentioned elsewhere as well, so the whole-program "exactly twice" gate
 * rejects them.  Kept because it is sound, tested and free.
 *
 * AND THE GATE IS NOT THE PROBLEM EITHER (measured the same day with
 * copyprop_report, below).  On comp2: moves=21, fused=0, all 21 rejected as
 * multi_occ.  Twenty-one variable-to-variable moves in a program with 1040
 * CReps and 400531 nodes -- so even a PERFECT gate could remove 21 commands.
 * The 363969 nodes inside comp2's loop bodies are not made of fusable moves at
 * all: comp2 averages ~113 nodes per command, so its bulk is what the commands
 * CARRY, not the command count.  Shrinking comp2 therefore means shrinking
 * encoded data, not eliminating moves.  Do not spend more effort on liveness
 * analysis here.
 *
 * WHAT THE COMMANDS CARRY, measured 2026-08-08 (Encoding.breakdown,
 * ./measure_proj full).  The guess written here first -- "patterns and embedded
 * constants" -- was WRONG.  Patterns are 0.9% of comp2 and constants 1.0%:
 * 91.9% is the UNARY VARIABLE NUMERALS.  The two levers on that, with their
 * closed-form limits, are in RWHILE_S.md ("符号化のノードはどこへ行っているか"). *)
let rec copyprop_blocks whole c =
  (* Identity removal runs in the same fixpoint: fusing a move can expose an
   * `x <= x`, and removing one lowers an occurrence count by two, which can in
   * turn let the write-once/read-once gate accept a move it had rejected. *)
  let c = drop_noops_spine (copyprop_com whole c) in
  let rec go = function
    | CSeq (a, b) -> CSeq (go a, go b)
    | CCond (e, th, el, f) ->
       CCond (e,
              (match th with BThen x -> BThen (copyprop_blocks whole x) | b -> b),
              (match el with BElse x -> BElse (copyprop_blocks whole x) | b -> b),
              f)
    | CLoop (e, d, l, f) ->
       CLoop (e,
              (match d with BDo x -> BDo (copyprop_blocks whole x) | b -> b),
              (match l with BLoop x -> BLoop (copyprop_blocks whole x) | b -> b),
              f)
    | CLocal (x, b) -> CLocal (x, copyprop_blocks whole b)
    | other -> other
  in
  go c

let rec copyprop_fix whole c =
  let c' = copyprop_blocks whole c in
  if c' = c then c else copyprop_fix c' c'

(* Why a move was NOT fused.  The gate is a global "t occurs exactly twice", and
 * on comp2 it rejects essentially everything inside loop bodies -- but "rejected"
 * covers four different reasons, and they call for different weakenings.  This
 * counts them so the next attempt starts from data rather than from a guess. *)
type cp_report = {
  mutable moves : int;           (* CRep (PVar t, PVar k) candidates, t <> k *)
  mutable fused : int;           (* would fuse under the current gate *)
  mutable multi_occ : int;       (* t occurs more than twice in the program *)
  mutable no_use : int;          (* no later occurrence of t on this spine *)
  mutable not_consuming : int;   (* the use reads t without consuming it *)
  mutable src_clobbered : int;   (* k is touched between the move and the use *)
}

let copyprop_report (Prog (_, _, body, _) : program) : cp_report =
  let r = { moves = 0; fused = 0; multi_occ = 0; no_use = 0;
            not_consuming = 0; src_clobbered = 0 } in
  let rec block c =
    let cmds = Array.of_list (spine c) in
    let n = Array.length cmds in
    for i = 0 to n - 1 do
      (match cmds.(i) with
       | CRep (PVar (Var t), PVar (Var k)) when t <> k ->
          r.moves <- r.moves + 1;
          if occ_com t body <> 2 then r.multi_occ <- r.multi_occ + 1
          else begin
            let j = ref (-1) in
            for x = i + 1 to n - 1 do
              if !j < 0 && occ_com t cmds.(x) > 0 then j := x
            done;
            if !j < 0 then r.no_use <- r.no_use + 1
            else begin
              let j = !j in
              let consuming = match cmds.(j) with
                | CRep (dst, src) -> occ_pat t src = 1 && occ_pat t dst = 0
                | _ -> false in
              let k_clear = ref true in
              for x = i + 1 to j - 1 do
                if occ_com k cmds.(x) > 0 then k_clear := false
              done;
              if not consuming then r.not_consuming <- r.not_consuming + 1
              else if not !k_clear then r.src_clobbered <- r.src_clobbered + 1
              else r.fused <- r.fused + 1
            end
          end
       | _ -> ());
      (* recurse into nested blocks *)
      (match cmds.(i) with
       | CCond (_, th, el, _) ->
          (match th with BThen x -> block x | _ -> ());
          (match el with BElse x -> block x | _ -> ())
       | CLoop (_, d, l, _) ->
          (match d with BDo x -> block x | _ -> ());
          (match l with BLoop x -> block x | _ -> ())
       | CLocal (_, x) -> block x
       | _ -> ())
    done in
  block body; r

let copyprop_program (Prog (ms, i, body, o) : program) : program =
  Prog (ms, i, copyprop_fix body body, o)

(* ===== p+ : the program-preserving version of a program (2026-08-09) =====
 *
 * `program_preserving p` is the program computing
 *
 *     [p+](d) = ( p2d p . [p](d) )
 *
 * i.e. p with its own encoding carried to the output.  It is p's body followed
 * by two commands: assign the (constant) encoding to a fresh variable, and pair
 * it with p's output pattern-wise.  Both are reversible: the assignment sets a
 * nil slot, and the replacement consumes the two slots it reads.
 *
 * WHY IT EXISTS.  A reversible Futamura projection needs a PROGRAM-PRESERVING
 * interpreter rint ([rint](p2d p, d) = (p2d p . [p](d))), so the fp1 residual
 * [spec](rint, p) is obliged to reproduce the program too.  Comparing that
 * residual with p -- the classical Jones-optimality criterion -- charges it for
 * work p never does.  p+ is the smallest EXTENSION of p carrying the residual's
 * OBLIGATION (not the smallest program with it: see RWhileJonesRevCE.agda),
 * so `residual <= p+` is the criterion's reversible form.  (The three values
 * [p+](d), [rint](p2d p, d) and [residual](d) are equal, which is checked in the
 * `jones-self` test group and by `./measure_proj jones-self`.)
 *
 * The two fresh names are `P-SELF` / `OUT-PP`; `RIdent`s from real programs are
 * generated by p2d or written by hand and none of the subjects uses them. *)
let program_preserving (Prog (ms, xin, body, yout) : program) : program =
  let pd = Program2DataRwhile.program2data (Prog (ms, xin, body, yout)) in
  let self = RIdent "P-SELF" and out = RIdent "OUT-PP" in
  Prog (ms, xin,
        CSeq (CSeq (body, CAss (self, EVal pd)),
              CRep (PVar (Var out), PCons (PVar (Var self), PVar (Var yout)))),
        out)

let simpProgram (Prog (ms, i, body, o) : program) : program =
  let ms' = List.map (fun (Mac (n, args, b)) -> Mac (n, args, simp_fix b)) ms in
  Prog (ms', i, simp_fix body, o)
