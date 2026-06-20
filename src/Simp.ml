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
    (try EVal (EvalRwhile.evalExp [] e') with _ -> e')
  else e'

(* truth of a folded expression, if it is a closed constant *)
let const_truth (e : exp) : bool option =
  match e with
  | EVal _ when closed_exp e ->
     (try Some (EvalRwhile.is_true (EvalRwhile.evalExp [] e)) with _ -> None)
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
  | CCase _     -> simpCom (Desugar.desugar_com c)
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

let simpProgram (Prog (ms, i, body, o) : program) : program =
  let ms' = List.map (fun (Mac (n, args, b)) -> Mac (n, args, simp_fix b)) ms in
  Prog (ms', i, simp_fix body, o)
