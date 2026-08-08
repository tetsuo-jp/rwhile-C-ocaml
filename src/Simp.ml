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

let rec copyprop_fix whole c =
  let c' = copyprop_com whole c in
  if c' = c then c else copyprop_fix c' c'

let copyprop_program (Prog (ms, i, body, o) : program) : program =
  Prog (ms, i, copyprop_fix body body, o)

let simpProgram (Prog (ms, i, body, o) : program) : program =
  let ms' = List.map (fun (Mac (n, args, b)) -> Mac (n, args, simp_fix b)) ms in
  Prog (ms', i, simp_fix body, o)
