(* Core.ml — a minimal reversible CORE intermediate representation for R-WHILE.
 *
 * This is an abstraction layer over the full AST that makes correctness easier
 * to check: it mirrors EXACTLY the machine-checked Agda model
 * (proofs/agda/RWhileRevFull.agda) — reversible primitives, sequencing, the
 * reversible conditional and the reversible loop — with nothing else (no
 * macros, no surface extensions, no branch-option noise).
 *
 *   - `elaborate` : full `com` (post-macro) -> `core`   (desugars everything)
 *   - `eval_core` : evaluate a core program; the CONTROL structure mirrors
 *     EvalRwhile, and the ATOMIC operations are REUSED from EvalRwhile
 *     (evalExp / evalPat / inv_evalPat / rupdate), so the core is faithful to
 *     the interpreter by construction.
 *   - `inv_core`  : core inversion; matches InvRwhile.invCom AND the Agda `inv`.
 *
 * Correctness then reduces to: (a) `elaborate` is faithful (checked by
 * differential tests against the real evaluator), and (b) the small core, whose
 * reversibility/determinism is machine-checked in Agda. *)

open AbsRwhile

type prim =
  | PAss of rIdent * exp        (* CAss x e : reversible XOR-assignment *)
  | PRep of pat * pat           (* CRep q r : read r, write q (pattern replacement) *)

type core =
  | Skip
  | Prim of prim
  | Seq  of core * core
  | Cond of exp * core * core * exp   (* if e then c else d fi f *)
  | Loop of exp * core * core * exp   (* from e do D loop L until f *)

(* ---------- elaboration: full com (post-macro) -> core ---------- *)

let rec elaborate : com -> core = function
  | CSeq (c, d)         -> Seq (elaborate c, elaborate d)
  | CAss (x, e)         -> Prim (PAss (x, e))
  | CRep (q, r)         -> Prim (PRep (q, r))
  | CCond (e, t, el, f) -> Cond (e, elab_then t, elab_else el, f)
  | CLoop (e, d, l, f)  -> Loop (e, elab_do d, elab_loop l, f)
  | CShow _             -> Skip   (* store-preserving; printing has no core meaning *)
  | CMac _              -> failwith "Core.elaborate: macros must be expanded first"
  | CLocal _ | CAutoFi _ | CArrAss _ ->
      failwith "Core.elaborate: surface extension not in the reversible core"
and elab_then = function BThen c -> elaborate c | BThenNone -> Skip
and elab_else = function BElse c -> elaborate c | BElseNone -> Skip
and elab_do   = function BDo c   -> elaborate c | BDoNone   -> Skip
and elab_loop = function BLoop c -> elaborate c | BLoopNone -> Skip

(* ---------- evaluation (control mirrors EvalRwhile; atoms reused) ---------- *)

let rec eval_core (s : EvalRwhile.store) : core -> EvalRwhile.store = function
  | Skip               -> s
  | Prim (PAss (x, e)) -> EvalRwhile.rupdate (x, EvalRwhile.evalExp s e) s
  | Prim (PRep (q, r)) -> let (s1, v) = EvalRwhile.evalPat s r in
                          EvalRwhile.inv_evalPat s1 (q, v)
  | Seq (c, d)         -> eval_core (eval_core s c) d
  | Cond (e, c, d, f)  ->
      if EvalRwhile.is_true (EvalRwhile.evalExp s e) then
        let s1 = eval_core s c in
        if EvalRwhile.is_true (EvalRwhile.evalExp s1 f) then s1
        else failwith "Core: cond then-branch exit assertion failed"
      else
        let s1 = eval_core s d in
        if EvalRwhile.evalExp s1 f = VNil then s1
        else failwith "Core: cond else-branch exit assertion failed"
  | Loop (e, d, l, f)  ->
      if EvalRwhile.is_true (EvalRwhile.evalExp s e)
      then eval_loop (eval_core s d) e d l f
      else failwith "Core: loop entry assertion failed"

and eval_loop s e d l f =
  if EvalRwhile.is_true (EvalRwhile.evalExp s f) then s
  else
    let s1 = eval_core s l in
    if EvalRwhile.evalExp s1 e <> VNil then
      failwith "Core: loop reversibility assertion failed (entry test not false after body)";
    let s2 = eval_core s1 d in
    eval_loop s2 e d l f

(* ---------- inversion (matches InvRwhile.invCom and Agda `inv`) ---------- *)

let rec inv_core : core -> core = function
  | Skip               -> Skip
  | Prim (PAss (x, e)) -> Prim (PAss (x, e))          (* self-inverse *)
  | Prim (PRep (q, r)) -> Prim (PRep (r, q))          (* swap patterns *)
  | Seq (c, d)         -> Seq (inv_core d, inv_core c)
  | Cond (e, c, d, f)  -> Cond (f, inv_core c, inv_core d, e)
  | Loop (e, d, l, f)  -> Loop (f, inv_core d, inv_core l, e)

(* ---------- run a whole program through the core (mirrors evalProgram) ---------- *)

let eval_program_core (p : program) (v : valT) : valT =
  let p' = MacroRwhile.expMacProgram p in
  let Prog (_, x, c, y) = p' in
  let s  = List.map (fun z -> (z, VNil)) (EvalRwhile.varProgram p') in
  let s1 = EvalRwhile.rupdate (x, EvalRwhile.desugar_val v) s in
  let s2 = eval_core s1 (elaborate c) in
  EvalRwhile.evalVariable s2 (Var y)
