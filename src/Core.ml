(* Core.ml — a minimal reversible CORE intermediate representation for R-WHILE.
 *
 * An abstraction layer over the full AST that makes correctness easier to check:
 * it is a small, SELF-CONTAINED reversible language (its own normalized
 * expressions `cexp`, patterns `cpat`, commands `core`) mirroring the
 * machine-checked Agda model (proofs/agda/RWhileRevFull, RWhileExec).  Surface
 * sugar (list literals) is desugared and surface extensions (arrays, local,
 * autofi) are rejected, so the core has no incidental complexity.
 *
 *   - normalize:  exp -> cexp,  pat -> cpat   (desugar list sugar; reject extensions)
 *   - elaborate:  com (post-macro) -> core
 *   - eval_core / eval_cexp / read_cpat / write_cpat : the small core semantics,
 *     mirroring EvalRwhile exactly (only the store layer rupdate/update is shared)
 *   - inv_core:   core inversion; matches InvRwhile.invCom AND the Agda `inv`.
 *
 * Faithfulness is checked by the `core-ir` differential tests against the real
 * evaluator; reversibility/involution of the core is machine-checked in Agda. *)

open AbsRwhile

(* ---------- normalized expressions and patterns ---------- *)

type cexp =
  | XVar  of rIdent
  | XVal  of valT                 (* already desugared (no VList) *)
  | XCons of cexp * cexp
  | XHd   of cexp
  | XTl   of cexp
  | XEq   of cexp * cexp
  | XPair of cexp

type cpat =
  | YVar  of rIdent
  | YVal  of valT
  | YCons of cpat * cpat

type prim =
  | PAss of rIdent * cexp         (* CAss x e : reversible XOR-assignment *)
  | PRep of cpat * cpat           (* CRep q r : read r, write q (pattern replacement) *)

type core =
  | Skip
  | Prim of prim
  | Seq  of core * core
  | Cond of cexp * core * core * cexp   (* if e then c else d fi f *)
  | Loop of cexp * core * core * cexp   (* from e do D loop L until f *)

(* ---------- normalization (full exp/pat -> core exp/pat) ---------- *)

let rec norm_exp : exp -> cexp = function
  | EVar (Var x)  -> XVar x
  | EVal v        -> XVal (EvalRwhile.desugar_val v)
  | ECons (a, b)  -> XCons (norm_exp a, norm_exp b)
  | EHd e         -> XHd (norm_exp e)
  | ETl e         -> XTl (norm_exp e)
  | EEq (a, b)    -> XEq (norm_exp a, norm_exp b)
  | EPair e       -> XPair (norm_exp e)
  | EList es      -> List.fold_right (fun e acc -> XCons (norm_exp e, acc)) es (XVal VNil)
  | EArrGet _     -> failwith "Core: array (extension) not in the reversible core"

let rec norm_pat : pat -> cpat = function
  | PVar (Var x)  -> YVar x
  | PVal v        -> YVal (EvalRwhile.desugar_val v)
  | PCons (a, b)  -> YCons (norm_pat a, norm_pat b)
  | PList ps      -> List.fold_right (fun p acc -> YCons (norm_pat p, acc)) ps (YVal VNil)

(* ---------- elaboration: full com (post-macro) -> core ---------- *)

let rec elaborate : com -> core = function
  | CSeq (c, d)         -> Seq (elaborate c, elaborate d)
  | CAss (x, e)         -> Prim (PAss (x, norm_exp e))
  | CRep (q, r)         -> Prim (PRep (norm_pat q, norm_pat r))
  | CCond (e, t, el, f) -> Cond (norm_exp e, elab_then t, elab_else el, norm_exp f)
  | CLoop (e, d, l, f)  -> Loop (norm_exp e, elab_do d, elab_loop l, norm_exp f)
  | CShow _             -> Skip   (* store-preserving; printing has no core meaning *)
  | CMac _              -> failwith "Core.elaborate: macros must be expanded first"
  | CLocal _ | CAutoFi _ | CArrAss _ ->
      failwith "Core.elaborate: surface extension not in the reversible core"
  | CCase _ as c -> elaborate (Desugar.desugar_com c)  (* normally desugared upstream *)
and elab_then = function BThen c -> elaborate c | BThenNone -> Skip
and elab_else = function BElse c -> elaborate c | BElseNone -> Skip
and elab_do   = function BDo c   -> elaborate c | BDoNone   -> Skip
and elab_loop = function BLoop c -> elaborate c | BLoopNone -> Skip

(* ---------- core semantics (mirrors EvalRwhile; only the store layer shared) ---------- *)

let vtrue  = VCons (VNil, VNil)
let is_true (v : valT) = v <> VNil

let eval_var (s : EvalRwhile.store) (x : rIdent) : valT =
  try List.assoc x s with Not_found -> failwith "Core: unbound variable"

let rec eval_cexp (s : EvalRwhile.store) : cexp -> valT = function
  | XVar x      -> eval_var s x
  | XVal v      -> v
  | XCons (a,b) -> VCons (eval_cexp s a, eval_cexp s b)
  | XHd e       -> (match eval_cexp s e with VCons (h,_) -> h | _ -> failwith "Core: hd of non-cons")
  | XTl e       -> (match eval_cexp s e with VCons (_,t) -> t | _ -> failwith "Core: tl of non-cons")
  | XEq (a,b)   -> if eval_cexp s a = eval_cexp s b then vtrue else VNil
  | XPair e     -> (match eval_cexp s e with VCons _ -> vtrue | _ -> VNil)

(* read a pattern (consuming its variables): returns (new store, value) *)
let rec read_cpat (s : EvalRwhile.store) : cpat -> EvalRwhile.store * valT = function
  | YCons (q,r) -> let (s1,d1) = read_cpat s q in
                   let (s2,d2) = read_cpat s1 r in (s2, VCons (d1,d2))
  | YVar x      -> (EvalRwhile.update (x, VNil) s, eval_var s x)
  | YVal v      -> (s, v)

(* write a value into a pattern (vars must be nil; literals must match) *)
let rec write_cpat (s : EvalRwhile.store) (p : cpat) (v : valT) : EvalRwhile.store =
  match p, v with
  | YCons (p1,p2), VCons (v1,v2) -> write_cpat (write_cpat s p1 v1) p2 v2
  | YVar x, _ -> if eval_var s x = VNil then EvalRwhile.update (x, v) s
                 else failwith "Core: pattern write conflict (target not nil)"
  | YVal w, _ -> if v = w then s else failwith "Core: pattern literal mismatch"
  | YCons _, _ -> failwith "Core: cons pattern against non-cons value"

let rec eval_core (s : EvalRwhile.store) : core -> EvalRwhile.store = function
  | Skip               -> s
  | Prim (PAss (x, e)) -> EvalRwhile.rupdate (x, eval_cexp s e) s
  | Prim (PRep (q, r)) -> let (s1, v) = read_cpat s r in write_cpat s1 q v
  | Seq (c, d)         -> eval_core (eval_core s c) d
  | Cond (e, c, d, f)  ->
      if is_true (eval_cexp s e) then
        let s1 = eval_core s c in
        if is_true (eval_cexp s1 f) then s1
        else failwith "Core: cond then-branch exit assertion failed"
      else
        let s1 = eval_core s d in
        if eval_cexp s1 f = VNil then s1
        else failwith "Core: cond else-branch exit assertion failed"
  | Loop (e, d, l, f)  ->
      if is_true (eval_cexp s e)
      then eval_loop (eval_core s d) e d l f
      else failwith "Core: loop entry assertion failed"

and eval_loop s e d l f =
  if is_true (eval_cexp s f) then s
  else
    let s1 = eval_core s l in
    if eval_cexp s1 e <> VNil then
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
