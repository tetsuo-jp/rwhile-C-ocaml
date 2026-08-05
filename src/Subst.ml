open AbsRwhile
open List

type subst = (rIdent * rIdent) list

let substRIdent (ss : subst) (x : rIdent) : rIdent =
  try assoc x ss with Not_found -> x

let substVariable ss (Var x) = Var (substRIdent ss x)

let rec substExp ss = function
    ECons (e, f) -> ECons (substExp ss e, substExp ss f)
  | EHd e -> EHd (substExp ss e)
  | ETl e -> ETl (substExp ss e)
  | EEq (e, f) -> EEq (substExp ss e, substExp ss f)
  | EPair e -> EPair (substExp ss e)
  | EVar x -> EVar (substVariable ss x)
  | EVal v -> EVal v
  | EList es -> EList (List.map (substExp ss) es)
  | EArrGet (x, i) -> EArrGet (substVariable ss x, substExp ss i)

and substPat ss = function
    PCons (q, r) -> PCons (substPat ss q, substPat ss r)
  | PVar x -> PVar (substVariable ss x)
  | PVal v -> PVal v
  | PList ps -> PList (List.map (substPat ss) ps)

and substCom ss = function
    CMac (m, xs) -> let xs' = map (fun y -> try assoc y ss with Not_found -> y) xs
                    in CMac (m, xs')
  | CAss (x, e) -> CAss (substRIdent ss x, substExp ss e)
  | CRep (q, r) -> CRep (substPat ss q, substPat ss r)
  | CSeq (c, d) -> CSeq (substCom ss c, substCom ss d)
  | CCond (e, thenbranch, elsebranch, f) ->
     CCond (substExp ss e, substThenBranch ss thenbranch, substElseBranch ss elsebranch, substExp ss f)
  | CLoop (e, dobranch, loopbranch, f) ->
     CLoop (substExp ss e, substDoBranch ss dobranch, substLoopBranch ss loopbranch, substExp ss f)
  | CShow e -> CShow (substExp ss e)
  (* Extensions *)
  | CLocal (x, c) -> CLocal (substRIdent ss x, substCom ss c)
  | CAutoFi (e, t, el) -> CAutoFi (substExp ss e, substThenBranch ss t, substElseBranch ss el)
  | CArrAss (x, i, e) -> CArrAss (substRIdent ss x, substExp ss i, substExp ss e)
  | (CCase _ | CSkip | CAssert _ | CSwap _ | CLocalD _ | CFor _ | CPush _ | CPop _) as c -> substCom ss (Desugar.desugar_com c)

and substThenBranch ss = function
    BThen com -> BThen (substCom ss com)
  | BThenNone -> BThenNone

and substElseBranch ss = function
    BElse com -> BElse (substCom ss com)
  | BElseNone -> BElseNone

and substDoBranch s = function
    BDo c   -> BDo (substCom s c)
  | BDoNone -> BDoNone

and substLoopBranch s = function
    BLoop c   -> BLoop (substCom s c)
  | BLoopNone -> BLoopNone

(* Collect every variable identifier occurring in a command (with duplicates).
   Used by macro expansion to alpha-rename a macro's internal local variables
   (those that are not formal parameters). *)
let rec varsExp = function
    ECons (e, f) -> varsExp e @ varsExp f
  | EHd e -> varsExp e
  | ETl e -> varsExp e
  | EEq (e, f) -> varsExp e @ varsExp f
  | EPair e -> varsExp e
  | EVar (Var x) -> [x]
  | EVal _ -> []
  | EList es -> concat (map varsExp es)
  | EArrGet (Var x, i) -> x :: varsExp i

and varsPat = function
    PCons (q, r) -> varsPat q @ varsPat r
  | PVar (Var x) -> [x]
  | PVal _ -> []
  | PList ps -> concat (map varsPat ps)

and varsCom = function
    CMac (_, xs) -> xs
  | CAss (x, e) -> x :: varsExp e
  | CRep (q, r) -> varsPat q @ varsPat r
  | CSeq (c, d) -> varsCom c @ varsCom d
  | CCond (e, thenbranch, elsebranch, f) ->
     varsExp e @ varsThenBranch thenbranch @ varsElseBranch elsebranch @ varsExp f
  | CLoop (e, dobranch, loopbranch, f) ->
     varsExp e @ varsDoBranch dobranch @ varsLoopBranch loopbranch @ varsExp f
  | CShow e -> varsExp e
  | CLocal (x, c) -> x :: varsCom c
  | CAutoFi (e, t, el) -> varsExp e @ varsThenBranch t @ varsElseBranch el
  | CArrAss (x, i, e) -> x :: varsExp i @ varsExp e
  | (CCase _ | CSkip | CAssert _ | CSwap _ | CLocalD _ | CFor _ | CPush _ | CPop _) as c -> varsCom (Desugar.desugar_com c)

and varsThenBranch = function BThen c -> varsCom c | BThenNone -> []
and varsElseBranch = function BElse c -> varsCom c | BElseNone -> []
and varsDoBranch = function BDo c -> varsCom c | BDoNone -> []
and varsLoopBranch = function BLoop c -> varsCom c | BLoopNone -> []

let substMacro s (Mac (x, xs, c)) = Mac (x, map (substRIdent s) xs, substCom s c)

let substProgram s (Prog (macros, x, c, y)) =
  Prog (map (substMacro s) macros, substRIdent s x, substCom s c, substRIdent s y)
