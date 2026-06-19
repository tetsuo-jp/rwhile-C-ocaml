open AbsRwhile
open String

(* 「INV-マクロ名」と「マクロ名」は逆命令になる。
 * invMacroName は、「マクロ名」を「INV-マクロ名」に、「INV-マクロ名」を「マクロ名」に書き換える。 *)
let invMacroName (RIdent str) : rIdent = 
  RIdent (if length str >= 5 && sub str 0 4 = "INV-"
	  then sub str 4 (length str - 4)
	  else "INV-" ^ str)

let rec invCom = function
    CMac (x, idents) -> CMac (invMacroName x, idents)
  | CAss (x, e) -> CAss (x, e)
  | CRep (p1, p2) -> CRep (p2, p1)
  | CSeq (c, d) -> CSeq (invCom d, invCom c)
  | CCond (e, thenbranch, elsebranch, f) ->
     CCond (f, invThenBranch thenbranch, invElseBranch elsebranch, e)
  | CLoop (e, dobranch, loopbranch, f) ->
     CLoop (f, invDoBranch dobranch, invLoopBranch loopbranch, e)
  | CShow e -> CShow e
  (* Extensions *)
  | CLocal (x, c) -> CLocal (x, invCom c)        (* local scope is symmetric *)
  | CAutoFi (e, t, el) -> CAutoFi (e, invThenBranch t, invElseBranch el)
  | CArrAss (x, i, e) -> CArrAss (x, i, e)       (* array update is self-inverse *)
  | CCase _ as c -> invCom (Desugar.desugar_com c)  (* normally desugared in invProgram *)

and invThenBranch = function
    BThen c   -> BThen (invCom c)
  | BThenNone -> BThenNone

and invElseBranch = function
    BElse c   -> BElse (invCom c)
  | BElseNone -> BElseNone

and invDoBranch = function
    BDo c   -> BDo (invCom c)
  | BDoNone -> BDoNone

and invLoopBranch = function
    BLoop c   -> BLoop (invCom c)
  | BLoopNone -> BLoopNone

let invProgram prog =
  let (Prog (macros, x, c, y)) = Desugar.desugar_program prog in
  Prog (macros, y, invCom c, x)
