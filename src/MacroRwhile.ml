(* Macro Expansion *)

open PrintRwhile
open AbsRwhile
open InvRwhile
open List

let rec expMacCom (ms : macro list) = function
    CMac (m, xs) -> let rec expandMacro = function
                      | [] -> failwith ("Macro " ^ printTree prtRIdent m ^ " not found")
                      | Mac (m',xs',c) :: ns ->
                         (try if invMacroName m' = m
                              then expMacCom ms (Subst.substCom (combine xs' xs) (invCom c))
                              else if m = m'
                              then expMacCom ms (Subst.substCom (combine xs' xs) c)
                              else expandMacro ns
                          with Invalid_argument _ ->
                            failwith ("Macro " ^ printTree prtRIdent m ^ " expects " ^ string_of_int (length xs') ^ " argument(s) but got " ^ string_of_int (length xs)))
                    in expandMacro ms
  | CAss _ as e -> e
  | CRep _ as e -> e
  | CSeq (c, d) -> CSeq (expMacCom ms c, expMacCom ms d)
  | CCond (e, thenbranch, elsebranch, f) ->
     CCond (e, expMacThenBranch ms thenbranch, expMacElseBranch ms elsebranch, f)
  | CLoop (e, dobranch, loopbranch, f) ->
     CLoop (e, expMacDoBranch ms dobranch, expMacLoopBranch ms loopbranch, f)
  | CShow e -> CShow e
  (* Extensions *)
  | CLocal (x, c) -> CLocal (x, expMacCom ms c)
  | CAutoFi (e, t, el) -> CAutoFi (e, expMacThenBranch ms t, expMacElseBranch ms el)
  | CArrAss _ as e -> e

and expMacThenBranch ms = function
    BThen c   -> BThen (expMacCom ms c)
  | BThenNone -> BThenNone

and expMacElseBranch ms = function
    BElse c   -> BElse (expMacCom ms c)
  | BElseNone -> BElseNone

and expMacDoBranch ms = function
    BDo c   -> BDo (expMacCom ms c)
  | BDoNone -> BDoNone

and expMacLoopBranch ms = function
    BLoop c   -> BLoop (expMacCom ms c)
  | BLoopNone -> BLoopNone

and expMacProgram (Prog (ms, x, c, y)) = Prog ([], x, expMacCom ms c, y)
