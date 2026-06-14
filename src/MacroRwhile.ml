(* Macro Expansion *)

open PrintRwhile
open AbsRwhile
open InvRwhile
open List

(* Hygienic macro expansion (opt-in, -hygienic-macros).  When enabled, each
   macro expansion alpha-renames the body's internal locals (every variable that
   is not a formal parameter) to a globally fresh "<name>-<n>" identifier (still
   a valid RIdent token), so repeated or nested macro calls cannot capture each
   other's locals.
   NOTE: this is genuine per-call-site alpha-conversion, so it INTENTIONALLY
   breaks programs that rely on local-name capture to communicate between a macro
   and its callee or its inverse (e.g. AUX/LOOKUP sharing a local Y in
   spec.rwhile, ri.rwhile).  Such programs must keep this flag OFF.  Default is
   OFF, preserving the historical non-hygienic semantics. *)
let hygienic = ref false
let fresh_counter = ref 0

(* Build the substitution for one macro expansion: formal parameters map to the
   actual arguments, and (when hygienic) internal locals are alpha-renamed.
   [combine] is evaluated first so an argument-count mismatch is still reported
   via the Invalid_argument handler.  The two sets are disjoint (locals exclude
   the formals xs'). *)
let expansionSubst (xs' : rIdent list) (xs : rIdent list) (body : com)
    : Subst.subst =
  let formalActual = combine xs' xs in
  if not !hygienic then formalActual
  else
    let locals =
      sort_uniq Stdlib.compare
        (filter (fun v -> not (mem v xs')) (Subst.varsCom body)) in
    let localSubst =
      map (fun (RIdent s) ->
          incr fresh_counter;
          (RIdent s, RIdent (s ^ "-" ^ string_of_int !fresh_counter)))
        locals in
    formalActual @ localSubst

let rec expMacCom (ms : macro list) = function
    CMac (m, xs) -> let rec expandMacro = function
                      | [] -> failwith ("Macro " ^ printTree prtRIdent m ^ " not found")
                      | Mac (m',xs',c) :: ns ->
                         (try if invMacroName m' = m
                              then let body = invCom c in
                                   expMacCom ms (Subst.substCom (expansionSubst xs' xs body) body)
                              else if m = m'
                              then expMacCom ms (Subst.substCom (expansionSubst xs' xs c) c)
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
