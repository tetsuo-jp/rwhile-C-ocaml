module SkelRwhile = struct

(* OCaml module generated by the BNF converter *)

open AbsRwhile

type result = string

let failure x = failwith "Undefined case." (* x discarded *)

let rec transRIdent (x : rIdent) : result = match x with
    RIdent string -> failure x


and transAtom (x : atom) : result = match x with
    Atom string -> failure x


and transProgram (x : program) : result = match x with
    Prog procs -> failure x


and transProc (x : proc) : result = match x with
    Proc (rident0, rident1, com, rident) -> failure x


and transCom (x : com) : result = match x with
    CSeq (com0, com) -> failure x
  | CAsn (rident, exp) -> failure x
  | CRep (pat0, pat) -> failure x
  | CCond (exp0, thenbranch, elsebranch, exp) -> failure x
  | CLoop (exp0, dobranch, loopbranch, exp) -> failure x
  | CShow exp -> failure x


and transThenBranch (x : thenBranch) : result = match x with
    BThen com -> failure x
  | BThenNone  -> failure x


and transElseBranch (x : elseBranch) : result = match x with
    BElse com -> failure x
  | BElseNone  -> failure x


and transDoBranch (x : doBranch) : result = match x with
    BDo com -> failure x
  | BDoNone  -> failure x


and transLoopBranch (x : loopBranch) : result = match x with
    BLoop com -> failure x
  | BLoopNone  -> failure x


and transExp (x : exp) : result = match x with
    ECons (exp0, exp) -> failure x
  | EHd exp -> failure x
  | ETl exp -> failure x
  | EEq (exp0, exp) -> failure x
  | EVar variable -> failure x
  | EVal val' -> failure x


and transPat (x : pat) : result = match x with
    PCons (pat0, pat) -> failure x
  | PVar variable -> failure x
  | PVal val' -> failure x
  | PCall (rident0, rident) -> failure x


and transVal (x : valT) : result = match x with
    VNil  -> failure x
  | VAtom atom -> failure x
  | VCons (val'0, val') -> failure x


and transVariable (x : variable) : result = match x with
    Var rident -> failure x



end