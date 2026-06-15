open AbsRwhile
open List

let atom str = VAtom (Atom str)

let rec conss = function
  | [] -> failwith "error in conss"
  | [v] -> v
  | v :: vs -> VCons (v, conss vs)

let rec repeat s n = if n = 0 then [] else s :: repeat s (n-1)

let doNothing = conss [atom "'ass"; conss [atom "'var"; VNil]; conss [atom "'val"; VNil]]

let transRIdent (RIdent str) : valT =
  match int_of_string_opt str with
  | Some n -> conss (repeat VNil n)
  | None -> failwith "Impossible happened."

let transVariable (Var rident) : valT = conss [atom "'var"; transRIdent rident]

let rec transExp (x : exp) : valT =
  match x with
  | EList es -> transExp (List.fold_right (fun e acc -> ECons (e, acc)) es (EVal VNil))
  | _ ->
  conss (match x with
         | EVar var -> [transVariable var]
         | EVal val' -> [atom "'val"; val']
         | ECons (e1, e2) -> [atom "'cons"; transExp e1; transExp e2]
         | EHd e -> [atom "'hd"; transExp e]
         | ETl e -> [atom "'tl"; transExp e]
         | EEq (e1, e2) -> [atom "'eq"; transExp e1; transExp e2]
         | EPair e -> [atom "'pairp"; transExp e]
         | EList _ -> assert false
         | EArrGet _ -> failwith "EArrGet cannot be translated to data")

and transPat (x : pat) : valT =
  match x with
  | PList ps -> transPat (List.fold_right (fun p acc -> PCons (p, acc)) ps (PVal VNil))
  | _ ->
  conss (match x with
         | PCons (p1, p2) -> [atom "'cons"; transPat p1; transPat p2]
         | PVar var -> [transVariable var]
         | PVal val' -> [atom "'val"; val']
         | PList _ -> assert false)

and transCom (c : com) : valT =
  conss (match c with
         | CSeq (c1, c2) -> [atom "'seq"; transCom c1; transCom c2]
         | CMac (_, _) -> failwith "error in transCom"
         | CAss (x, e) -> [atom "'ass"; conss [atom "'var"; transRIdent x]; transExp e]
         | CRep (p1, p2) -> [atom "'rep"; transPat p1; transPat p2]
         | CCond (e, thenbranch, elsebranch, f) ->
            [atom "'cond"; conss [transExp e; transThenBranch thenbranch; transElseBranch elsebranch; transExp f; VNil]]
         | CLoop (e, dobranch, loopbranch, f) ->
            [atom "'loop"; conss [transExp e; transDoBranch dobranch; transLoopBranch loopbranch; transExp f; VNil]]
         | CShow _ -> failwith "CShow cannot be translated to data"
         | CLocal _ -> failwith "CLocal cannot be translated to data"
         | CAutoFi _ -> failwith "CAutoFi cannot be translated to data"
         | CArrAss _ -> failwith "CArrAss cannot be translated to data")

and transThenBranch = function
    BThen com -> transCom com
  | BThenNone -> doNothing

and transElseBranch = function
    BElse com -> transCom com
  | BElseNone -> doNothing

and transDoBranch = function
    BDo com -> transCom com
  | BDoNone -> doNothing

and transLoopBranch = function
    BLoop com -> transCom com
  | BLoopNone -> doNothing

and transProgram = function
    Prog ([], x, c, y) -> conss [conss [atom "'var"; transRIdent x];
                                 transCom c;
                                 conss [atom "'var"; transRIdent y]]
  | _ -> failwith "Impossible happened."

let program2data (p : program) : valT =
  let p2 = MacroRwhile.expMacProgram p in
  let vs = EvalRwhile.varProgram p2 in
  let rec incseq m n = if m = n then [m] else m :: incseq (m+1) n in
  let ws = map (fun n -> RIdent (string_of_int n)) (incseq 1 (length vs)) in
  let p3 = Subst.substProgram (combine vs ws) p2 in
  transProgram p3
