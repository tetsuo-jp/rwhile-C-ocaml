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
         | CArrAss _ -> failwith "CArrAss cannot be translated to data"
         | CCase _ | CSkip | CAssert _ | CSwap _ | CLocalD _ | CFor _ | CPush _ | CPop _ ->
            failwith "transCom: surface sugar must be desugared first (Desugar.desugar_program)")

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

(* ---- data2program: inverse of transProgram ---------------------------------
 * Decodes a program-as-data value (p2d output / a spec residual) back to an AST,
 * so residuals can be EVALUATED directly (EvalRwhile.evalProgram) without going
 * through the ri.rwhile self-interpreter.  Variable index n (unary nil-count)
 * maps back to RIdent (string_of_int n), matching transRIdent's encoding. *)
let rec d_count = function
  | VNil -> 0
  | VCons (VNil, t) -> 1 + d_count t
  | _ -> failwith "data2program: malformed variable index"
let d_ident v = RIdent (string_of_int (d_count v))

let rec d_exp = function
  | VCons (VAtom (Atom "'var"), i) -> EVar (Var (d_ident i))
  | VCons (VAtom (Atom "'val"), v) -> EVal v
  | VCons (VAtom (Atom "'cons"), VCons (a, b)) -> ECons (d_exp a, d_exp b)
  | VCons (VAtom (Atom "'hd"), e) -> EHd (d_exp e)
  | VCons (VAtom (Atom "'tl"), e) -> ETl (d_exp e)
  | VCons (VAtom (Atom "'eq"), VCons (a, b)) -> EEq (d_exp a, d_exp b)
  | VCons (VAtom (Atom "'pairp"), e) -> EPair (d_exp e)
  | _ -> failwith "data2program: malformed expression"

let rec d_pat = function
  | VCons (VAtom (Atom "'var"), i) -> PVar (Var (d_ident i))
  | VCons (VAtom (Atom "'val"), v) -> PVal v
  | VCons (VAtom (Atom "'cons"), VCons (a, b)) -> PCons (d_pat a, d_pat b)
  | _ -> failwith "data2program: malformed pattern"

let rec d_com = function
  | VCons (VAtom (Atom "'seq"), VCons (a, b)) -> CSeq (d_com a, d_com b)
  | VCons (VAtom (Atom "'ass"), VCons (VCons (VAtom (Atom "'var"), i), e)) ->
     CAss (d_ident i, d_exp e)
  | VCons (VAtom (Atom "'rep"), VCons (p1, p2)) -> CRep (d_pat p1, d_pat p2)
  | VCons (VAtom (Atom "'cond"),
           VCons (e, VCons (t, VCons (d, VCons (f, VNil))))) ->
     CCond (d_exp e, BThen (d_com t), BElse (d_com d), d_exp f)
  | VCons (VAtom (Atom "'loop"),
           VCons (e, VCons (d, VCons (l, VCons (f, VNil))))) ->
     CLoop (d_exp e, BDo (d_com d), BLoop (d_com l), d_exp f)
  | _ -> failwith "data2program: malformed command"

let data2program : valT -> program = function
  | VCons (VCons (VAtom (Atom "'var"), i),
           VCons (c, VCons (VAtom (Atom "'var"), j))) ->
     Prog ([], d_ident i, d_com c, d_ident j)
  | _ -> failwith "data2program: malformed program"

(* ON by default (./ri -first-occurrence-vars turns it off): number the
   variables by static access weight instead of first occurrence.  See
   Optimize.ml pass 1.  A variable's number is a UNARY numeral in the encoding,
   so this halves the encoded program (|spec_av| 817701 -> 399565 nodes) and the
   fp2 compiler with it (812515 -> 386681), and makes the whole test suite run
   3.5x faster (125 s -> 36 s).  It is a pure renaming: the answer never
   changes, and fp1/fp2/fp3 all still hold. *)
let hot_vars : bool ref = ref true

(* Opt-in (./ri -share-slots): give variables with disjoint live ranges the SAME
   store slot, so the self-interpreter's store gets shorter.  See Optimize.ml
   pass 2.  Subsumes -hot-vars (it renumbers too), so it wins if both are set. *)
let share_slots : bool ref = ref false

(* ./ri -p2d -static-vars X,Y : names of the subject's STATIC variables, pushed
   to the end of the numbering so the dynamic ones -- the only ones that survive
   into a residual -- get the short unary indices.  See Optimize.ml pass 3. *)
let static_vars : string list ref = ref []

(* Also settable by environment variable, so the drivers that do not parse
   command lines (test-suite, measure_proj, specsize) can be run both ways:
     RWHILE_HOT_VARS=1 ./measure_proj      RWHILE_SHARE_SLOTS=1 ./measure_proj *)
let () =
  if Sys.getenv_opt "RWHILE_FIRST_OCCURRENCE_VARS" <> None then hot_vars := false;
  if Sys.getenv_opt "RWHILE_SHARE_SLOTS" <> None then share_slots := true;
  (match Sys.getenv_opt "RWHILE_STATIC_VARS" with
   | Some s when s <> "" -> static_vars := String.split_on_char ',' s
   | _ -> ())

let program2data (p : program) : valT =
  let p2 = MacroRwhile.expMacProgram p in
  let statics = map (fun s -> RIdent s) !static_vars in
  let sub =
    if !share_slots then
      (* pass 2 allocates slots; pass 3 then pushes the slots whose variables are
         all static to the end.  (These were not composed at first -- static_vars
         was simply ignored when share_slots was on.) *)
      Optimize.slot_alloc_static_last statics p2
    else
      let vs0 = if !hot_vars then Optimize.var_order p2 else EvalRwhile.varProgram p2 in
      let vs = match statics with
        | [] -> vs0
        | ss -> Optimize.order_static_last ss vs0 in
      let rec incseq m n = if m = n then [m] else m :: incseq (m+1) n in
      let ws = map (fun n -> RIdent (string_of_int n)) (incseq 1 (length vs)) in
      combine vs ws in
  let p3 = Subst.substProgram sub p2 in
  transProgram p3
