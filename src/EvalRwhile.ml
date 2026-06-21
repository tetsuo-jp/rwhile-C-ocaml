open AbsRwhile
open PrintRwhile
open List

type store = (rIdent * valT) list

let vtrue = VCons (VNil, VNil)
let vfalse = VNil
(* R-WHILE truth convention: nil is false, ANY non-nil value is true.  Test
   expressions in conditionals/loops are not restricted to the boolean (nil.nil)
   — e.g. `if Y fi Y` is the identity for any Y, and the self-interpreter
   ri.rwhile dispatches on the raw test value with `if W ... fi W`.  =? still
   yields exactly vtrue/vfalse. *)
let is_true (v : valT) : bool = v <> VNil

(* execution-step counter: incremented once per command executed by evalCom.
 * A cheap, additive measure of run-time cost (for comparing a specialised
 * residual against the interpreter it was specialised from). *)
let eval_steps = ref 0
let reset_steps () = eval_steps := 0
let get_steps () = !eval_steps

(* Extension feature flags -- set by Main.ml command-line options *)
let enable_local  = ref false
let enable_autofi = ref false
let enable_array  = ref false

(* ===== Error reporting =====
 * When llm_errors is set (via the -llm-errors flag), evaluation errors are
 * emitted as a structured, machine-parseable block that an LLM (or any tool)
 * can read field-by-field.  When it is not set, the ORIGINAL human-readable
 * message is raised unchanged, so existing behaviour and tests are preserved.
 *
 * Structured format:
 *   [RWHILE-ERROR]
 *   category: <stable kind, e.g. reversible-update>
 *   message:  <one-line summary (same string as the plain-mode message)>
 *   expected: <optional>
 *   actual:   <optional>
 *   context:  <optional, e.g. variable / expression / store excerpt>
 *   hint:     <optional, why it likely happened / how to fix>
 *   [/RWHILE-ERROR]
 *)
let llm_errors = ref false

let format_structured ~category ?expected ?actual ?context ?hint msg =
  (* Keep the message field to a single line; any multi-line detail (e.g. a store
   * dump) belongs in context, so the block stays cleanly field-per-line. *)
  let msg_line = match String.index_opt msg '\n' with
    | Some i -> String.sub msg 0 i
    | None -> msg in
  let b = Buffer.create 128 in
  Buffer.add_string b "[RWHILE-ERROR]\n";
  Buffer.add_string b ("category: " ^ category ^ "\n");
  Buffer.add_string b ("message: " ^ msg_line ^ "\n");
  let add k = function Some v -> Buffer.add_string b (k ^ ": " ^ v ^ "\n") | None -> () in
  add "expected" expected;
  add "actual" actual;
  add "context" context;
  add "hint" hint;
  Buffer.add_string b "[/RWHILE-ERROR]";
  Buffer.contents b

(* Raise an evaluation error (always a Failure, so Main.ml's handler catches it).
 * In plain mode the message is exactly [msg]; in LLM mode it is the structured
 * block carrying the extra fields. *)
let eval_error ~category ?expected ?actual ?context ?hint msg =
  if !llm_errors
  then failwith (format_structured ~category ?expected ?actual ?context ?hint msg)
  else failwith msg

(* Format an unexpected (non-Failure) exception for Main.ml's top-level handler. *)
let format_uncaught (msg : string) : string =
  if !llm_errors
  then format_structured ~category:"internal"
         ~hint:"unexpected interpreter exception; if this is reachable from a \
                well-formed program it indicates an interpreter bug"
         msg
  else msg

(* Array helpers for -array extension.
 * Index encoding: 0=nil, 1=(nil.nil), 2=(nil.(nil.nil)), ... (unary cons-chain).
 * arr_get arr idx   -- read element at idx from arr (non-destructive)
 * arr_rupdate arr idx vx -- reversibly XOR element at idx with vx *)
let rec arr_get arr idx =
  match idx with
  | VNil ->
    (match arr with
     | VCons (h, _) -> h
     | VNil -> VNil
     | _ -> eval_error ~category:"array"
              ~actual:(printTree prtValT arr)
              ~hint:"an array must be a cons-chain (a.(b.(...)))"
              "Array structure error in get")
  | VCons (VNil, rest) ->
    (match arr with
     | VCons (_, t) -> arr_get t rest
     | _ -> eval_error ~category:"array"
              ~context:("remaining index depth: " ^ printTree prtValT rest)
              ~hint:"the index reaches past the end of the array"
              "Array index out of bounds")
  | _ -> eval_error ~category:"array"
           ~actual:(printTree prtValT idx)
           ~hint:"array indices are unary cons-chains: 0=nil, 1=(nil.nil), 2=(nil.(nil.nil)), ..."
           ("Invalid array index: " ^ printTree prtValT idx)

let rec arr_rupdate arr idx vx =
  match idx with
  | VNil ->
    (match arr with
     | VCons (h, t) ->
       let h' = if h = VNil then vx
                else if vx = h  then VNil
                else if vx = VNil then h
                else eval_error ~category:"array"
                       ~expected:("current element (" ^ printTree prtValT h ^ ") or nil")
                       ~actual:(printTree prtValT vx)
                       ~hint:"A[I] ^= E is reversible XOR: it clears (assign current) or sets (assign to nil)"
                       "error in array element update"
       in VCons (h', t)
     | _ -> eval_error ~category:"array" ~hint:"the index reaches past the end of the array"
              "Array index out of bounds in update")
  | VCons (VNil, rest) ->
    (match arr with
     | VCons (h, t) -> VCons (h, arr_rupdate t rest vx)
     | _ -> eval_error ~category:"array" ~hint:"the index reaches past the end of the array"
              "Array index out of bounds in update")
  | _ -> eval_error ~category:"array"
           ~actual:(printTree prtValT idx)
           ~hint:"array indices are unary cons-chains: 0=nil, 1=(nil.nil), 2=(nil.(nil.nil)), ..."
           ("Invalid array index: " ^ printTree prtValT idx)

let prtStore (i : int) (e : (rIdent * valT) list) : doc = 
  let rec f = function
    | [] -> concatD []
    | [(x,v)] -> concatD [prtRIdent 0 x; render ":="; prtValT 0 v]
    | (x,v) :: ss -> concatD [prtRIdent 0 x; render ":="; prtValT 0 v; render "," ; f ss]
  in concatD [render "{"; f e; render "}"]

(* リストに要素を追加する。ただし、すでにその要素がリストにある場合は追加しない。 *)
let rec insert x = function 
  | [] -> [x]
  | y :: ys -> y :: if x = y then ys else insert x ys

let merge xs ys = fold_right insert xs ys

(* Reversible update *)
let rec rupdate (x, vx) = function
  | [] -> eval_error ~category:"unbound-variable"
            ~context:("variable=" ^ printTree prtRIdent x)
            ~hint:"the variable is not declared/used in the program, so it has no store slot"
            ("Variable " ^ printTree prtRIdent x ^ " is not found (1)")
  | (y, vy) :: ys -> if x = y
		     then (if vy = VNil
			   then (y, vx)
			   else if vx = vy
			   then (y, VNil)
			   else if vx = VNil
			   then (y, vy)
			   else (if !llm_errors
                                 then eval_error ~category:"reversible-update"
                                        ~context:("variable=" ^ printTree prtRIdent x)
                                        ~expected:("current value (" ^ printTree prtValT vy ^ ") or nil")
                                        ~actual:("assign " ^ printTree prtValT vx)
                                        ~hint:"x ^= e is reversible XOR: it only clears (assign the current value) \
                                               or sets (assign to a nil variable); assigning a different non-nil \
                                               value is irreversible and forbidden"
                                        "error in update"
                                 else (Printf.eprintf "error in update: var=%s cur=%s new=%s\n%!" (printTree prtRIdent x) (printTree prtValT vy) (printTree prtValT vx); failwith "error in update"))) :: ys
		     else (y, vy) :: rupdate (x, vx) ys

(* Irreversible update *)
let rec update (x, vx) = function
  | [] -> eval_error ~category:"unbound-variable"
            ~context:("variable=" ^ printTree prtRIdent x)
            ~hint:"the variable is not declared/used in the program, so it has no store slot"
            ("Variable " ^ printTree prtRIdent x ^ " is not found (2)")
  | (y, vy) :: ys -> if x = y
		     then ((y, vx) :: ys)
		     else (y, vy) :: update (x, vx) ys

let all_cleared (s : store) = for_all (fun (_, v) -> v = VNil) s

(* Size of a value tree: total number of nodes (VNil/VAtom leaves and VCons
 * internal nodes).  Used by the -stats flag and tests to measure residual /
 * garbage sizes for the Futamura-projection demos (see
 * plan_reversible_projections_impl.md Stage A). *)
let rec count_nodes = function
  | VNil -> 1
  | VAtom _ -> 1
  | VCons (a, b) -> 1 + count_nodes a + count_nodes b
  | VList vs -> 1 + List.fold_left (fun acc v -> acc + count_nodes v) 0 vs

(* プログラム中に使用されている変数名を列挙する。 *)
let rec varProgram (Prog (ms, x, c, y)) = insert x (insert y (varCom c))

and varMac (Mac (_,xs,c)) = merge xs (varCom c)

and varCom = function
  | CMac (_, xs) -> merge xs []
  | CAss (x,e) -> insert x (varExp e)
  | CRep (q, r) -> merge (varPat q) (varPat r)
  | CSeq (c, d) -> merge (varCom c) (varCom d)
  | CCond (e, thenBranch, elseBranch, f) ->
     fold_right merge [varExp e; varExp f; varThenBranch thenBranch; varElseBranch elseBranch] []
  | CLoop (e, doBranch, loopBranch, f) ->
     fold_right merge [varExp e; varExp f; varDoBranch doBranch; varLoopBranch loopBranch] []
  | CShow e -> varExp e
  (* Extensions *)
  | CLocal (x, c) -> insert x (varCom c)
  | CAutoFi (e, t, el) -> fold_right merge [varExp e; varThenBranch t; varElseBranch el] []
  | CArrAss (x, i, e) -> insert x (merge (varExp i) (varExp e))
  | CCase _ as c -> varCom (Desugar.desugar_com c)

and varPat : pat -> rIdent list = function
   PCons (q,r) -> merge (varPat q) (varPat r)
 | PVar (Var x) -> [x]
 | PVal _ -> []
 | PList ps -> fold_right merge (map varPat ps) []

and varThenBranch = function
  | BThen com -> varCom com
  | BThenNone -> []

and varElseBranch = function
  | BElse com -> varCom com
  | BElseNone -> []

and varDoBranch = function
  | BDo com -> varCom com
  | BDoNone -> []

and varLoopBranch = function
  | BLoop com -> varCom com
  | BLoopNone -> []

and varExp : exp -> rIdent list = function
  | ECons (e1, e2) -> merge (varExp e1) (varExp e2)
  | EHd e -> varExp e
  | ETl e -> varExp e
  | EEq (e1, e2) -> merge (varExp e1) (varExp e2)
  | EPair e -> varExp e
  | EVar (Var x) -> [x]
  | EVal _ -> []
  | EArrGet (Var x, i) -> insert x (varExp i)
  | EList es -> fold_right merge (map varExp es) []

(* Desugar list notation: [v1; v2; v3] -> VCons(v1, VCons(v2, VCons(v3, VNil))) *)
let rec desugar_val = function
  | VList vs -> List.fold_right (fun v acc -> VCons (desugar_val v, acc)) vs VNil
  | VCons (h, t) -> VCons (desugar_val h, desugar_val t)
  | v -> v

(* Desugar list pattern: [p1; p2; p3] -> PCons(p1, PCons(p2, PCons(p3, PVal VNil))) *)
let rec desugar_pat = function
  | PList [] -> PVal VNil
  | PList (p :: ps) -> PCons (desugar_pat p, desugar_pat (PList ps))
  | PCons (p1, p2) -> PCons (desugar_pat p1, desugar_pat p2)
  | p -> p

(* Linearity check: a variable should appear at most once within a single
 * replacement pattern.  A non-linear pattern such as `cons X X` is not
 * reversible; on the READ side it silently reads the second occurrence as nil
 * (data loss) with no runtime error.  We collect such patterns so the caller
 * can WARN about them — this is reported, not fatal, because some existing
 * programs technically contain them. *)
let linearity_violations (Prog (_, _, c, _)) : (string * pat) list =
  let rec praw = function
    | PCons (q, r) -> praw q @ praw r
    | PVar (Var x) -> [x]
    | PVal _ -> []
    | PList ps -> List.concat (List.map praw ps)
  in
  let acc = ref [] in
  let chk_pat where p =
    let vs = praw p in
    if List.length vs <> List.length (merge vs []) then acc := (where, p) :: !acc
  in
  let rec walk = function
    | CRep (q, r) -> chk_pat "lhs (write)" q; chk_pat "rhs (read)" r
    | CSeq (a, b) -> walk a; walk b
    | CCond (_, t, e, _) -> walkT t; walkE e
    | CLoop (_, d, l, _) -> walkD d; walkL l
    | CLocal (_, c) -> walk c
    | CAutoFi (_, t, e) -> walkT t; walkE e
    | CCase _ as c -> walk (Desugar.desugar_com c)
    | CAss _ | CMac _ | CShow _ | CArrAss _ -> ()
  and walkT = function BThen c -> walk c | BThenNone -> ()
  and walkE = function BElse c -> walk c | BElseNone -> ()
  and walkD = function BDo c -> walk c | BDoNone -> ()
  and walkL = function BLoop c -> walk c | BLoopNone -> ()
  in walk c; List.rev !acc

(* Emit a non-fatal warning (stderr) for each non-linear pattern. *)
let warn_linearity p =
  List.iter (fun (where, pat) ->
    let msg = "Non-linear pattern " ^ printTree prtPat pat
              ^ " (a variable is used more than once; position=" ^ where ^ ")" in
    prerr_endline
      (if !llm_errors
       then format_structured ~category:"non-linear-pattern"
              ~hint:"a variable should appear at most once in a replacement pattern (p <= q); \
                     repeating it is not reversible — on the read side the second occurrence \
                     reads as nil, silently losing data"
              msg
       else "[RWHILE-WARNING] " ^ msg))
    (linearity_violations p)

(* Evaluation *)
let evalVariable s (Var x) =
  try assoc x s
  with Not_found ->
    eval_error ~category:"unbound-variable"
      ~context:("variable=" ^ printTree prtRIdent x)
      ~hint:"the variable is referenced but has no store slot (should not happen for a well-formed program)"
      ("Variable " ^ printTree prtRIdent x ^ " is not found (in store)")

let rec evalExp s = function
    ECons (e1, e2) -> VCons (evalExp s e1, evalExp s e2)
  | EHd e -> (match evalExp s e with
	      | VNil | VAtom _ | VList _ as v ->
                 eval_error ~category:"no-head"
                   ~actual:(printTree prtValT v)
                   ~hint:"hd requires a cons value (a.b); nil, an atom, or a list literal has no head"
                   ("No head. Expression " ^ printTree prtExp (EHd e) ^ " has value " ^ printTree prtValT v)
	      | VCons (v,_) -> v)
  | ETl e -> (match evalExp s e with
	      | VNil | VAtom _ | VList _ as v ->
                 eval_error ~category:"no-tail"
                   ~actual:(printTree prtValT v)
                   ~hint:"tl requires a cons value (a.b); nil, an atom, or a list literal has no tail"
                   ("No tail. Expression " ^ printTree prtExp (ETl e) ^ " has value " ^ printTree prtValT v)
	      | VCons (_,v) -> v)
  | EEq (e1, e2) -> if evalExp s e1 = evalExp s e2 then vtrue else vfalse
  | EPair e -> (match evalExp s e with VCons _ -> vtrue | _ -> vfalse)
  | EVar x -> evalVariable s x
  | EVal v -> desugar_val v
  | EList es -> List.fold_right (fun e acc -> VCons (evalExp s e, acc)) es VNil
  | EArrGet (x, idx_exp) ->
     if not !enable_array
     then eval_error ~category:"disabled-extension"
            ~hint:"pass the -array flag to enable array operations"
            "get A[I] requires the -array flag"
     else arr_get (evalVariable s x) (evalExp s idx_exp)

and evalPat s = function
    PCons (q, r) -> let (s1, d1) = evalPat s q in
		      let (s2, d2) = evalPat s1 r in
		      (s2, VCons (d1, d2))
  | PVar (Var y) -> let v = evalVariable s (Var y) in
		    (update (y,VNil) s, v)
  | PVal val' -> (s, desugar_val val')
  | PList _ as p -> evalPat s (desugar_pat p)

and inv_evalPat s = function
    (PList _ as p, v) -> inv_evalPat s (desugar_pat p, v)
  | (PCons (p1, p2), VCons (v1, v2)) -> let s1 = inv_evalPat s (p1, v1) in
					inv_evalPat s1 (p2, v2)
  | (PVar (Var y) as p, v) -> if evalVariable s (Var y) = VNil
			      then update (y, v) s
			      else eval_error ~category:"pattern-write-conflict"
				     ~actual:("variable " ^ printTree prtRIdent y ^ " = " ^ printTree prtValT (evalVariable s (Var y)))
				     ~context:("pattern=" ^ printTree prtPat p ^ "; term=" ^ printTree prtValT v ^ "; store=" ^ printTree prtStore s)
				     ~hint:"a CRep target variable (p in 'p <= q') must be nil before it is written; it is already bound"
				     ("Pattern write conflict: " ^ printTree prtPat p ^ " is already non-nil (in inv_evalPat.PVar)")
  | (PVal v', v) -> let dv' = desugar_val v' in
		    if v = dv' then s
		    else eval_error ~category:"pattern-mismatch"
			   ~expected:(printTree prtValT dv')
			   ~actual:(printTree prtValT v)
			   ~context:("store=" ^ printTree prtStore s)
			   ~hint:"a literal pattern requires the value to equal the literal exactly"
			   ("Pattern matching failed: " ^ printTree prtValT v ^ " and " ^ printTree prtValT dv' ^ " are not equal (in inv_evalPat)")
  | (PCons _ as p, v) -> eval_error ~category:"pattern-shape-mismatch"
			   ~expected:"a cons value (a.b)"
			   ~actual:(printTree prtValT v)
			   ~context:("pattern=" ^ printTree prtPat p ^ "; store=" ^ printTree prtStore s)
			   ~hint:"a cons pattern (cons p1 p2) requires a cons value; got a non-cons (often nil), so the data shape does not match the pattern"
			   ("Cannot match cons pattern " ^ printTree prtPat p ^ " against non-cons value " ^ printTree prtValT v ^ " (in inv_evalPat.PCons)")

and evalCom (s : store) (c : com) : store =
  incr eval_steps;
  match c with
  | CMac (_, _) -> eval_error ~category:"internal"
                     ~hint:"macros must be expanded before evaluation; evalProgram runs expMacProgram first"
                     "Impossible happened.  Macro must not appear in runtime."
  | CAss (y, e) -> let v' = evalExp s e in
		   rupdate (y, v') s
  | CRep (q, r) -> let (s1, v1) = evalPat s r in
		   inv_evalPat s1 (q, v1)
  | CSeq (c, d) -> let s1 = evalCom s c in
		   evalCom s1 d
  | CCond (e, thenbranch, elsebranch, f) ->
     if is_true (evalExp s e) then
       let s1 = (match thenbranch with
		 | BThen c -> evalCom s c
		 | BThenNone -> s)
       in
       if is_true (evalExp s1 f) then s1
       else eval_error ~category:"assertion-failed"
              ~context:("exit assertion=" ^ printTree prtExp f ^ "; branch=then")
              ~expected:"true (exit assertion must hold after the then-branch)"
              ~actual:(printTree prtValT (evalExp s1 f))
              ~hint:"in 'if e then C else D fi f', f is an assertion: it must be TRUE after the then-branch is taken"
              ("Assertion " ^ printTree prtExp f ^ " is not true.\n")
     else
       let s1 = match elsebranch with
	 | BElse c -> evalCom s c
	 | BElseNone -> s
       in
       if evalExp s1 f = vfalse then s1
       else eval_error ~category:"assertion-failed"
              ~context:("exit assertion=" ^ printTree prtExp f ^ "; branch=else")
              ~expected:"false (exit assertion must not hold after the else-branch)"
              ~actual:(printTree prtValT (evalExp s1 f))
              ~hint:"in 'if e then C else D fi f', f is an assertion: it must be FALSE after the else-branch is taken"
              ("Assertion " ^ printTree prtExp f ^ " is not false.\n")
  | CLoop (e, dobranch, loopbranch, f) ->
     if is_true (evalExp s e) then
       let s1 = match dobranch with
	   BDo c -> evalCom s c
	 | BDoNone -> s
       in
       evalLoop s1 (e, dobranch, loopbranch, f)
     else eval_error ~category:"assertion-failed"
            ~context:("entry test=" ^ printTree prtExp e)
            ~expected:"true (loop entry test must hold on first entry)"
            ~actual:(printTree prtValT (evalExp s e))
            ~hint:"in 'from e do D loop L until f', the entry test e must be TRUE when the loop is first reached"
            ("Assertion " ^ printTree prtExp e ^ " is not true.\n")
  | CShow e -> (print_string (printTree prtExp e ^ " = " ^ printTree prtValT (evalExp s e) ^ "\n"); s)
  (* Extensions *)
  | CLocal (x, c) ->
     if not !enable_local then
       eval_error ~category:"disabled-extension"
         ~hint:"pass the -local flag to enable scoped local variables"
         "local/end requires the -local flag"
     else
       let v = assoc x s in
       if v <> VNil then
         eval_error ~category:"local-not-nil"
           ~context:("variable=" ^ printTree prtRIdent x)
           ~actual:(printTree prtValT v)
           ~expected:"nil at block entry"
           ~hint:"a local variable must be nil when its block is entered"
           ("local variable " ^ printTree prtRIdent x ^
                   " must be nil at block entry, but is " ^ printTree prtValT v)
       else
         let s1 = evalCom s c in
         let v1 = assoc x s1 in
         if v1 <> VNil then
           eval_error ~category:"local-not-nil"
             ~context:("variable=" ^ printTree prtRIdent x)
             ~actual:(printTree prtValT v1)
             ~expected:"nil at block exit"
             ~hint:"a local variable must be cleared back to nil before its block ends"
             ("local variable " ^ printTree prtRIdent x ^
                     " must be nil at block exit (cleanup missing), but is " ^ printTree prtValT v1)
         else s1
  | CAutoFi (e, thenbranch, elsebranch) ->
     if not !enable_autofi then
       eval_error ~category:"disabled-extension"
         ~hint:"pass the -autofi flag to enable the auto-fi conditional (iff)"
         "iff requires the -autofi flag"
     else
       if is_true (evalExp s e) then
         let s1 = match thenbranch with BThen c -> evalCom s c | BThenNone -> s in
         if is_true (evalExp s1 e) then s1
         else eval_error ~category:"assertion-failed"
                ~context:("condition=" ^ printTree prtExp e ^ "; branch=then")
                ~expected:"true (condition must still hold after the then-branch)"
                ~actual:(printTree prtValT (evalExp s1 e))
                ~hint:"iff reuses the condition as its exit assertion; it must be TRUE after the then-branch"
                ("iff auto-fi: condition " ^ printTree prtExp e ^
                        " not true after then-branch.\n")
       else
         let s1 = match elsebranch with BElse c -> evalCom s c | BElseNone -> s in
         if evalExp s1 e = vfalse then s1
         else eval_error ~category:"assertion-failed"
                ~context:("condition=" ^ printTree prtExp e ^ "; branch=else")
                ~expected:"false (condition must remain false after the else-branch)"
                ~actual:(printTree prtValT (evalExp s1 e))
                ~hint:"iff reuses the condition as its exit assertion; it must be FALSE after the else-branch"
                ("iff auto-fi: condition " ^ printTree prtExp e ^
                        " not false after else-branch.\n")
  | CArrAss (x, idx_exp, val_exp) ->
     if not !enable_array then
       eval_error ~category:"disabled-extension"
         ~hint:"pass the -array flag to enable array operations"
         "A[I] ^= E requires the -array flag"
     else
       let arr = assoc x s in
       let idx = evalExp s idx_exp in
       let v   = evalExp s val_exp in
       update (x, arr_rupdate arr idx v) s
  | CCase _ as c -> evalCom s (Desugar.desugar_com c)  (* normally desugared in evalProgram *)

and evalLoop (s : store) (e, dobranch, loopbranch, f) : store =
  if is_true (evalExp s f)
  then s
  else
    let s1 = (match loopbranch with
	 	BLoop c   -> evalCom s c
	      | BLoopNone -> s)
    in
    (* Reversibility invariant: the entry test e must be re-established FALSE
     * after each loop body L.  This used to be an OCaml `assert`, which gave no
     * diagnostic and was silently removed under -noassert; make it explicit. *)
    (if evalExp s1 e <> VNil then
       eval_error ~category:"assertion-failed"
         ~context:("entry test=" ^ printTree prtExp e)
         ~expected:"false (entry test must be false after each loop body)"
         ~actual:(printTree prtValT (evalExp s1 e))
         ~hint:"in 'from e do D loop L until f', the entry test e must be FALSE after each 'loop' body L runs; \
                otherwise the loop is not reversible"
         ("Loop reversibility assertion: " ^ printTree prtExp e ^ " is not false after the loop body.\n"));
    let s2 = (match dobranch with
		BDo c   -> evalCom s1 c
	      | BDoNone -> s1)
    in
    evalLoop s2 (e, dobranch, loopbranch, f)

and evalProgram (p : program) (v : valT): valT =
  let Prog (ms, x, c, y) as p' = MacroRwhile.expMacProgram p in
  ignore ms;
  warn_linearity p';
  let s = map (fun x -> (x, VNil)) (varProgram p') in
  (* Desugar the input value: list-notation literals like ['a,'b,'c] must become
   * cons-chains, exactly like ['a,'b,'c] written inside the program would. *)
  let s1 = rupdate (x, desugar_val v) s in
  let s2 = evalCom s1 c in
  let res = evalVariable s2 (Var y) in
  let s3 = rupdate (y, res) s2 in
  if all_cleared s3 then res
  else
    (* Report the actual offending (post-cleanup) store s3, and list only the
     * variables that are still non-nil. *)
    let dirty = filter (fun (_, vv) -> vv <> VNil) s3 in
    eval_error ~category:"store-not-cleared"
      ~context:("non-nil variables: " ^ printTree prtStore dirty)
      ~expected:"all variables nil at program end (reversibility condition)"
      ~hint:"every variable except the output must be cleared back to nil before 'write'; \
             a variable left non-nil means some assignment or replacement was not undone"
      ("Some variables are not nil.\n" ^ printTree prtStore s3)
