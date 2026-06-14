open AbsRwhile

(* ===== Helper functions ===== *)

let parse_program (s : string) : program =
  ParRwhile.pProgram LexRwhile.token (Lexing.from_string s)

let parse_val (s : string) : valT =
  ParRwhile.pValT LexRwhile.token (Lexing.from_string s)

let show_val (v : valT) : string =
  PrintRwhile.printTree PrintRwhile.prtValT v

let show_program (p : program) : string =
  PrintRwhile.printTree PrintRwhile.prtProgram p

let read_file filename =
  let ch = open_in filename in
  let len = in_channel_length ch in
  let s = really_input_string ch len in
  close_in ch;
  s

let find_substring s sub =
  let n = String.length s
  and m = String.length sub in
  let rec loop i =
    if i + m > n then None
    else if String.sub s i m = sub then Some i
    else loop (i + 1)
  in
  loop 0

let macro_prefix filename =
  let src = read_file filename in
  match find_substring src "(* ===== Main program ===== *)" with
  | Some i -> String.sub src 0 i
  | None -> failwith ("main marker not found in " ^ filename)

let parse_macro_harness filename body =
  parse_program ((macro_prefix filename) ^ "\n" ^ body)

let eval_string prog_str val_str =
  let prog = parse_program prog_str in
  let data = parse_val val_str in
  EvalRwhile.evalProgram prog data

let vtrue = VCons (VNil, VNil)
let vfalse = VNil
let atom s = VAtom (Atom s)
let pair a b = VCons (a, b)
let idx0 = VNil
let idx1 = VCons (VNil, VNil)
let idx2 = VCons (VNil, idx1)
let static_entry v = VCons (vtrue, v)
let dynamic_entry v = VCons (VNil, v)

(* Alcotest testables *)
let valT_testable =
  Alcotest.testable (fun fmt v -> Format.pp_print_string fmt (show_val v)) (=)

let program_testable =
  Alcotest.testable (fun fmt p -> Format.pp_print_string fmt (show_program p)) (=)

(* ===== Store operations tests ===== *)

let test_insert_empty () =
  let id = RIdent "X" in
  Alcotest.(check (list (pair (of_pp (fun fmt (RIdent s) -> Format.pp_print_string fmt s)) valT_testable)))
    "insert into empty"
    [(id, VNil)]
    (EvalRwhile.insert (id, VNil) [])

let test_insert_existing () =
  let x = RIdent "X" in
  let store = [(x, VNil); (RIdent "Y", VNil)] in
  let result = EvalRwhile.insert (x, VNil) store in
  Alcotest.(check int) "same length" 2 (List.length result)

let test_rupdate_nil_to_val () =
  let x = RIdent "X" in
  let store = [(x, VNil)] in
  let result = EvalRwhile.rupdate (x, vtrue) store in
  Alcotest.(check valT_testable) "rupdate nil->val" vtrue (List.assoc x result)

let test_rupdate_val_to_same () =
  let x = RIdent "X" in
  let store = [(x, vtrue)] in
  let result = EvalRwhile.rupdate (x, vtrue) store in
  Alcotest.(check valT_testable) "rupdate val->nil" VNil (List.assoc x result)

let test_rupdate_val_to_nil () =
  let x = RIdent "X" in
  let v = VCons (VNil, VCons (VNil, VNil)) in
  let store = [(x, v)] in
  let result = EvalRwhile.rupdate (x, VNil) store in
  Alcotest.(check valT_testable) "rupdate keeps val" v (List.assoc x result)

let test_rupdate_different_fails () =
  let x = RIdent "X" in
  let store = [(x, VCons (VNil, VNil))] in
  Alcotest.check_raises "rupdate different values fails"
    (Failure "error in update")
    (fun () -> ignore (EvalRwhile.rupdate (x, VCons (VNil, VCons (VNil, VNil))) store))

let test_rupdate_not_found () =
  let x = RIdent "X" in
  Alcotest.check_raises "rupdate not found"
    (Failure ("Variable X is not found (1)"))
    (fun () -> ignore (EvalRwhile.rupdate (x, VNil) []))

let test_update_replace () =
  let x = RIdent "X" in
  let store = [(x, VNil)] in
  let result = EvalRwhile.update (x, vtrue) store in
  Alcotest.(check valT_testable) "update replaces" vtrue (List.assoc x result)

let test_all_cleared_true () =
  let store = [(RIdent "X", VNil); (RIdent "Y", VNil)] in
  Alcotest.(check bool) "all cleared" true (EvalRwhile.all_cleared store)

let test_all_cleared_false () =
  let store = [(RIdent "X", VNil); (RIdent "Y", vtrue)] in
  Alcotest.(check bool) "not all cleared" false (EvalRwhile.all_cleared store)

(* ===== Expression evaluation tests ===== *)

let test_eval_val () =
  let store = [] in
  let result = EvalRwhile.evalExp store (EVal VNil) in
  Alcotest.(check valT_testable) "eval nil literal" VNil result

let test_eval_var () =
  let x = RIdent "X" in
  let store = [(x, vtrue)] in
  let result = EvalRwhile.evalExp store (EVar (Var x)) in
  Alcotest.(check valT_testable) "eval var" vtrue result

let test_eval_cons () =
  let store = [] in
  let result = EvalRwhile.evalExp store (ECons (EVal VNil, EVal (VAtom (Atom "'a")))) in
  Alcotest.(check valT_testable) "eval cons" (VCons (VNil, VAtom (Atom "'a"))) result

let test_eval_hd () =
  let x = RIdent "X" in
  let v = VCons (VAtom (Atom "'a"), VNil) in
  let store = [(x, v)] in
  let result = EvalRwhile.evalExp store (EHd (EVar (Var x))) in
  Alcotest.(check valT_testable) "eval hd" (VAtom (Atom "'a")) result

let test_eval_tl () =
  let x = RIdent "X" in
  let v = VCons (VAtom (Atom "'a"), VAtom (Atom "'b")) in
  let store = [(x, v)] in
  let result = EvalRwhile.evalExp store (ETl (EVar (Var x))) in
  Alcotest.(check valT_testable) "eval tl" (VAtom (Atom "'b")) result

let test_eval_hd_nil_fails () =
  let store = [] in
  Alcotest.check_raises "hd nil fails"
    (Failure "No head. Expression hd nil has value nil")
    (fun () -> ignore (EvalRwhile.evalExp store (EHd (EVal VNil))))

let test_eval_tl_nil_fails () =
  let store = [] in
  Alcotest.check_raises "tl nil fails"
    (Failure "No tail. Expression tl nil has value nil")
    (fun () -> ignore (EvalRwhile.evalExp store (ETl (EVal VNil))))

let test_eval_eq_true () =
  let store = [] in
  let result = EvalRwhile.evalExp store (EEq (EVal VNil, EVal VNil)) in
  Alcotest.(check valT_testable) "=? nil nil = true" vtrue result

let test_eval_eq_false () =
  let store = [] in
  let result = EvalRwhile.evalExp store (EEq (EVal VNil, EVal (VAtom (Atom "'a")))) in
  Alcotest.(check valT_testable) "=? nil 'a = false" vfalse result

(* ===== Variable collection tests ===== *)

let test_var_program () =
  let prog = parse_program "read X; X ^= nil; write Y" in
  let vars = EvalRwhile.varProgram prog in
  Alcotest.(check bool) "X in vars" true (List.mem (RIdent "X") vars);
  Alcotest.(check bool) "Y in vars" true (List.mem (RIdent "Y") vars)

let test_var_loop () =
  let prog = parse_program "read Y; from =? X nil loop cons Z Y <= Y; X <= cons Z X until =? Y nil; write X" in
  let vars = EvalRwhile.varProgram prog in
  Alcotest.(check bool) "X in vars" true (List.mem (RIdent "X") vars);
  Alcotest.(check bool) "Y in vars" true (List.mem (RIdent "Y") vars);
  Alcotest.(check bool) "Z in vars" true (List.mem (RIdent "Z") vars)

(* ===== Inversion tests ===== *)

let test_inv_macro_name () =
  Alcotest.(check string) "INV- prefix"
    "INV-FOO"
    (let (RIdent s) = InvRwhile.invMacroName (RIdent "FOO") in s);
  Alcotest.(check string) "remove INV- prefix"
    "FOO"
    (let (RIdent s) = InvRwhile.invMacroName (RIdent "INV-FOO") in s)

let test_inv_ass () =
  let c = CAss (RIdent "X", EVal VNil) in
  let c' = InvRwhile.invCom c in
  Alcotest.(check bool) "inv of assignment is itself" true (c = c')

let test_inv_rep () =
  let p = PVar (Var (RIdent "X")) in
  let q = PVar (Var (RIdent "Y")) in
  let c = CRep (p, q) in
  let expected = CRep (q, p) in
  Alcotest.(check bool) "inv of replacement swaps" true (InvRwhile.invCom c = expected)

let test_inv_seq () =
  let c1 = CAss (RIdent "X", EVal VNil) in
  let c2 = CAss (RIdent "Y", EVal VNil) in
  let c = CSeq (c1, c2) in
  match InvRwhile.invCom c with
  | CSeq (a, b) ->
    Alcotest.(check bool) "inv seq reverses order" true (a = InvRwhile.invCom c2 && b = InvRwhile.invCom c1)
  | _ -> Alcotest.fail "inv of seq should be seq"

let test_inv_cond () =
  let e = EVal VNil in
  let f = EVar (Var (RIdent "X")) in
  let c = CCond (e, BThenNone, BElseNone, f) in
  match InvRwhile.invCom c with
  | CCond (e', _, _, f') ->
    Alcotest.(check bool) "inv cond swaps test/assert" true (e' = f && f' = e)
  | _ -> Alcotest.fail "inv of cond should be cond"

let test_inv_loop () =
  let e = EVal VNil in
  let f = EVar (Var (RIdent "X")) in
  let c = CLoop (e, BDoNone, BLoopNone, f) in
  match InvRwhile.invCom c with
  | CLoop (e', _, _, f') ->
    Alcotest.(check bool) "inv loop swaps from/until" true (e' = f && f' = e)
  | _ -> Alcotest.fail "inv of loop should be loop"

let test_inv_program () =
  let prog = parse_program "read X; X ^= nil; write Y" in
  let inv = InvRwhile.invProgram prog in
  match inv with
  | Prog (_, x, _, y) ->
    Alcotest.(check string) "inv reads Y" "Y" (let (RIdent s) = x in s);
    Alcotest.(check string) "inv writes X" "X" (let (RIdent s) = y in s)

let test_inv_involution () =
  let prog = parse_program "read Y; from =? X nil loop cons Z Y <= Y; X <= cons Z X until =? Y nil; write X" in
  let inv2 = InvRwhile.invProgram (InvRwhile.invProgram prog) in
  Alcotest.(check program_testable) "inv(inv(p)) = p" prog inv2

(* ===== Substitution tests ===== *)

let test_subst_rident () =
  let ss = [(RIdent "X", RIdent "Y")] in
  let result = Subst.substRIdent ss (RIdent "X") in
  Alcotest.(check string) "subst X -> Y" "Y" (let (RIdent s) = result in s)

let test_subst_rident_unchanged () =
  let ss = [(RIdent "X", RIdent "Y")] in
  let result = Subst.substRIdent ss (RIdent "Z") in
  Alcotest.(check string) "subst Z unchanged" "Z" (let (RIdent s) = result in s)

let test_subst_exp () =
  let ss = [(RIdent "X", RIdent "Y")] in
  let e = EVar (Var (RIdent "X")) in
  let result = Subst.substExp ss e in
  Alcotest.(check bool) "subst in exp" true (result = EVar (Var (RIdent "Y")))

let test_subst_com () =
  let ss = [(RIdent "X", RIdent "Y")] in
  let c = CAss (RIdent "X", EVar (Var (RIdent "X"))) in
  let result = Subst.substCom ss c in
  let expected = CAss (RIdent "Y", EVar (Var (RIdent "Y"))) in
  Alcotest.(check bool) "subst in com" true (result = expected)

let test_subst_program () =
  let ss = [(RIdent "X", RIdent "A"); (RIdent "Y", RIdent "B")] in
  let prog = parse_program "read X; X ^= nil; write Y" in
  let result = Subst.substProgram ss prog in
  match result with
  | Prog (_, x, _, y) ->
    Alcotest.(check string) "subst read var" "A" (let (RIdent s) = x in s);
    Alcotest.(check string) "subst write var" "B" (let (RIdent s) = y in s)

(* ===== Macro expansion tests ===== *)

let test_macro_expand_simple () =
  let prog_str = "macro M(X) X ^= nil read Y; M(Y); write Y" in
  let prog = parse_program prog_str in
  let expanded = MacroRwhile.expMacProgram prog in
  match expanded with
  | Prog (ms, _, _, _) ->
    Alcotest.(check int) "macros removed" 0 (List.length ms)

let test_macro_expand_inv () =
  let prog_str = "macro M(X) X ^= nil read Y; INV-M(Y); write Y" in
  let prog = parse_program prog_str in
  let expanded = MacroRwhile.expMacProgram prog in
  match expanded with
  | Prog (ms, _, c, _) ->
    Alcotest.(check int) "macros removed" 0 (List.length ms);
    Alcotest.(check bool) "body is assignment" true
      (match c with CAss _ -> true | _ -> false)

let test_macro_not_found () =
  let prog_str = "read Y; NONEXISTENT(Y); write Y" in
  let prog = parse_program prog_str in
  Alcotest.check_raises "macro not found"
    (Failure "Macro NONEXISTENT not found")
    (fun () -> ignore (MacroRwhile.expMacProgram prog))

let test_macro_arity_mismatch () =
  let prog_str = "macro M(X, Y) X ^= nil read Z; M(Z); write Z" in
  let prog = parse_program prog_str in
  Alcotest.check_raises "arity mismatch"
    (Failure "Macro M expects 2 argument(s) but got 1")
    (fun () -> ignore (MacroRwhile.expMacProgram prog))

(* ===== Program-to-data translation tests ===== *)

let test_p2d_simple () =
  let prog = parse_program "read X; X ^= nil; write Y" in
  let data = Program2DataRwhile.program2data prog in
  Alcotest.(check bool) "p2d produces non-nil" true (data <> VNil)

let test_p2d_conss () =
  let result = Program2DataRwhile.conss [VNil] in
  Alcotest.(check valT_testable) "conss singleton" VNil result

let test_p2d_conss_pair () =
  let result = Program2DataRwhile.conss [VNil; VAtom (Atom "'a")] in
  Alcotest.(check valT_testable) "conss pair" (VCons (VNil, VAtom (Atom "'a"))) result

let test_p2d_conss_triple () =
  let result = Program2DataRwhile.conss [VNil; VNil; VNil] in
  let expected = VCons (VNil, VCons (VNil, VNil)) in
  Alcotest.(check valT_testable) "conss triple" expected result

(* ===== Integration tests: parse -> eval ===== *)

let test_eval_identity () =
  let result = eval_string "read Y; X ^= nil; write Y" "('a.'b)" in
  Alcotest.(check valT_testable) "identity" (VCons (VAtom (Atom "'a"), VAtom (Atom "'b"))) result

let test_eval_rep () =
  let result = eval_string "read Y; X <= Y; write X" "('1.('2.('3.nil)))" in
  let expected = parse_val "('1.('2.('3.nil)))" in
  Alcotest.(check valT_testable) "rep copies" expected result

let test_eval_swap () =
  let result = eval_string
    "read X; cons Y Z <= X; X <= cons Z Y; write X"
    "('a.'b)" in
  Alcotest.(check valT_testable) "swap" (VCons (VAtom (Atom "'b"), VAtom (Atom "'a"))) result

let test_eval_reverse () =
  let prog = "read Y; from =? X nil loop cons Z Y <= Y; X <= cons Z X until =? Y nil; write X" in
  let result = eval_string prog "('1.('2.('3.nil)))" in
  let expected = parse_val "('3.('2.('1.nil)))" in
  Alcotest.(check valT_testable) "reverse list" expected result

let test_eval_if_true () =
  let prog = "read Y; if Y then X ^= nil else X ^= nil fi Y; write Y" in
  let result = eval_string prog "(nil.nil)" in
  Alcotest.(check valT_testable) "if true branch" vtrue result

let test_eval_if_false () =
  let prog = "read Y; if Y then X ^= nil else X ^= nil fi Y; write Y" in
  let result = eval_string prog "nil" in
  Alcotest.(check valT_testable) "if false branch" VNil result

let test_eval_show () =
  let result = eval_string "read Y; show Y; write Y" "'a" in
  Alcotest.(check valT_testable) "show passes through" (VAtom (Atom "'a")) result

let test_eval_cons_exp () =
  (* Use replacement to move X into a cons pair, preserving reversibility *)
  let result = eval_string "read X; cons Y nil <= cons X nil; Y ^= cons Y Y; write Y" "nil" in
  let expected = VCons (VNil, VNil) in
  Alcotest.(check valT_testable) "cons expression" expected result

let test_eval_eq_check () =
  let result = eval_string "read X; Y ^= =? X nil; write Y" "nil" in
  Alcotest.(check valT_testable) "=? nil nil" vtrue result

let test_eval_eq_check_false () =
  (* Test =? with unequal values: =? 'a nil = nil (false) *)
  (* Use evalExp directly instead of full program to avoid cleanup constraints *)
  let store = [(RIdent "X", VAtom (Atom "'a"))] in
  let result = EvalRwhile.evalExp store (EEq (EVar (Var (RIdent "X")), EVal VNil)) in
  Alcotest.(check valT_testable) "=? 'a nil" vfalse result

let test_eval_macro_minus () =
  let prog = {|
    macro MINUS(X,Y)
      from  =? Y' nil
      loop  cons nil X <= X;
            cons nil Y <= Y;
            Y' <= cons nil Y'
      until =? Y nil;
      Y <= Y'

    read Z;
      cons X Y <= Z;
      MINUS(X,Y);
      Z <= cons X Y;
    write Z
  |} in
  let result = eval_string prog "((nil.(nil.(nil.(nil.nil)))).(nil.(nil.(nil.nil))))" in
  let expected = parse_val "((nil.nil).(nil.(nil.(nil.nil))))" in
  Alcotest.(check valT_testable) "minus 4-3=1" expected result

let test_eval_reversibility () =
  let prog = "read Y; from =? X nil loop cons Z Y <= Y; X <= cons Z X until =? Y nil; write X" in
  let inv_prog = "read X; from =? Y nil loop cons Z X <= X; Y <= cons Z Y until =? X nil; write Y" in
  let input = "('a.('b.('c.nil)))" in
  let reversed = eval_string prog input in
  let restored = eval_string inv_prog (show_val reversed) in
  let expected = parse_val input in
  Alcotest.(check valT_testable) "reverse then unreverse" expected restored

let test_eval_non_cleared_fails () =
  (* When a variable is not cleared, evalProgram raises Failure *)
  let raised = ref false in
  (try ignore (eval_string "read X; Y ^= cons nil nil; write X" "nil")
   with Failure msg ->
     raised := true;
     Alcotest.(check bool) "error mentions variables"
       true (String.length msg > 0));
  Alcotest.(check bool) "exception raised" true !raised

(* ===== Inverse evaluation integration test ===== *)

let test_inv_eval_swap () =
  let prog = parse_program "read X; cons Y Z <= X; X <= cons Z Y; write X" in
  let inv = InvRwhile.invProgram prog in
  let result = EvalRwhile.evalProgram inv (VCons (VAtom (Atom "'b"), VAtom (Atom "'a"))) in
  Alcotest.(check valT_testable) "inv swap" (VCons (VAtom (Atom "'a"), VAtom (Atom "'b"))) result

let test_inv_eval_reverse () =
  let prog = parse_program
    "read Y; from =? X nil loop cons Z Y <= Y; X <= cons Z X until =? Y nil; write X" in
  let inv = InvRwhile.invProgram prog in
  let input = parse_val "('3.('2.('1.nil)))" in
  let result = EvalRwhile.evalProgram inv input in
  let expected = parse_val "('1.('2.('3.nil)))" in
  Alcotest.(check valT_testable) "inv reverse" expected result

(* ===== Parse/Print roundtrip tests ===== *)

let test_parse_print_roundtrip_val () =
  let inputs = ["nil"; "'a"; "(nil . nil)"; "('a . ('b . nil))"] in
  List.iter (fun s ->
    let v = parse_val s in
    let s' = show_val v in
    let v' = parse_val s' in
    Alcotest.(check valT_testable) ("roundtrip val: " ^ s) v v'
  ) inputs

let test_parse_print_roundtrip_prog () =
  let inputs = [
    "read X; X ^= nil; write Y";
    "read Y; X <= Y; write X";
    "read X; cons Y Z <= X; X <= cons Z Y; write X";
  ] in
  List.iter (fun s ->
    let p = parse_program s in
    let s' = show_program p in
    let p' = parse_program s' in
    Alcotest.(check program_testable) ("roundtrip prog: " ^ s) p p'
  ) inputs

(* ===== Program-to-data file integration tests ===== *)

let parse_file_program filename =
  let ch = open_in filename in
  let prog = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel ch) in
  close_in ch;
  prog

let parse_file_val filename =
  let ch = open_in filename in
  let v = ParRwhile.pValT LexRwhile.token (Lexing.from_channel ch) in
  close_in ch;
  v

let examples_dir = "../examples"

let test_file_rep () =
  let prog = parse_file_program (examples_dir ^ "/rep.rwhile") in
  let data = parse_file_val (examples_dir ^ "/list123.val") in
  let result = EvalRwhile.evalProgram prog data in
  let expected = parse_file_val (examples_dir ^ "/list123.val") in
  Alcotest.(check valT_testable) "rep.rwhile" expected result

let test_file_enumeration () =
  let prog = parse_file_program (examples_dir ^ "/enumeration.rwhile") in
  let data = parse_file_val (examples_dir ^ "/nil.val") in
  let _result = EvalRwhile.evalProgram prog data in
  Alcotest.(check unit) "enumeration.rwhile runs" () ()

let test_file_length () =
  let prog = parse_file_program (examples_dir ^ "/length.rwhile") in
  let data = parse_file_val (examples_dir ^ "/list123.val") in
  let result = EvalRwhile.evalProgram prog data in
  (* length of ('1.('2.('3.nil))) is 3, result is (list . length) *)
  Alcotest.(check bool) "length.rwhile produces non-nil" true (result <> VNil)

let test_file_minus () =
  let prog = parse_file_program (examples_dir ^ "/minus.rwhile") in
  let data = parse_file_val (examples_dir ^ "/minus.val") in
  let result = EvalRwhile.evalProgram prog data in
  (* (4.3) -> (1.3) *)
  let expected = VCons (VCons (VNil, VNil), VCons (VNil, VCons (VNil, VCons (VNil, VNil)))) in
  Alcotest.(check valT_testable) "minus.rwhile (4-3=1)" expected result

let test_file_compare () =
  let prog = parse_file_program (examples_dir ^ "/compare.rwhile") in
  List.iter (fun vf ->
    let data = parse_file_val (examples_dir ^ "/" ^ vf) in
    let _result = EvalRwhile.evalProgram prog data in
    Alcotest.(check unit) ("compare.rwhile + " ^ vf) () ()
  ) ["compare0.val"; "compare1.val"; "compare2.val"]

let test_file_rle () =
  let prog = parse_file_program (examples_dir ^ "/rle.rwhile") in
  List.iter (fun vf ->
    let data = parse_file_val (examples_dir ^ "/" ^ vf) in
    let _result = EvalRwhile.evalProgram prog data in
    Alcotest.(check unit) ("rle.rwhile + " ^ vf) () ()
  ) ["rle0.val"; "rle1.val"; "rle2.val"; "rle3.val"; "rle4.val"]

let test_file_inverse () =
  let prog = parse_file_program (examples_dir ^ "/ri.rwhile") in
  let inv = InvRwhile.invProgram prog in
  (* inv(inv(p)) = p should hold *)
  let inv2 = InvRwhile.invProgram inv in
  Alcotest.(check program_testable) "ri.rwhile inv involution" prog inv2

let test_file_p2d () =
  let prog = parse_file_program (examples_dir ^ "/reverse.rwhile") in
  let data = Program2DataRwhile.program2data prog in
  (* Verify the p2d result matches the expected .val file *)
  let expected = parse_file_val (examples_dir ^ "/reverse.val") in
  Alcotest.(check valT_testable) "p2d reverse.rwhile" expected data

(* Helper: [rint]((p_data . d)) = (p_data . [p](d))
 * Verify that the self-interpreter reproduces the direct result. *)
let check_ri prog_name input expected_output =
  let ri = parse_file_program (examples_dir ^ "/ri.rwhile") in
  let prog = parse_file_program (examples_dir ^ "/" ^ prog_name ^ ".rwhile") in
  let prog_data = Program2DataRwhile.program2data prog in
  let ri_input = VCons (prog_data, input) in
  let ri_result = EvalRwhile.evalProgram ri ri_input in
  let expected = VCons (prog_data, expected_output) in
  Alcotest.(check valT_testable)
    ("[rint]((" ^ prog_name ^ " . input)) = (" ^ prog_name ^ " . [" ^ prog_name ^ "](input))")
    expected ri_result

let test_ri_id_nil () =
  (* [rint]((id . nil)) = (id_data . nil) *)
  check_ri "id" VNil VNil

let test_ri_swap () =
  (* [rint]((swap . ('a.'b))) = (swap_data . ('b.'a)) *)
  let input = VCons (atom "'a", atom "'b") in
  let expected = VCons (atom "'b", atom "'a") in
  check_ri "swap" input expected

let test_ri_reverse () =
  (* [rint]((reverse . [a,b,c])) = (reverse_data . [c,b,a]) *)
  let input = parse_val "('a . ('b . ('c . nil)))" in
  let expected = parse_val "('c . ('b . ('a . nil)))" in
  check_ri "reverse" input expected

let test_ri_minus () =
  (* [rint]((minus . (2.1))) = (minus_data . [minus]((2.1)))
   * minus(2,1): 2-1=1, output = ((nil.nil).(nil.nil)) = (1.1) per minus semantics *)
  let prog = parse_file_program (examples_dir ^ "/minus.rwhile") in
  let input = parse_val "((nil . (nil . nil)) . (nil . nil))" in
  let direct = EvalRwhile.evalProgram prog input in
  check_ri "minus" input direct

let test_ri_length () =
  (* [rint]((length . [a,b,c])) = (length_data . [length]([a,b,c])) *)
  let prog = parse_file_program (examples_dir ^ "/length.rwhile") in
  let input = parse_val "('a . ('b . ('c . nil)))" in
  let direct = EvalRwhile.evalProgram prog input in
  check_ri "length" input direct

let test_ri_compare () =
  (* [rint]((compare . (1.2))) = (compare_data . [compare]((1.2))) *)
  let prog = parse_file_program (examples_dir ^ "/compare.rwhile") in
  let input = parse_val "((nil . nil) . (nil . (nil . nil)))" in
  let direct = EvalRwhile.evalProgram prog input in
  check_ri "compare" input direct

let test_ri_rep () =
  (* [rint]((rep . ('a.'b))) = (rep_data . [rep](('a.'b))) *)
  let prog = parse_file_program (examples_dir ^ "/rep.rwhile") in
  let input = VCons (atom "'a", atom "'b") in
  let direct = EvalRwhile.evalProgram prog input in
  check_ri "rep" input direct

let test_ri_rle () =
  (* [rint]((rle . input)) = (rle_data . [rle](input)) *)
  let prog = parse_file_program (examples_dir ^ "/rle.rwhile") in
  let input = parse_file_val (examples_dir ^ "/rle0.val") in
  let direct = EvalRwhile.evalProgram prog input in
  check_ri "rle" input direct

let test_ri_ri_id () =
  (* [rint]((rint . (id . 'a))) = (rint . [rint]((id . 'a))) = (rint . (id . 'a)) *)
  let ri = parse_file_program (examples_dir ^ "/ri.rwhile") in
  let ri_data = Program2DataRwhile.program2data ri in
  let id_data = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/id.rwhile")) in
  (* inner: [rint]((id . 'a)) = (id . 'a) *)
  let inner_input = VCons (id_data, atom "'a") in
  let inner_result = EvalRwhile.evalProgram ri inner_input in
  (* outer: [rint]((rint . (id . 'a))) = (rint . inner_result) *)
  let outer_input = VCons (ri_data, inner_input) in
  let outer_result = EvalRwhile.evalProgram ri outer_input in
  let expected = VCons (ri_data, inner_result) in
  Alcotest.(check valT_testable)
    "[rint]((rint.(id.'a))) = (rint.(id.'a))"
    expected outer_result

let test_ri_ri_ri_id () =
  (* [rint]((rint . (rint . (id . 'a)))) = (rint . [rint]((rint . (id . 'a))))
     = (rint . (rint . (id . 'a))) *)
  let ri = parse_file_program (examples_dir ^ "/ri.rwhile") in
  let ri_data = Program2DataRwhile.program2data ri in
  let id_data = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/id.rwhile")) in
  let level0 = VCons (id_data, atom "'a") in          (* (id . 'a) *)
  let level1 = VCons (ri_data, level0) in              (* (rint . (id . 'a)) *)
  let level2 = VCons (ri_data, level1) in              (* (rint . (rint . (id . 'a))) *)
  let result = EvalRwhile.evalProgram ri level2 in
  (* [rint]((rint.(rint.(id.'a)))) = (rint . [rint]((rint.(id.'a)))) = (rint . (rint . (id . 'a))) *)
  let expected = VCons (ri_data, level1) in
  Alcotest.(check valT_testable)
    "[rint]((rint.(rint.(id.'a)))) = (rint.(rint.(id.'a)))"
    expected result

let test_file_lookup () =
  let prog = parse_file_program (examples_dir ^ "/lookup.rwhile") in
  let data = parse_file_val (examples_dir ^ "/nil.val") in
  let result = EvalRwhile.evalProgram prog data in
  let expected = VAtom (Atom "'22") in
  Alcotest.(check valT_testable) "lookup.rwhile" expected result

let test_file_lookup_ppl2015 () =
  let prog = parse_file_program (examples_dir ^ "/lookup_ppl2015.rwhile") in
  let data = parse_file_val (examples_dir ^ "/nil.val") in
  let result = EvalRwhile.evalProgram prog data in
  let expected = VAtom (Atom "'11") in
  Alcotest.(check valT_testable) "lookup_ppl2015.rwhile" expected result

(* ===== Specializer (spec.rwhile) tests ===== *)

(* Helper: given spec output (P . (P_res . S)), extract residual P_res *)
let extract_residual output =
  match output with
  | VCons (_, VCons (p_res, _)) -> p_res
  | _ -> failwith ("unexpected spec output format: " ^ show_val output)

let with_extensions ?(array=false) ?(autofi=false) f =
  let old_array = !(EvalRwhile.enable_array) in
  let old_autofi = !(EvalRwhile.enable_autofi) in
  EvalRwhile.enable_array := array;
  EvalRwhile.enable_autofi := autofi;
  Fun.protect f ~finally:(fun () ->
    EvalRwhile.enable_array := old_array;
    EvalRwhile.enable_autofi := old_autofi)

(* Helper: run program_as_data via ri.rwhile with given dynamic input,
   return the output data (tl of ri result) *)
let run_via_ri prog_data dyn_input =
  let ri = parse_file_program (examples_dir ^ "/ri.rwhile") in
  let v = VCons (prog_data, dyn_input) in
  let result = EvalRwhile.evalProgram ri v in
  match result with
  | VCons (_, data) -> data
  | v -> v

let test_spec_id_nil_runs () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let spec_input = parse_file_val (examples_dir ^ "/id_and_nil.p_val") in
  let result = EvalRwhile.evalProgram spec spec_input in
  Alcotest.(check bool) "spec result is non-nil" true (result <> VNil)

let test_spec_output_structure () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let spec_input = parse_file_val (examples_dir ^ "/id_and_nil.p_val") in
  let output = EvalRwhile.evalProgram spec spec_input in
  (* New format: output IS the residual program (('var.I).(cond_cmd.('var.J))) *)
  Alcotest.(check bool) "output is a program (VCons pair)"
    true
    (match output with VCons (_, VCons (_, _)) -> true | _ -> false)

let test_spec_residual_semantics_id () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let spec_input = parse_file_val (examples_dir ^ "/id_and_nil.p_val") in
  let output = EvalRwhile.evalProgram spec spec_input in
  let result = run_via_ri output VNil in
  Alcotest.(check valT_testable) "spec(id,nil) residual on nil = nil" VNil result

let test_spec_residual_semantics_swap () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let spec_input = parse_file_val (examples_dir ^ "/swap.p_val") in
  let output = EvalRwhile.evalProgram spec spec_input in
  let result = run_via_ri output VNil in
  let expected = parse_val "('b . 'a)" in
  Alcotest.(check valT_testable) "spec(swap,('a.'b)) residual on nil = ('b.'a)" expected result

let test_spec_first_projection_ri_reverse () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let spec_input = parse_file_val (examples_dir ^ "/reverse_and_list123.p_val") in
  let output = EvalRwhile.evalProgram spec spec_input in
  let result = run_via_ri output VNil in
  let expected = parse_val "('c . ('b . ('a . nil)))" in
  Alcotest.(check valT_testable) "spec(reverse,list123) residual on nil = reversed list" expected result

(* ===== Partial mode tests ===== *)

let test_spec_partial_swap () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let swap_data = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/swap.rwhile")) in
  (* Q = [spec]((swap.'a))  — input to spec is (swap_data . ('partial . 'a)) *)
  let partial_input = VCons (swap_data, VCons (atom "'partial", atom "'a")) in
  let residual = EvalRwhile.evalProgram spec partial_input in
  (* [Q]('b) = [swap](('a.'b)) = ('b.'a) *)
  let result = run_via_ri residual (atom "'b") in
  let expected = VCons (atom "'b", atom "'a") in
  Alcotest.(check valT_testable) "[[spec]((swap.'a))]('b) = ('b.'a)"
    expected result

(* ===== First Futamura projection tests =====
 * [[spec]((rint . p))](d) = [rint]((p . d)) = (p . [p](d))
 *)

(* Helper: test first Futamura projection for program prog_name with input d.
 * comp_p = [spec]((rint . p)), then [comp_p](d) should = (p . [p](d)) *)
let check_first_projection prog_name d =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let ri_data = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/ri.rwhile")) in
  let prog = parse_file_program (examples_dir ^ "/" ^ prog_name ^ ".rwhile") in
  let prog_data = Program2DataRwhile.program2data prog in
  (* comp_p = [spec]((rint . p)) *)
  let input = VCons (ri_data, VCons (atom "'partial", prog_data)) in
  let comp_p = EvalRwhile.evalProgram spec input in
  (* [comp_p](d) = [rint]((p . d)) = (p . [p](d)) *)
  let result = run_via_ri comp_p d in
  let direct = EvalRwhile.evalProgram prog d in
  let expected = VCons (prog_data, direct) in
  Alcotest.(check valT_testable)
    ("[[spec]((rint." ^ prog_name ^ "))](d) = (" ^ prog_name ^ ".[" ^ prog_name ^ "](d))")
    expected result

let test_fp1_id () =
  (* [[spec]((rint.id))]('a) = (id . 'a) *)
  check_first_projection "id" (atom "'a")

let test_fp1_swap () =
  (* [[spec]((rint.swap))](('a.'b)) = (swap . ('b.'a)) *)
  check_first_projection "swap" (VCons (atom "'a", atom "'b"))

let test_fp1_reverse () =
  (* [[spec]((rint.reverse))]([a,b,c]) = (reverse . [c,b,a]) *)
  check_first_projection "reverse" (parse_val "('a . ('b . ('c . nil)))")

let test_spec_ext_id_nil_runs () =
  with_extensions ~array:true ~autofi:true @@ fun () ->
  let spec = parse_file_program (examples_dir ^ "/spec_ext.rwhile") in
  let spec_input = parse_file_val (examples_dir ^ "/id_and_nil.p_val") in
  let result = EvalRwhile.evalProgram spec spec_input in
  Alcotest.(check bool) "spec_ext result is non-nil" true (result <> VNil)

(* ===== Macro-level tests for spec.rwhile ===== *)

let test_spec_macro_lookup () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Arr Idx <= In; LOOKUP(Arr,Idx,Res); Out <= cons Arr (cons Idx Res); write Out" in
  let arr = pair (atom "'z") (pair (atom "'a") (pair (atom "'b") VNil)) in
  let input = pair arr idx1 in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair arr (pair idx1 (atom "'a")) in
  Alcotest.(check valT_testable) "LOOKUP preserves array and returns indexed value" expected result

let test_spec_macro_update () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Arr (cons Idx Val) <= In; UPDATE(Arr,Idx,Val); Out <= cons Arr (cons Idx Val); write Out" in
  let arr = pair VNil (pair VNil VNil) in
  let input = pair arr (pair idx1 (atom "'x")) in
  let result = EvalRwhile.evalProgram prog input in
  let expected_arr = pair VNil (pair (atom "'x") VNil) in
  let expected = pair expected_arr (pair idx1 (atom "'x")) in
  Alcotest.(check valT_testable) "UPDATE reversibly updates indexed slot" expected result

let test_spec_macro_spec_exp_static_var () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl E <= In; SPEC-EXP(E,RE); Out <= cons Vl (cons E RE); write Out" in
  let vl = pair (static_entry (atom "'a")) VNil in
  let e = parse_val "('var . nil)" in
  let input = pair vl e in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair vl (pair e (static_entry (atom "'a"))) in
  Alcotest.(check valT_testable) "SPEC-EXP static variable" expected result

let test_spec_macro_spec_exp_dynamic_var () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl E <= In; SPEC-EXP(E,RE); Out <= cons Vl (cons E RE); write Out" in
  let vl = pair (dynamic_entry VNil) VNil in
  let e = parse_val "('var . nil)" in
  let input = pair vl e in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair vl (pair e (dynamic_entry e)) in
  Alcotest.(check valT_testable) "SPEC-EXP dynamic variable" expected result

let test_spec_macro_lift_static () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read R; LIFT(R,E); Out <= cons R E; write Out" in
  let input = static_entry (atom "'a") in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair (static_entry (atom "'a")) (parse_val "('val . 'a)") in
  Alcotest.(check valT_testable) "LIFT static result" expected result

let test_spec_macro_lift_dynamic () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read R; LIFT(R,E); Out <= cons R E; write Out" in
  let dyn = parse_val "('var . nil)" in
  let input = dynamic_entry dyn in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair (dynamic_entry dyn) dyn in
  Alcotest.(check valT_testable) "LIFT dynamic result" expected result

let test_spec_macro_pat_leaf_static () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl PP <= In; PAT-LEAF-STATIC(PP,Stat); Out <= cons Vl (cons PP Stat); write Out" in
  let vl = pair (static_entry (atom "'a")) VNil in
  let pp = parse_val "('var . nil)" in
  let input = pair vl pp in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair vl (pair pp vtrue) in
  Alcotest.(check valT_testable) "PAT-LEAF-STATIC for static var" expected result

let test_spec_macro_check_pat_static () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl PP <= In; CHECK-PAT-STATIC(PP,Stat); Out <= cons Vl (cons PP Stat); write Out" in
  let vl = pair (static_entry (atom "'a")) (pair (static_entry (atom "'b")) VNil) in
  let pp = parse_val "('cons . (('var . nil) . ('var . (nil . nil))))" in
  let input = pair vl pp in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair vl (pair pp vtrue) in
  Alcotest.(check valT_testable) "CHECK-PAT-STATIC for one-level cons" expected result

let test_spec_macro_pat_read_leaf () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl PP <= In; PAT-READ-LEAF(PP,PV); Out <= cons Vl (cons PP PV); write Out" in
  let vl = pair (static_entry (atom "'a")) VNil in
  let pp = parse_val "('var . nil)" in
  let input = pair vl pp in
  let result = EvalRwhile.evalProgram prog input in
  let expected_vl = pair (dynamic_entry VNil) VNil in
  let expected = pair expected_vl (pair pp (atom "'a")) in
  Alcotest.(check valT_testable) "PAT-READ-LEAF reads and clears slot" expected result

let test_spec_macro_pat_read_simple () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl PP <= In; PAT-READ-SIMPLE(PP,PV); Out <= cons Vl (cons PP PV); write Out" in
  let vl = pair (static_entry (atom "'a")) (pair (static_entry (atom "'b")) VNil) in
  let pp = parse_val "('cons . (('var . nil) . ('var . (nil . nil))))" in
  let input = pair vl pp in
  let result = EvalRwhile.evalProgram prog input in
  let expected_vl = pair (dynamic_entry VNil) (pair (dynamic_entry VNil) VNil) in
  let expected = pair expected_vl (pair pp (pair (atom "'a") (atom "'b"))) in
  Alcotest.(check valT_testable) "PAT-READ-SIMPLE for one-level cons" expected result

let test_spec_macro_pat_write_leaf () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl (cons PP PV) <= In; PAT-WRITE-LEAF(PP,PV); Out <= cons Vl PP; write Out" in
  let vl = pair (dynamic_entry VNil) VNil in
  let pp = parse_val "('var . nil)" in
  let input = pair vl (pair pp (atom "'a")) in
  let result = EvalRwhile.evalProgram prog input in
  let expected_vl = pair (static_entry (atom "'a")) VNil in
  let expected = pair expected_vl pp in
  Alcotest.(check valT_testable) "PAT-WRITE-LEAF writes static slot" expected result

let test_spec_macro_pat_write_simple () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read In; cons Vl (cons PP PV) <= In; PAT-WRITE-SIMPLE(PP,PV); Out <= cons Vl PP; write Out" in
  let vl = pair (dynamic_entry VNil) (pair (dynamic_entry VNil) VNil) in
  let pp = parse_val "('cons . (('var . nil) . ('var . (nil . nil))))" in
  let input = pair vl (pair pp (pair (atom "'a") (atom "'b"))) in
  let result = EvalRwhile.evalProgram prog input in
  let expected_vl = pair (static_entry (atom "'a")) (pair (static_entry (atom "'b")) VNil) in
  let expected = pair expected_vl pp in
  Alcotest.(check valT_testable) "PAT-WRITE-SIMPLE for one-level cons" expected result

let test_spec_macro_make_seq () =
  let prog = parse_macro_harness (examples_dir ^ "/spec.rwhile")
    "read RCode; MAKE-SEQ(RCode,Cmd); write Cmd" in
  let c1 = parse_val "('ass . (('var . nil) . ('val . nil)))" in
  let c2 = parse_val "('rep . (('var . nil) . ('var . (nil . nil))))" in
  let input = pair c2 (pair c1 VNil) in
  let expected = parse_val "('seq . (('ass . (('var . nil) . ('val . nil))) . ('rep . (('var . nil) . ('var . (nil . nil))))) )" in
  let result = EvalRwhile.evalProgram prog input in
  Alcotest.(check valT_testable) "MAKE-SEQ folds reverse residual list" expected result

(* ===== Macro-level tests for spec_ext.rwhile ===== *)

let test_spec_ext_macro_spec_exp_static_var () =
  with_extensions ~array:true ~autofi:true @@ fun () ->
  let prog = parse_macro_harness (examples_dir ^ "/spec_ext.rwhile")
    "read In; cons Vl E <= In; SPEC-EXP(E,RE); Out <= cons Vl (cons E RE); write Out" in
  let vl = pair (static_entry (atom "'a")) VNil in
  let e = parse_val "('var . nil)" in
  let input = pair vl e in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair vl (pair e (static_entry (atom "'a"))) in
  Alcotest.(check valT_testable) "spec_ext SPEC-EXP static variable" expected result

let test_spec_ext_macro_lift_dynamic () =
  with_extensions ~array:true ~autofi:true @@ fun () ->
  let prog = parse_macro_harness (examples_dir ^ "/spec_ext.rwhile")
    "read R; LIFT(R,E); Out <= cons R E; write Out" in
  let dyn = parse_val "('var . nil)" in
  let input = dynamic_entry dyn in
  let result = EvalRwhile.evalProgram prog input in
  let expected = pair (dynamic_entry dyn) dyn in
  Alcotest.(check valT_testable) "spec_ext LIFT dynamic result" expected result

let test_spec_ext_macro_make_seq () =
  with_extensions ~array:true ~autofi:true @@ fun () ->
  let prog = parse_macro_harness (examples_dir ^ "/spec_ext.rwhile")
    "read RCode; MAKE-SEQ(RCode,Cmd); write Cmd" in
  let c1 = parse_val "('ass . (('var . nil) . ('val . nil)))" in
  let c2 = parse_val "('rep . (('var . nil) . ('var . (nil . nil))))" in
  let input = pair c2 (pair c1 VNil) in
  let expected = parse_val "('seq . (('ass . (('var . nil) . ('val . nil))) . ('rep . (('var . nil) . ('var . (nil . nil))))) )" in
  let result = EvalRwhile.evalProgram prog input in
  Alcotest.(check valT_testable) "spec_ext MAKE-SEQ folds reverse residual list" expected result

(* ===== Interpreter robustness / bug-fix regression tests ===== *)

(* Assert that running [thunk ()] raises Failure whose message contains [sub]. *)
let check_fail_contains name sub thunk =
  match (try ignore (thunk ()); None with Failure m -> Some m) with
  | None -> Alcotest.failf "%s: expected a Failure, but none was raised" name
  | Some m ->
     Alcotest.(check bool) (name ^ ": message contains \"" ^ sub ^ "\"")
       true (find_substring m sub <> None)

(* BUG: input value with list-notation sugar must be desugared, exactly like a
 * list literal written inside the program. *)
let test_list_input_desugared () =
  (* X ^= nil is a no-op on a non-nil X, so this is the identity program. *)
  let prog = parse_program "read X; X ^= nil; write X" in
  let out  = EvalRwhile.evalProgram prog (parse_val "['a, 'b, 'c]") in
  let expected = parse_val "('a . ('b . ('c . nil)))" in
  Alcotest.(check valT_testable) "list-syntax input desugared to cons-chain" expected out

(* list-syntax input used by hd/=?: previously raised "No head". *)
let test_list_input_hd () =
  let prog = parse_program "read X; cons H T <= X; T <= cons H T; write T" in
  let out  = EvalRwhile.evalProgram prog (parse_val "['a, 'b]") in
  let expected = parse_val "('a . ('b . nil))" in
  Alcotest.(check valT_testable) "hd/cons on list-syntax input" expected out

(* BUG: inv_evalPat must desugar a literal pattern (PVal) before comparing, so a
 * cons literal containing list sugar matches the equivalent constructed value. *)
let test_pval_list_pattern_desugar () =
  let prog = parse_program "read X; (nil . ['a]) <= cons nil (cons 'a nil); write X" in
  let out  = EvalRwhile.evalProgram prog VNil in
  Alcotest.(check valT_testable) "literal pattern with list sugar matches" VNil out

(* BUG: a variable that occurs only inside show must still get a store slot
 * (previously raised an uncaught Not_found). *)
let test_show_var_collected () =
  let prog = parse_program "read X; show GHOST; write X" in
  let out  = EvalRwhile.evalProgram prog (atom "'a") in
  Alcotest.(check valT_testable) "show-only variable does not crash" (atom "'a") out

(* BUG: loop reversibility violation must be a caught Failure with a useful
 * message, not an OCaml Assert_failure (and not silently skipped). *)
let test_loop_reversibility_caught () =
  check_fail_contains "loop reversibility" "not false after the loop body"
    (fun () -> eval_string
        "read D; from =? X nil do Z ^= 'z loop Y ^= 'y until =? Z nil; write D" "nil")

(* BUG: a non-linear replacement pattern (a variable used twice) must be
 * detected and reported (non-fatal warning). *)
let test_nonlinear_pattern_detected () =
  let prog = parse_program "read X; Y <= cons X X; write Y" in
  let viols = EvalRwhile.linearity_violations prog in
  Alcotest.(check bool) "cons X X flagged as non-linear" true (List.length viols >= 1);
  (* A linear program produces no violations. *)
  let ok = parse_program "read X; Y <= cons X nil; write Y" in
  Alcotest.(check int) "linear program has no violations" 0
    (List.length (EvalRwhile.linearity_violations ok))

(* BUG: the not-all-cleared error must name the actually-dirty variable. *)
let test_noncleared_names_var () =
  check_fail_contains "non-cleared names Y" "Y"
    (fun () -> eval_string "read X; Y ^= 'junk; write X" "'a")

(* New: -llm-errors mode emits a structured, parseable block. *)
let test_llm_error_format () =
  EvalRwhile.llm_errors := true;
  let m =
    Fun.protect ~finally:(fun () -> EvalRwhile.llm_errors := false)
      (fun () -> try ignore (eval_string "read X; Y ^= hd X; write X" "'a"); ""
                 with Failure m -> m) in
  Alcotest.(check bool) "has [RWHILE-ERROR] header" true (find_substring m "[RWHILE-ERROR]" <> None);
  Alcotest.(check bool) "has category field"        true (find_substring m "category: no-head" <> None);
  Alcotest.(check bool) "has hint field"            true (find_substring m "hint:" <> None)

(* New: plain mode is unchanged (no structured wrapper). *)
let test_plain_error_unchanged () =
  Alcotest.check_raises "plain hd nil message unchanged"
    (Failure "No head. Expression hd nil has value nil")
    (fun () -> ignore (eval_string "read X; Y ^= hd nil; write X" "'a"))

(* ===== Partially-static annotated-value (AV) algebra (Stage 1 foundation) =====
 * av.rwhile implements the AV algebra (cons/hd/tl over 'S/'D/'C tags) that will
 * back a partially-static rewrite of spec.rwhile (see
 * analysis_partial_static_design.md). These check the key property the current
 * spec lacks: cons(static, dynamic) keeps the static part recoverable. *)
let check_av name input_str expected_str =
  let prog = parse_file_program (examples_dir ^ "/av.rwhile") in
  let out  = EvalRwhile.evalProgram prog (parse_val input_str) in
  Alcotest.(check valT_testable) name (parse_val expected_str) out

let test_av_hd_static () =
  check_av "hd static" "('hd . ('S . ('a . 'b)))" "('S . 'a)"
let test_av_hd_partial () =
  (* hd of a partially-static cons recovers the static head *)
  check_av "hd partial-static"
    "('hd . ('C . (('S . 'a) . ('D . ('var . nil)))))" "('S . 'a)"
let test_av_hd_dynamic () =
  check_av "hd dynamic"
    "('hd . ('D . ('var . nil)))" "('D . ('hd . ('var . nil)))"
let test_av_tl_partial () =
  check_av "tl partial-static"
    "('tl . ('C . (('S . 'a) . ('D . ('var . nil)))))" "('D . ('var . nil))"
let test_av_cons_both_static () =
  check_av "cons both-static folds"
    "('cons . (('S . 'a) . ('S . 'b)))" "('S . ('a . 'b))"
let test_av_cons_mixed_keeps_static () =
  (* the crux: a static/dynamic cons stays partially static (not collapsed) *)
  check_av "cons mixed keeps static car"
    "('cons . (('S . 'a) . ('D . ('var . nil))))"
    "('C . (('S . 'a) . ('D . ('var . nil))))"
let test_av_lift_static () =
  check_av "lift static -> val" "('lift . ('S . 'a))" "('val . 'a)"
let test_av_lift_dynamic () =
  check_av "lift dynamic -> code" "('lift . ('D . ('var . nil)))" "('var . nil)"
let test_av_lift_partial () =
  (* lift recurses through 'C, lowering static leaves to 'val and keeping code *)
  check_av "lift partial-static cons"
    "('lift . ('C . (('S . 'a) . ('D . ('var . nil)))))"
    "('cons . (('val . 'a) . ('var . nil)))"
let test_av_lift_nested () =
  check_av "lift nested partial-static"
    "('lift . ('C . (('S . 'a) . ('C . (('S . 'b) . ('D . ('var . nil)))))))"
    "('cons . (('val . 'a) . ('cons . (('val . 'b) . ('var . nil)))))"
let test_av_eq_static_true () =
  check_av "eq static equal -> static true"
    "('eq . (('S . 'a) . ('S . 'a)))" "('S . (nil . nil))"
let test_av_eq_static_false () =
  check_av "eq static unequal -> static false"
    "('eq . (('S . 'a) . ('S . 'b)))" "('S . nil)"
let test_av_eq_mixed_dynamic () =
  (* one side dynamic -> residual eq with the static side lifted to ('val.v) *)
  check_av "eq mixed -> dynamic eq"
    "('eq . (('S . 'a) . ('D . ('var . nil))))"
    "('D . ('eq . (('val . 'a) . ('var . nil))))"

(* ===== Garbage / size measurement (Stage A) ===== *)

(* Assert a value's node count is within [limit] (regression guard on residual /
 * garbage size for the projection demos). *)
let assert_size_at_most name limit v =
  let n = EvalRwhile.count_nodes v in
  Alcotest.(check bool) (Printf.sprintf "%s: nodes %d <= %d" name n limit) true (n <= limit)

let test_count_nodes () =
  Alcotest.(check int) "nil = 1 node" 1 (EvalRwhile.count_nodes VNil);
  Alcotest.(check int) "atom = 1 node" 1 (EvalRwhile.count_nodes (atom "'a"));
  Alcotest.(check int) "('a.'b) = 3 nodes" 3 (EvalRwhile.count_nodes (parse_val "('a . 'b)"));
  Alcotest.(check int) "[a,b,c] = 7 nodes" 7
    (EvalRwhile.count_nodes (parse_val "('a . ('b . ('c . nil)))"));
  (* list-sugar input is desugared, so it counts the same as the cons form *)
  Alcotest.(check int) "['a,'b,'c] desugars to 7 nodes" 7
    (EvalRwhile.count_nodes (EvalRwhile.desugar_val (parse_val "['a, 'b, 'c]")))

(* Record (and guard) the garbage size of the currently-green spec-partial demo
 * [[spec]((swap.'a))] — its residual program-as-data. *)
let test_stats_spec_partial_residual () =
  let spec = parse_file_program (examples_dir ^ "/spec.rwhile") in
  let swap_data = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/swap.rwhile")) in
  let residual = EvalRwhile.evalProgram spec
    (VCons (swap_data, VCons (atom "'partial", atom "'a"))) in
  assert_size_at_most "spec-partial(swap) residual" 200 residual

(* ===== AV-based SPEC-EXP (Stage B step 2) =====
 * spec_av.rwhile's main is a harness: input (Vl . E), output (Vl . (E . RE)).
 * Store Vl below: slot0 = ('S.'a) static, slot1 = ('D.('var.(nil.nil))) dynamic. *)
let av_store = "(('S . 'a) . (('D . ('var . (nil . nil))) . nil))"

let check_spec_exp_av name e_str expected_re_str =
  let prog = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let input = pair (parse_val av_store) (parse_val e_str) in
  match EvalRwhile.evalProgram prog input with
  | VCons (_, VCons (_, re)) ->
     Alcotest.(check valT_testable) name (parse_val expected_re_str) re
  | _ -> Alcotest.failf "%s: unexpected output shape" name

let test_se_av_var_static () =
  check_spec_exp_av "var static" "('var . nil)" "('S . 'a)"
let test_se_av_var_dynamic () =
  check_spec_exp_av "var dynamic" "('var . (nil . nil))" "('D . ('var . (nil . nil)))"
let test_se_av_val () =
  check_spec_exp_av "val literal static" "('val . 'z)" "('S . 'z)"
let test_se_av_cons_partial () =
  (* CRUX: cons(static var, dynamic var) stays partially static (not collapsed) *)
  check_spec_exp_av "cons static/dynamic -> partial-static"
    "('cons . (('var . nil) . ('var . (nil . nil))))"
    "('C . (('S . 'a) . ('D . ('var . (nil . nil)))))"
let test_se_av_hd_recovers_static () =
  (* hd(cons static dynamic) recovers the static head — old SPEC-EXP could not *)
  check_spec_exp_av "hd of partial cons recovers static"
    "('hd . ('cons . (('var . nil) . ('var . (nil . nil)))))"
    "('S . 'a)"
let test_se_av_hd_dynamic () =
  check_spec_exp_av "hd of dynamic var stays dynamic"
    "('hd . ('var . (nil . nil)))" "('D . ('hd . ('var . (nil . nil))))"
let test_se_av_eq_static_resolves () =
  (* eq(static var, static literal) resolves to a static boolean (=> dispatch
   * like '=? Tag ...' specializes away) *)
  check_spec_exp_av "eq static var/literal -> static true"
    "('eq . (('var . nil) . ('val . 'a)))" "('S . (nil . nil))"

(* ===== AV-based SPEC-STEP (Stage B step 3: 'seq, 'ass) =====
 * Harness: input (Vl . Cmd), output (Vl' . (Cmd . RCode)). *)
let check_spec_step_av name vl_str cmd_str expected_str =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; cons Vl Cmd <= In; SPEC-CMD-AV(Cmd); Out <= cons Vl (cons Cmd RCode); write Out" in
  let out = EvalRwhile.evalProgram prog (pair (parse_val vl_str) (parse_val cmd_str)) in
  Alcotest.(check valT_testable) name (parse_val expected_str) out

let test_ss_av_ass_static_exec () =
  (* var0 static-nil, "var0 ^= 'a" -> executed statically, slot becomes ('S.'a),
   * no residual *)
  check_spec_step_av "ass static execution"
    "(('S . nil) . nil)"
    "('ass . (('var . nil) . ('val . 'a)))"
    "((('S . 'a) . nil) . (('ass . (('var . nil) . ('val . 'a))) . nil))"

let test_ss_av_ass_residualize () =
  (* var0 dynamic, "var0 ^= 'a" -> residualized as var0 ^= (val 'a) *)
  check_spec_step_av "ass residualize (dynamic var)"
    "(('D . ('var . nil)) . nil)"
    "('ass . (('var . nil) . ('val . 'a)))"
    "((('D . ('var . nil)) . nil) . (('ass . (('var . nil) . ('val . 'a))) . (('ass . (('var . nil) . ('val . 'a))) . nil)))"

let test_ss_av_ass_dynamic_expr () =
  (* var0 static-nil, "var0 ^= var1" with var1 dynamic -> residualized and var0
   * promoted to dynamic *)
  check_spec_step_av "ass dynamic expr promotes var"
    "(('S . nil) . (('D . ('var . (nil . nil))) . nil))"
    "('ass . (('var . nil) . ('var . (nil . nil))))"
    "((('D . ('var . nil)) . (('D . ('var . (nil . nil))) . nil)) . (('ass . (('var . nil) . ('var . (nil . nil)))) . (('ass . (('var . nil) . ('var . (nil . nil)))) . nil)))"

let test_ss_av_seq_static () =
  (* seq of two static assignments, both executed statically (no residual) *)
  check_spec_step_av "seq static execution"
    "(('S . nil) . nil)"
    "('seq . (('ass . (('var . nil) . ('val . 'a))) . ('ass . (('var . nil) . ('var . nil)))))"
    "((('S . nil) . nil) . (('seq . (('ass . (('var . nil) . ('val . 'a))) . ('ass . (('var . nil) . ('var . nil))))) . nil))"

(* ===== Test runner ===== *)

let () =
  Alcotest.run "R-WHILE Interpreter" [
    "store", [
      Alcotest.test_case "insert empty" `Quick test_insert_empty;
      Alcotest.test_case "insert existing" `Quick test_insert_existing;
      Alcotest.test_case "rupdate nil->val" `Quick test_rupdate_nil_to_val;
      Alcotest.test_case "rupdate val->same" `Quick test_rupdate_val_to_same;
      Alcotest.test_case "rupdate val->nil" `Quick test_rupdate_val_to_nil;
      Alcotest.test_case "rupdate different fails" `Quick test_rupdate_different_fails;
      Alcotest.test_case "rupdate not found" `Quick test_rupdate_not_found;
      Alcotest.test_case "update replace" `Quick test_update_replace;
      Alcotest.test_case "all cleared true" `Quick test_all_cleared_true;
      Alcotest.test_case "all cleared false" `Quick test_all_cleared_false;
    ];
    "eval-exp", [
      Alcotest.test_case "eval val" `Quick test_eval_val;
      Alcotest.test_case "eval var" `Quick test_eval_var;
      Alcotest.test_case "eval cons" `Quick test_eval_cons;
      Alcotest.test_case "eval hd" `Quick test_eval_hd;
      Alcotest.test_case "eval tl" `Quick test_eval_tl;
      Alcotest.test_case "eval hd nil fails" `Quick test_eval_hd_nil_fails;
      Alcotest.test_case "eval tl nil fails" `Quick test_eval_tl_nil_fails;
      Alcotest.test_case "eval =? true" `Quick test_eval_eq_true;
      Alcotest.test_case "eval =? false" `Quick test_eval_eq_false;
    ];
    "var-collect", [
      Alcotest.test_case "var program" `Quick test_var_program;
      Alcotest.test_case "var loop" `Quick test_var_loop;
    ];
    "inversion", [
      Alcotest.test_case "inv macro name" `Quick test_inv_macro_name;
      Alcotest.test_case "inv assignment" `Quick test_inv_ass;
      Alcotest.test_case "inv replacement" `Quick test_inv_rep;
      Alcotest.test_case "inv sequence" `Quick test_inv_seq;
      Alcotest.test_case "inv conditional" `Quick test_inv_cond;
      Alcotest.test_case "inv loop" `Quick test_inv_loop;
      Alcotest.test_case "inv program" `Quick test_inv_program;
      Alcotest.test_case "inv involution" `Quick test_inv_involution;
    ];
    "substitution", [
      Alcotest.test_case "subst rident" `Quick test_subst_rident;
      Alcotest.test_case "subst rident unchanged" `Quick test_subst_rident_unchanged;
      Alcotest.test_case "subst exp" `Quick test_subst_exp;
      Alcotest.test_case "subst com" `Quick test_subst_com;
      Alcotest.test_case "subst program" `Quick test_subst_program;
    ];
    "macro", [
      Alcotest.test_case "expand simple" `Quick test_macro_expand_simple;
      Alcotest.test_case "expand inv" `Quick test_macro_expand_inv;
      Alcotest.test_case "not found" `Quick test_macro_not_found;
      Alcotest.test_case "arity mismatch" `Quick test_macro_arity_mismatch;
    ];
    "p2d", [
      Alcotest.test_case "p2d simple" `Quick test_p2d_simple;
      Alcotest.test_case "conss singleton" `Quick test_p2d_conss;
      Alcotest.test_case "conss pair" `Quick test_p2d_conss_pair;
      Alcotest.test_case "conss triple" `Quick test_p2d_conss_triple;
    ];
    "eval-integration", [
      Alcotest.test_case "identity" `Quick test_eval_identity;
      Alcotest.test_case "rep" `Quick test_eval_rep;
      Alcotest.test_case "swap" `Quick test_eval_swap;
      Alcotest.test_case "reverse" `Quick test_eval_reverse;
      Alcotest.test_case "if true" `Quick test_eval_if_true;
      Alcotest.test_case "if false" `Quick test_eval_if_false;
      Alcotest.test_case "show" `Quick test_eval_show;
      Alcotest.test_case "cons exp" `Quick test_eval_cons_exp;
      Alcotest.test_case "eq check true" `Quick test_eval_eq_check;
      Alcotest.test_case "eq check false" `Quick test_eval_eq_check_false;
      Alcotest.test_case "macro minus" `Quick test_eval_macro_minus;
      Alcotest.test_case "reversibility" `Quick test_eval_reversibility;
      Alcotest.test_case "non-cleared fails" `Quick test_eval_non_cleared_fails;
    ];
    "stats", [
      Alcotest.test_case "count_nodes" `Quick test_count_nodes;
      Alcotest.test_case "spec-partial residual size" `Quick test_stats_spec_partial_residual;
    ];
    "spec-av-step", [
      Alcotest.test_case "ass static execution" `Quick test_ss_av_ass_static_exec;
      Alcotest.test_case "ass residualize" `Quick test_ss_av_ass_residualize;
      Alcotest.test_case "ass dynamic expr" `Quick test_ss_av_ass_dynamic_expr;
      Alcotest.test_case "seq static" `Quick test_ss_av_seq_static;
    ];
    "spec-av-exp", [
      Alcotest.test_case "var static" `Quick test_se_av_var_static;
      Alcotest.test_case "var dynamic" `Quick test_se_av_var_dynamic;
      Alcotest.test_case "val literal" `Quick test_se_av_val;
      Alcotest.test_case "cons -> partial-static" `Quick test_se_av_cons_partial;
      Alcotest.test_case "hd recovers static" `Quick test_se_av_hd_recovers_static;
      Alcotest.test_case "hd dynamic" `Quick test_se_av_hd_dynamic;
      Alcotest.test_case "eq static resolves" `Quick test_se_av_eq_static_resolves;
    ];
    "av-algebra", [
      Alcotest.test_case "hd static" `Quick test_av_hd_static;
      Alcotest.test_case "hd partial-static" `Quick test_av_hd_partial;
      Alcotest.test_case "hd dynamic" `Quick test_av_hd_dynamic;
      Alcotest.test_case "tl partial-static" `Quick test_av_tl_partial;
      Alcotest.test_case "cons both-static folds" `Quick test_av_cons_both_static;
      Alcotest.test_case "cons mixed keeps static" `Quick test_av_cons_mixed_keeps_static;
      Alcotest.test_case "lift static" `Quick test_av_lift_static;
      Alcotest.test_case "lift dynamic" `Quick test_av_lift_dynamic;
      Alcotest.test_case "lift partial-static" `Quick test_av_lift_partial;
      Alcotest.test_case "lift nested" `Quick test_av_lift_nested;
      Alcotest.test_case "eq static true" `Quick test_av_eq_static_true;
      Alcotest.test_case "eq static false" `Quick test_av_eq_static_false;
      Alcotest.test_case "eq mixed dynamic" `Quick test_av_eq_mixed_dynamic;
    ];
    "interpreter-robustness", [
      Alcotest.test_case "list-syntax input desugared" `Quick test_list_input_desugared;
      Alcotest.test_case "hd on list-syntax input" `Quick test_list_input_hd;
      Alcotest.test_case "literal pattern list-sugar desugar" `Quick test_pval_list_pattern_desugar;
      Alcotest.test_case "show-only variable collected" `Quick test_show_var_collected;
      Alcotest.test_case "loop reversibility caught" `Quick test_loop_reversibility_caught;
      Alcotest.test_case "non-linear pattern detected" `Quick test_nonlinear_pattern_detected;
      Alcotest.test_case "non-cleared names dirty var" `Quick test_noncleared_names_var;
      Alcotest.test_case "llm-errors structured format" `Quick test_llm_error_format;
      Alcotest.test_case "plain error message unchanged" `Quick test_plain_error_unchanged;
    ];
    "inv-eval", [
      Alcotest.test_case "inv swap" `Quick test_inv_eval_swap;
      Alcotest.test_case "inv reverse" `Quick test_inv_eval_reverse;
    ];
    "roundtrip", [
      Alcotest.test_case "parse/print val" `Quick test_parse_print_roundtrip_val;
      Alcotest.test_case "parse/print prog" `Quick test_parse_print_roundtrip_prog;
    ];
    "rint", [
      Alcotest.test_case "[rint]((id.nil))=(id.nil)" `Quick test_ri_id_nil;
      Alcotest.test_case "[rint]((swap.('a.'b)))=(swap.('b.'a))" `Quick test_ri_swap;
      Alcotest.test_case "[rint]((rep.('a.'b)))=(rep.[rep](('a.'b)))" `Quick test_ri_rep;
      Alcotest.test_case "[rint]((reverse.[a,b,c]))=(reverse.[c,b,a])" `Slow test_ri_reverse;
      Alcotest.test_case "[rint]((minus.(2.1)))=(minus.[minus]((2.1)))" `Quick test_ri_minus;
      Alcotest.test_case "[rint]((length.[a,b,c]))=(length.[length]([a,b,c]))" `Quick test_ri_length;
      Alcotest.test_case "[rint]((compare.(1.2)))=(compare.[compare]((1.2)))" `Quick test_ri_compare;
      Alcotest.test_case "[rint]((rle.input))=(rle.[rle](input))" `Slow test_ri_rle;
      Alcotest.test_case "[rint]((rint.(id.'a)))=(rint.(id.'a))" `Slow test_ri_ri_id;
      Alcotest.test_case "[rint]((rint.(rint.(id.'a))))=(rint.(rint.(id.'a)))" `Slow test_ri_ri_ri_id;
    ];
    (* Full-static spec tests removed: types don't match partial mode format.
     * Proper spec input is (p . ('partial . s)), not (p . s). *)
    "spec-partial", [
      Alcotest.test_case "[[spec]((swap.'a))]('b)=('b.'a)" `Quick test_spec_partial_swap;
    ];
    "first-projection", [
      Alcotest.test_case "[[spec]((rint.id))]('a)=(id.'a)" `Slow test_fp1_id;
      Alcotest.test_case "[[spec]((rint.swap))](('a.'b))=(swap.('b.'a))" `Slow test_fp1_swap;
      Alcotest.test_case "[[spec]((rint.reverse))]([a,b,c])=(reverse.[c,b,a])" `Slow test_fp1_reverse;
    ];
    "spec-ext", [
      Alcotest.test_case "spec_ext(id,nil) runs" `Quick test_spec_ext_id_nil_runs;
    ];
    "spec-macros", [
      Alcotest.test_case "LOOKUP" `Quick test_spec_macro_lookup;
      Alcotest.test_case "UPDATE" `Quick test_spec_macro_update;
      Alcotest.test_case "SPEC-EXP static var" `Quick test_spec_macro_spec_exp_static_var;
      Alcotest.test_case "SPEC-EXP dynamic var" `Quick test_spec_macro_spec_exp_dynamic_var;
      Alcotest.test_case "LIFT static" `Quick test_spec_macro_lift_static;
      Alcotest.test_case "LIFT dynamic" `Quick test_spec_macro_lift_dynamic;
      Alcotest.test_case "PAT-LEAF-STATIC" `Quick test_spec_macro_pat_leaf_static;
      Alcotest.test_case "CHECK-PAT-STATIC" `Quick test_spec_macro_check_pat_static;
      Alcotest.test_case "PAT-READ-LEAF" `Quick test_spec_macro_pat_read_leaf;
      Alcotest.test_case "PAT-READ-SIMPLE" `Quick test_spec_macro_pat_read_simple;
      Alcotest.test_case "PAT-WRITE-LEAF" `Quick test_spec_macro_pat_write_leaf;
      Alcotest.test_case "PAT-WRITE-SIMPLE" `Quick test_spec_macro_pat_write_simple;
      Alcotest.test_case "MAKE-SEQ" `Quick test_spec_macro_make_seq;
    ];
    "spec-ext-macros", [
      Alcotest.test_case "SPEC-EXP static var" `Quick test_spec_ext_macro_spec_exp_static_var;
      Alcotest.test_case "LIFT dynamic" `Quick test_spec_ext_macro_lift_dynamic;
      Alcotest.test_case "MAKE-SEQ" `Quick test_spec_ext_macro_make_seq;
    ];
    "file-integration", [
      Alcotest.test_case "rep.rwhile" `Quick test_file_rep;
      Alcotest.test_case "enumeration.rwhile" `Quick test_file_enumeration;
      Alcotest.test_case "length.rwhile" `Quick test_file_length;
      Alcotest.test_case "minus.rwhile" `Quick test_file_minus;
      Alcotest.test_case "compare.rwhile" `Quick test_file_compare;
      Alcotest.test_case "rle.rwhile" `Quick test_file_rle;
      Alcotest.test_case "inverse ri.rwhile" `Quick test_file_inverse;
      Alcotest.test_case "p2d reverse.rwhile" `Quick test_file_p2d;
      Alcotest.test_case "lookup.rwhile" `Quick test_file_lookup;
      Alcotest.test_case "lookup_ppl2015.rwhile" `Quick test_file_lookup_ppl2015;
    ];
  ]
