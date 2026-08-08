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

let contains_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  go 0

let rindex_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = if i < 0 then -1 else if String.sub s i m = sub then i else go (i - 1) in
  go (n - m)

(* spec_av's AV-CAPTURE draws residual temp indices from the global counter
 * TmpCtr, which spec_av's own main initialises (TEMP-IDX) and clears.  These
 * harnesses build their OWN main around spec_av's macros, so they must bracket
 * the body the same way -- otherwise the store-clean check trips on the counter
 * alone ("Some variables are not nil: TmpCtr := ..."), which looks like a
 * specialiser bug and is not one.  Injected here, in the one place, rather than
 * in each of the harness bodies. *)
let parse_macro_harness filename body =
  let prefix = macro_prefix filename in
  let body =
    if contains_sub prefix "TEMP-IDX" && contains_sub body "write" then begin
      let i = String.index body ';' in
      let w = rindex_sub body "write" in
      String.sub body 0 (i + 1) ^ " TEMP-IDX(TmpCtr); "
      ^ String.sub body (i + 1) (w - i - 1)
      ^ "TmpCtr ^= TmpCtr; " ^ String.sub body w (String.length body - w)
    end else body in
  parse_program (prefix ^ "\n" ^ body)

let eval_string prog_str val_str =
  let prog = parse_program prog_str in
  let data = parse_val val_str in
  EvalRwhile.evalProgram prog data

let vtrue = VCons (VNil, VNil)
let vfalse = VNil
let atom s = VAtom (Atom s)
let pair a b = VCons (a, b)
(* spec_av's main now takes a binding-time-aware input In = (Prog . (BT . Src)).
 * fp1 always supplies BT = 'S (the static-input half is genuinely static). *)
let spec_in prog src = VCons (prog, VCons (atom "'S", src))
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

(* Build a store (a Map) from an association list -- the store is now a
 * balanced-tree map (EvalRwhile.RIdentMap), not a list. *)
let store_of_list l =
  List.fold_left (fun m (x, v) -> EvalRwhile.RIdentMap.add x v m)
    EvalRwhile.RIdentMap.empty l

let test_insert_empty () =
  let id = RIdent "X" in
  Alcotest.(check (list (pair (of_pp (fun fmt (RIdent s) -> Format.pp_print_string fmt s)) valT_testable)))
    "insert into empty"
    [(id, VNil)]
    (EvalRwhile.insert (id, VNil) [])

let test_insert_existing () =
  let x = RIdent "X" in
  let store = [(x, VNil); (RIdent "Y", VNil)] in     (* insert is a list op *)
  let result = EvalRwhile.insert (x, VNil) store in
  Alcotest.(check int) "same length" 2 (List.length result)

let test_rupdate_nil_to_val () =
  let x = RIdent "X" in
  let store = store_of_list [(x, VNil)] in
  let result = EvalRwhile.rupdate (x, vtrue) store in
  Alcotest.(check valT_testable) "rupdate nil->val" vtrue (EvalRwhile.RIdentMap.find x result)

let test_rupdate_val_to_same () =
  let x = RIdent "X" in
  let store = store_of_list [(x, vtrue)] in
  let result = EvalRwhile.rupdate (x, vtrue) store in
  Alcotest.(check valT_testable) "rupdate val->nil" VNil (EvalRwhile.RIdentMap.find x result)

let test_rupdate_val_to_nil () =
  let x = RIdent "X" in
  let v = VCons (VNil, VCons (VNil, VNil)) in
  let store = store_of_list [(x, v)] in
  let result = EvalRwhile.rupdate (x, VNil) store in
  Alcotest.(check valT_testable) "rupdate keeps val" v (EvalRwhile.RIdentMap.find x result)

let test_rupdate_different_fails () =
  let x = RIdent "X" in
  let store = store_of_list [(x, VCons (VNil, VNil))] in
  Alcotest.check_raises "rupdate different values fails"
    (Failure "error in update")
    (fun () -> ignore (EvalRwhile.rupdate (x, VCons (VNil, VCons (VNil, VNil))) store))

let test_rupdate_not_found () =
  let x = RIdent "X" in
  Alcotest.check_raises "rupdate not found"
    (Failure ("Variable X is not found (1)"))
    (fun () -> ignore (EvalRwhile.rupdate (x, VNil) (store_of_list [])))

let test_update_replace () =
  let x = RIdent "X" in
  let store = store_of_list [(x, VNil)] in
  let result = EvalRwhile.update (x, vtrue) store in
  Alcotest.(check valT_testable) "update replaces" vtrue (EvalRwhile.RIdentMap.find x result)

let test_all_cleared_true () =
  let store = store_of_list [(RIdent "X", VNil); (RIdent "Y", VNil)] in
  Alcotest.(check bool) "all cleared" true (EvalRwhile.all_cleared store)

let test_all_cleared_false () =
  let store = store_of_list [(RIdent "X", VNil); (RIdent "Y", vtrue)] in
  Alcotest.(check bool) "not all cleared" false (EvalRwhile.all_cleared store)

(* ===== Expression evaluation tests ===== *)

let test_eval_val () =
  let store = store_of_list [] in
  let result = EvalRwhile.evalExp store (EVal VNil) in
  Alcotest.(check valT_testable) "eval nil literal" VNil result

let test_eval_var () =
  let x = RIdent "X" in
  let store = store_of_list [(x, vtrue)] in
  let result = EvalRwhile.evalExp store (EVar (Var x)) in
  Alcotest.(check valT_testable) "eval var" vtrue result

let test_eval_cons () =
  let store = store_of_list [] in
  let result = EvalRwhile.evalExp store (ECons (EVal VNil, EVal (VAtom (Atom "'a")))) in
  Alcotest.(check valT_testable) "eval cons" (VCons (VNil, VAtom (Atom "'a"))) result

let test_eval_hd () =
  let x = RIdent "X" in
  let v = VCons (VAtom (Atom "'a"), VNil) in
  let store = store_of_list [(x, v)] in
  let result = EvalRwhile.evalExp store (EHd (EVar (Var x))) in
  Alcotest.(check valT_testable) "eval hd" (VAtom (Atom "'a")) result

let test_eval_tl () =
  let x = RIdent "X" in
  let v = VCons (VAtom (Atom "'a"), VAtom (Atom "'b")) in
  let store = store_of_list [(x, v)] in
  let result = EvalRwhile.evalExp store (ETl (EVar (Var x))) in
  Alcotest.(check valT_testable) "eval tl" (VAtom (Atom "'b")) result

let test_eval_hd_nil_fails () =
  let store = store_of_list [] in
  Alcotest.check_raises "hd nil fails"
    (Failure "No head. Expression hd nil has value nil")
    (fun () -> ignore (EvalRwhile.evalExp store (EHd (EVal VNil))))

let test_eval_tl_nil_fails () =
  let store = store_of_list [] in
  Alcotest.check_raises "tl nil fails"
    (Failure "No tail. Expression tl nil has value nil")
    (fun () -> ignore (EvalRwhile.evalExp store (ETl (EVal VNil))))

let test_eval_eq_true () =
  let store = store_of_list [] in
  let result = EvalRwhile.evalExp store (EEq (EVal VNil, EVal VNil)) in
  Alcotest.(check valT_testable) "=? nil nil = true" vtrue result

let test_eval_eq_false () =
  let store = store_of_list [] in
  let result = EvalRwhile.evalExp store (EEq (EVal VNil, EVal (VAtom (Atom "'a")))) in
  Alcotest.(check valT_testable) "=? nil 'a = false" vfalse result

let test_eval_pair_cons () =
  let result = EvalRwhile.evalExp (store_of_list []) (EPair (EVal (VCons (VNil, VNil)))) in
  Alcotest.(check valT_testable) "pair? (nil.nil) = true" vtrue result

let test_eval_pair_atom () =
  let result = EvalRwhile.evalExp (store_of_list []) (EPair (EVal (VAtom (Atom "'a")))) in
  Alcotest.(check valT_testable) "pair? 'a = false" vfalse result

let test_eval_pair_nil () =
  let result = EvalRwhile.evalExp (store_of_list []) (EPair (EVal VNil)) in
  Alcotest.(check valT_testable) "pair? nil = false" vfalse result

(* parse + full-program round trip: confirms `pair?` lexes/parses and the p2d
 * encoding exists (program-to-data uses the 'pairp tag). *)
let test_pair_program () =
  let prog = parse_program "read X; R ^= pair? X; X ^= X; write R" in
  Alcotest.(check valT_testable) "pair? on a cons"
    vtrue (EvalRwhile.evalProgram prog (VCons (atom "'a", atom "'b")));
  Alcotest.(check valT_testable) "pair? on an atom"
    vfalse (EvalRwhile.evalProgram prog (atom "'a"));
  (* p2d encodes pair? as ('pairp . code) *)
  let d = Program2DataRwhile.program2data prog in
  Alcotest.(check bool) "p2d emits 'pairp tag" true
    (let s = show_val d in
     let rec contains i = i + 6 <= String.length s &&
       (String.sub s i 6 = "'pairp" || contains (i+1)) in contains 0)

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

(* ===== Wire-format bridge tests =====
   Cross-validate the Agda model RWhileSpecAVWire (encEx / parseEx) against the
   implementation's expression encoder/decoder (Program2DataRwhile.transExp /
   d_exp).  The Agda module mirrors d_exp line by line and proves a round trip
   parseEx (encEx e) ≡ just e; these tests pin the *same* wire trees and the
   *same* variable-index convention (unary nil-count, nil = 0) on the OCaml side. *)

(* d_exp on the exact wire tree of Agda's Examples.ex1-wire:
   'hd . ('cons . (('var . nil) . ('val . (nil . nil)))) *)
let test_wire_ex1_decode () =
  let a s = VAtom (Atom s) in
  let vtrue = VCons (VNil, VNil) in
  let wire =
    VCons (a "'hd",
      VCons (a "'cons",
        VCons (VCons (a "'var", VNil),
               VCons (a "'val", vtrue)))) in
  let expected =
    EHd (ECons (EVar (Var (RIdent "0")), EVal vtrue)) in
  Alcotest.(check bool) "d_exp matches Agda parseEx ex1" true
    (Program2DataRwhile.d_exp wire = expected)

(* d_exp on Agda's Examples.ex2-wire: eq of store slots 1 and 2.
   'eq . (('var . (nil.nil)) . ('var . (nil.(nil.nil)))) *)
let test_wire_ex2_decode () =
  let a s = VAtom (Atom s) in
  let idx1 = VCons (VNil, VNil) in
  let idx2 = VCons (VNil, VCons (VNil, VNil)) in
  let wire =
    VCons (a "'eq",
      VCons (VCons (a "'var", idx1),
             VCons (a "'var", idx2))) in
  let expected =
    EEq (EVar (Var (RIdent "1")), EVar (Var (RIdent "2"))) in
  Alcotest.(check bool) "d_exp matches Agda parseEx ex2" true
    (Program2DataRwhile.d_exp wire = expected)

(* transExp then d_exp round-trips an atom-free expression (no variables, to skip
   transRIdent's separate 1-based convention) — mirrors Agda's parse-enc. *)
let test_wire_roundtrip_structural () =
  let e = EHd (ECons (EVal VNil, EVal (VCons (VNil, VNil)))) in
  let back = Program2DataRwhile.d_exp (Program2DataRwhile.transExp e) in
  Alcotest.(check bool) "d_exp (transExp e) = e" true (back = e)

(* Command layer (mirrors Agda RWhileSpecAVWireCom.Examples.c0):
   d_com on the exact wire tree of cAss 0 (cons x1 x0) matches Agda parseCom.
   'ass . (('var . nil) . ('cons . (('var . (nil.nil)) . ('var . nil)))) *)
let test_wire_com_decode () =
  let a s = VAtom (Atom s) in
  let wire =
    VCons (a "'ass",
      VCons (VCons (a "'var", VNil),
        VCons (a "'cons",
          VCons (VCons (a "'var", VCons (VNil, VNil)),
                 VCons (a "'var", VNil))))) in
  let expected =
    CAss (RIdent "0", ECons (EVar (Var (RIdent "1")), EVar (Var (RIdent "0")))) in
  Alcotest.(check bool) "d_com matches Agda parseCom c0" true
    (Program2DataRwhile.d_com wire = expected)

(* transCom then d_com round-trips a variable-free command (skips the 'ass/'var
   index convention) — mirrors Agda's parse-enc-com. *)
let test_wire_com_roundtrip_structural () =
  let c = CSeq (CRep (PVal VNil, PVal (VCons (VNil, VNil))),
                CRep (PVal (VCons (VNil, VNil)), PVal VNil)) in
  let back = Program2DataRwhile.d_com (Program2DataRwhile.transCom c) in
  Alcotest.(check bool) "d_com (transCom c) = c" true (back = c)

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
  let store = store_of_list [(RIdent "X", VAtom (Atom "'a"))] in
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

(* ===== Simp: copy propagation over residual moves ===== *)
(* Motivation (2026-08-08).  Capture-on-escape in spec_av fixes the nested-pattern
 * bound but emits `Tmp <= ('var.k)` at EVERY escape, overwhelmingly for slots
 * that are never reused -- blowing the fp1 residual up 13x.  The captures that
 * are pure overhead are exactly a copy: a fresh temp written once, read once,
 * with its source untouched in between.  Removing those is plain copy
 * propagation, and the residual is ordinary R-WHILE, so it belongs here rather
 * than in the annotated-value domain. *)

let simp_prog_body (Prog (_, _, body, _)) = body

let cp s = show_program (Simp.copyprop_program (parse_program s))
let same s = show_program (parse_program s)

let test_copyprop_basic () =
  (* T is written once and consumed once, K untouched in between -> fuse *)
  Alcotest.(check string) "T <= K; X <= T  ==>  X <= K"
    (same "read K; X <= K; write X")
    (cp   "read K; T <= K; X <= T; write X")

let test_copyprop_into_cons_pattern () =
  Alcotest.(check string) "T <= K; cons A B <= T  ==>  cons A B <= K"
    (same "read K; cons A B <= K; X <= cons A B; write X")
    (cp   "read K; T <= K; cons A B <= T; X <= cons A B; write X")

let test_copyprop_blocked_source_rewritten () =
  (* K is written between the move and the use: the value would differ *)
  let src = "read K; T <= K; K <= Y; X <= T; Y <= K; write X" in
  Alcotest.(check string) "blocked when the source is rewritten in between"
    (same src) (cp src)

let test_copyprop_blocked_temp_read_twice () =
  let src = "read K; T <= K; X <= T; Y ^= X; write X" in
  Alcotest.(check bool) "temp read by an expression is not fused away"
    true
    (let out = cp "read K; T <= K; Y ^= T; X <= T; write X" in
     ignore src; out = same "read K; T <= K; Y ^= T; X <= T; write X")

let test_copyprop_preserves_semantics () =
  (* the property that actually matters: same answer, still invertible *)
  let src = "read K; T <= K; cons A B <= T; U <= B; X <= cons U A; write X" in
  let p = parse_program src in
  let p' = Simp.copyprop_program p in
  let d = VCons (atom "'a", atom "'b") in
  Alcotest.(check valT_testable) "copyprop preserves the answer"
    (EvalRwhile.evalProgram p d) (EvalRwhile.evalProgram p' d);
  let inv_of q = InvRwhile.invProgram q in
  Alcotest.(check valT_testable) "copyprop preserves the inverse's answer"
    (EvalRwhile.evalProgram (inv_of p) (EvalRwhile.evalProgram p d))
    (EvalRwhile.evalProgram (inv_of p') (EvalRwhile.evalProgram p' d))

(* EXTENSION 2026-08-08: fuse inside nested blocks too.  comp2 (the fp2 compiler)
 * keeps 363969 of its 400531 nodes INSIDE loop bodies, so a pass that only walks
 * the top-level spine cannot reach the part that matters.  The soundness argument
 * is unchanged: "t occurs exactly twice in the WHOLE program" already forces both
 * occurrences into the same block, and within one execution of that block the
 * per-iteration reasoning is the same as for straight-line code (t is consumed by
 * its use, so it is nil again when the block re-enters). *)
let test_copyprop_inside_conditional () =
  let src = "read K; if =? K nil then T <= K; X <= T else X <= K fi =? X nil; write X" in
  let out = cp src in
  Alcotest.(check bool) "the move inside the then-branch is fused away"
    true
    (let rec count_sub s sub i n =
       if i + String.length sub > String.length s then n
       else count_sub s sub (i + 1)
              (if String.sub s i (String.length sub) = sub then n + 1 else n) in
     count_sub out "<=" 0 0 < count_sub (same src) "<=" 0 0)

let test_copyprop_inside_loop_semantics () =
  (* a real loop body, checked by RUNNING it rather than by comparing text *)
  let src = "read K; X <= K; from =? Y nil do T <= X; X <= T; Y <= cons nil Y              loop Y <= cons nil Y until =? Y (nil.nil); cons Z Y <= Y;              Z ^= Z; W <= X; write W" in
  let p = parse_program src in
  let p' = Simp.copyprop_program p in
  let d = atom "'a" in
  Alcotest.(check valT_testable) "loop-body copyprop preserves the answer"
    (EvalRwhile.evalProgram p d) (EvalRwhile.evalProgram p' d)

let test_copyprop_is_identity_without_moves () =
  let src = "read K; X ^= K; K ^= X; write X" in
  Alcotest.(check string) "no single-use temp moves: unchanged"
    (same src) (cp src)

(* ===== -work: the cost -steps does not count =====
 * RWHILE_S.md has said since 2026-08-06 that `-steps` counts command nodes and
 * not the SIZE of the values touched, so "二次の仕事は =? の中に隠れる".  These
 * tests pin the meter that makes that visible, and then EXHIBIT the hidden
 * quadratic: a for-loop over a unary numeral is linear in steps and quadratic in
 * work.  Without the second test the meter would be untested where it matters. *)

let work_of_exp e =
  EvalRwhile.reset_work ();
  ignore (EvalRwhile.evalExp EvalRwhile.RIdentMap.empty e);
  EvalRwhile.get_work ()

let rec unary_val n = if n = 0 then VNil else VCons (VNil, unary_val (n - 1))
let rec unary_src n = if n = 0 then "nil" else "(nil . " ^ unary_src (n - 1) ^ ")"

let test_work_equal_values_cost_their_size () =
  (* comparing two equal values examines every node of both: 2*count_nodes - ...
   * precisely, one unit per node PAIR, so count_nodes of one side. *)
  List.iter (fun n ->
      let v = unary_val n in
      Alcotest.(check int) (Printf.sprintf "=? on equal unary %d" n)
        (EvalRwhile.count_nodes v)
        (work_of_exp (EEq (EVal v, EVal v))))
    [0; 1; 5; 20]

let test_work_mismatch_stops_early () =
  (* an early mismatch costs O(1), however big the values are -- the meter must
   * model short-circuiting, or it would just be count_nodes in disguise *)
  Alcotest.(check int) "atom vs cons: one unit"
    1 (work_of_exp (EEq (EVal (atom "'a"), EVal (unary_val 100))));
  Alcotest.(check bool) "a late mismatch costs more than an early one"
    true (work_of_exp (EEq (EVal (unary_val 100), EVal (VCons (unary_val 99, atom "'x"))))
          > work_of_exp (EEq (EVal (atom "'a"), EVal (unary_val 100))))

let test_work_charges_the_reversible_update () =
  (* `X ^= E` clears X by comparing its current value with E's -- the same hidden
   * comparison, and the one the for-counter's increment pays every iteration *)
  let p = parse_program "read X; Y ^= X; Y ^= X; write X" in
  let d = unary_val 30 in
  EvalRwhile.reset_work ();
  ignore (EvalRwhile.evalProgram p d);
  Alcotest.(check bool) "the clearing assignment is charged for the value's size"
    true (EvalRwhile.get_work () >= EvalRwhile.count_nodes d)

let test_work_exposes_the_hidden_quadratic () =
  (* THE point of the meter.  `for I = nil to N` tests `=? I N` every iteration
   * against a unary numeral, so the loop is linear in commands and quadratic in
   * nodes examined.  Doubling N must roughly double the steps and roughly
   * QUADRUPLE the work. *)
  let run n =
    let src = Printf.sprintf
      "read X; for I = nil to %s do Y ^= 'a; Y ^= 'a end; write X" (unary_src n) in
    let p = parse_program src in
    EvalRwhile.reset_steps (); EvalRwhile.reset_work ();
    ignore (EvalRwhile.evalProgram p VNil);
    (EvalRwhile.get_steps (), EvalRwhile.get_work ()) in
  let (s1, w1) = run 20 and (s2, w2) = run 40 in
  Alcotest.(check bool)
    (Printf.sprintf "steps grow linearly: %d -> %d (< 2.5x)" s1 s2)
    true (float_of_int s2 < 2.5 *. float_of_int s1);
  Alcotest.(check bool)
    (Printf.sprintf "work grows quadratically: %d -> %d (> 3x)" w1 w2)
    true (float_of_int w2 > 3.0 *. float_of_int w1)

let test_work_counter_resets () =
  EvalRwhile.reset_work ();
  Alcotest.(check int) "reset zeroes the meter" 0 (EvalRwhile.get_work ());
  ignore (work_of_exp (EEq (EVal (unary_val 3), EVal (unary_val 3))));
  EvalRwhile.reset_work ();
  Alcotest.(check int) "and again after use" 0 (EvalRwhile.get_work ())

(* ===== Encoding: where the nodes of a p2d-encoded program go =====
 * Motivation (2026-08-08).  comp2 cannot be shrunk by fusing moves (21 candidates
 * in 400531 nodes -- see the note at the end of Simp.ml), so the bulk is what the
 * commands CARRY, not how many there are.  Encoding.breakdown attributes every
 * node to one of eight categories.  These tests pin the two things that make the
 * attribution trustworthy: it ADDS UP (the categories total count_nodes exactly),
 * and each category is the size the encoding really charges, computed by hand
 * from Program2DataRwhile.transProgram. *)

let enc_breakdown src = Encoding.breakdown_program (parse_program src)

let test_encoding_adds_up () =
  (* Encoding.breakdown raises if the categories miss count_nodes, so simply
   * running it over a spread of shapes is the check.  Re-assert it here anyway,
   * so a failure names the property rather than the exception. *)
  List.iter (fun src ->
      let p = parse_program src in
      let r = Encoding.breakdown_program p in
      Alcotest.(check int) ("breakdown adds up: " ^ src)
        (EvalRwhile.count_nodes (Program2DataRwhile.program2data p))
        (Encoding.total r))
    [ "read X; Y <= X; write Y";
      "read X; Y ^= cons X X; X ^= Y; write Y";
      "read X; cons A B <= X; X <= cons B A; write X";
      "read X; if =? X nil then Y ^= 'a else Y ^= 'b fi =? Y nil; write Y";
      "read X; from =? Y nil do Y <= X loop Y <= X until =? Y nil; write Y";
      "read X; Y ^= (('a.'b).('c.nil)); X ^= Y; write X" ]

let test_encoding_var_cost_is_unary () =
  (* Variable index k costs 2k+1 nodes (k conses + k+1 nils), so the SAME program
   * with more variables ahead of the hot one costs strictly more.  This is the
   * term pass 1 (Optimize.var_order) minimises; the test pins that it is really
   * the unary numeral being charged, not a constant per occurrence. *)
  let r = enc_breakdown "read X; Y <= X; write Y" in
  (* Four occurrences (read X, the two pattern leaves, write Y) of two variables,
   * which get indices 0 and 1 whichever way the numbering breaks the tie.  Index
   * 0 costs 1 node, index 1 costs 3 -- twice each. *)
  Alcotest.(check int) "four variable occurrences" 4 r.Encoding.var_occs;
  Alcotest.(check int) "unary indices: 2*1 + 2*3" 8 r.Encoding.var_index;
  Alcotest.(check int) "header is 2 nodes each" 8 r.Encoding.var_header;
  Alcotest.(check int) "largest index is 1" 1 r.Encoding.max_index

let test_encoding_const_is_charged_to_const () =
  (* an embedded literal is charged to `const`, not to the structural categories *)
  let r = enc_breakdown "read X; Y ^= (('a.'b).('c.nil)); X ^= Y; write X" in
  (* ('a.'b).('c.nil) = 3 conses + 4 leaves = 7 nodes *)
  Alcotest.(check int) "one 'val occurrence" 1 r.Encoding.const_occs;
  Alcotest.(check int) "literal charged at its own size" 7 r.Encoding.const

let test_encoding_hot_numbering_shrinks_var_index () =
  (* The whole point of the attribution: pass 1 shows up as a smaller var_index
   * and nothing else moves much.  Compare hot-vars (default) with first-occurrence
   * numbering on a program where the hot variable is introduced late. *)
  let src = "read X; A ^= X; B ^= A; C ^= B; D ^= C;              D ^= D; D ^= C; C ^= B; B ^= A; A ^= X;              Y ^= X; write Y" in
  let p = parse_program src in
  let hot = Encoding.breakdown_program p in
  let old =
    let saved = !Program2DataRwhile.hot_vars in
    Program2DataRwhile.hot_vars := false;
    let r = Encoding.breakdown_program p in
    Program2DataRwhile.hot_vars := saved; r in
  Alcotest.(check bool) "hot-vars numbering costs no more in var_index"
    true (hot.Encoding.var_index <= old.Encoding.var_index);
  Alcotest.(check int) "the same variable occurrences either way"
    old.Encoding.var_occs hot.Encoding.var_occs;
  Alcotest.(check int) "renumbering does not change the structural nodes"
    (old.Encoding.com_struct + old.Encoding.exp_struct + old.Encoding.pat_struct)
    (hot.Encoding.com_struct + hot.Encoding.exp_struct + hot.Encoding.pat_struct)

let test_encoding_optimal_is_a_lower_bound () =
  (* optimal_var_index is a closed-form minimum over ALL renumberings, so no
   * actual numbering may beat it -- check both the default (pass 1) and
   * first-occurrence numbering on the same program. *)
  let src = "read X; A ^= X; B ^= A; C ^= B; D ^= C;              D ^= D; D ^= C; C ^= B; B ^= A; A ^= X;              Y ^= X; X ^= Y; Y ^= X; Y ^= X; write X" in
  let p = parse_program src in
  let check label r =
    Alcotest.(check bool) (label ^ ": optimal is a lower bound")
      true (Encoding.optimal_var_index r <= r.Encoding.var_index) in
  check "hot-vars" (Encoding.breakdown_program p);
  let saved = !Program2DataRwhile.hot_vars in
  Program2DataRwhile.hot_vars := false;
  check "first-occurrence" (Encoding.breakdown_program p);
  Program2DataRwhile.hot_vars := saved

let test_encoding_optimal_by_hand () =
  (* three variables occurring 4, 2 and 1 times cost 4*1 + 2*3 + 1*5 = 15 nodes
   * under the best numbering, whatever the actual one is *)
  let r = Encoding.empty () in
  Hashtbl.replace r.Encoding.idx_hist 0 1;
  Hashtbl.replace r.Encoding.idx_hist 1 4;
  Hashtbl.replace r.Encoding.idx_hist 2 2;
  Alcotest.(check int) "4*1 + 2*3 + 1*5" 15 (Encoding.optimal_var_index r)

let test_encoding_bits_nodes_by_hand () =
  (* the bit-list cost model, on indices whose bits are easy to read off:
   *   0        -> the empty list, 1 node
   *   1 = 1b   -> 1 + (1 + 3)                     = 5
   *   2 = 10b  -> 1 + (1 + 1) + (1 + 3)           = 7
   *   3 = 11b  -> 1 + (1 + 3) + (1 + 3)           = 9
   *   4 = 100b -> 1 + (1+1) + (1+1) + (1+3)       = 9 *)
  List.iter (fun (k, want) ->
      Alcotest.(check int) (Printf.sprintf "bits_nodes %d" k) want (Encoding.bits_nodes k))
    [ 0, 1; 1, 5; 2, 7; 3, 9; 4, 9 ];
  (* and it must beat the unary numeral exactly where the tail is: 2k+1 vs
   * O(log k).  At index 239 unary costs 479 nodes. *)
  Alcotest.(check bool) "bit-list is cheaper than unary at the tail"
    true (Encoding.bits_nodes 239 < 2 * 239 + 1)

let test_encoding_rejects_non_program () =
  Alcotest.check_raises "a non-program value is rejected, not silently counted"
    (Failure "Encoding: malformed program")
    (fun () -> ignore (Encoding.breakdown (atom "'nonsense")))

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

(* ===== The optimisations as a CLI pass, swept over the real examples =====
 * Simp.simpProgram and Simp.copyprop_program were written for residuals and are
 * exercised on hand-written fragments and on the fp1/fp2 residuals.  Exposing
 * them as `./ri -simp -copyprop` means they now run on programs nobody had them
 * in mind for -- macros, sugar, loops, the self-interpreters -- so the property
 * that matters is swept over the examples the suite already runs: the optimised
 * program must give the SAME answer, and must still be invertible.
 *
 * `-copyprop` expands macros first (Main.ml does the same), because the
 * whole-program "occurs exactly twice" gate cannot see through a macro call. *)

let opt_expand p = MacroRwhile.expMacProgram p
let opt_simp p = Simp.simpProgram (opt_expand p)
let opt_full p = Simp.copyprop_program (Simp.simpProgram (opt_expand p))

(* (program file, data file) pairs -- the ones the file-integration group runs,
 * plus the sugar and case examples, which exercise the desugaring paths. *)
let opt_examples =
  [ "rep.rwhile", "list123.val";
    "length.rwhile", "list123.val";
    "minus.rwhile", "minus.val";
    "compare.rwhile", "compare0.val";
    "rle.rwhile", "rle2.val";
    "reverse.rwhile", "list123.val";
    "case_swap.rwhile", "list123.val";
    "case_tag.rwhile", "case_tag.val";
    "stack_reverse.rwhile", "list123.val";
    "lookup.rwhile", "nil.val" ]

let test_opt_preserves_answers () =
  List.iter (fun (pf, df) ->
      let p = parse_file_program (examples_dir ^ "/" ^ pf) in
      let d = parse_file_val (examples_dir ^ "/" ^ df) in
      let base = EvalRwhile.evalProgram p d in
      Alcotest.(check valT_testable) ("-simp preserves the answer: " ^ pf)
        base (EvalRwhile.evalProgram (opt_simp p) d);
      Alcotest.(check valT_testable) ("-simp -copyprop preserves the answer: " ^ pf)
        base (EvalRwhile.evalProgram (opt_full p) d))
    opt_examples

let test_opt_preserves_invertibility () =
  (* the reversible-language half: the optimised program's syntactic inverse
   * still undoes it.  A transformation can preserve the forward answer and
   * still break this -- copy propagation moves where a value is consumed. *)
  List.iter (fun (pf, df) ->
      let p = parse_file_program (examples_dir ^ "/" ^ pf) in
      let d = parse_file_val (examples_dir ^ "/" ^ df) in
      let q = opt_full p in
      let out = EvalRwhile.evalProgram q d in
      Alcotest.(check valT_testable) ("inverse round-trips: " ^ pf)
        d (EvalRwhile.evalProgram (InvRwhile.invProgram q) out))
    opt_examples

let test_opt_preserves_cost_or_improves () =
  (* the optimisations must never make a program cost MORE steps: they only
   * delete commands (dead branches, fused moves) *)
  List.iter (fun (pf, df) ->
      let p = parse_file_program (examples_dir ^ "/" ^ pf) in
      let d = parse_file_val (examples_dir ^ "/" ^ df) in
      EvalRwhile.reset_steps ();
      ignore (EvalRwhile.evalProgram (opt_expand p) d);
      let base = EvalRwhile.get_steps () in
      EvalRwhile.reset_steps ();
      ignore (EvalRwhile.evalProgram (opt_full p) d);
      let opt = EvalRwhile.get_steps () in
      Alcotest.(check bool)
        (Printf.sprintf "%s: %d steps -> %d, never worse" pf base opt)
        true (opt <= base))
    opt_examples

let test_opt_is_identity_on_a_clean_program () =
  (* nothing to fold and no single-use temp moves: the pass must be the identity,
   * so `-simp -copyprop` is safe to leave on *)
  let src = "read X; Y ^= X; X ^= Y; write Y" in
  Alcotest.(check string) "no opportunities: unchanged"
    (show_program (parse_program src))
    (show_program (Simp.copyprop_program (Simp.simpProgram (parse_program src))))


let test_file_rep () =
  let prog = parse_file_program (examples_dir ^ "/rep.rwhile") in
  let data = parse_file_val (examples_dir ^ "/list123.val") in
  let result = EvalRwhile.evalProgram prog data in
  let expected = parse_file_val (examples_dir ^ "/list123.val") in
  Alcotest.(check valT_testable) "rep.rwhile" expected result

(* COLLECT-REFS (案1-B selective-dynamicize helper) is reversible: running it
   forward then INV on a full command tree preserves the tree (out == in) with no
   assertion error.  This locks in the grammar-directed case+begin/end-marker
   COLLECT-REFS proven via the examples/test_collect_refs.rwhile harness. *)
let test_collect_refs_roundtrip () =
  let prog = parse_file_program (examples_dir ^ "/test_collect_refs.rwhile") in
  let tree = parse_val
    ("('seq . (('ass . (('var . nil) . ('hd . ('var . (nil . nil))))) . "
     ^ "('cond . (('eq . (('var . nil) . ('val . 'swap))) . "
     ^ "(('rep . (('var . nil) . ('var . (nil . nil)))) . "
     ^ "(('loop . (('var . (nil . nil)) . (('rep . (('var . nil) . ('val . nil))) . "
     ^ "(('ass . (('var . (nil . nil)) . ('val . nil))) . (('var . nil) . nil))))) . "
     ^ "(('val . nil) . nil)))))))") in
  let out = EvalRwhile.evalProgram prog tree in
  Alcotest.(check valT_testable) "COLLECT-REFS forward->INV preserves tree" tree out

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
  (* inv(inv(p)) = p should hold -- but inversion is defined on CORE R-WHILE, and
     invProgram desugars first (ri.rwhile uses `case`), so the fixed point of the
     involution is the desugared program, not the raw parse tree. *)
  let inv2 = InvRwhile.invProgram inv in
  Alcotest.(check program_testable) "ri.rwhile inv involution"
    (Desugar.desugar_program prog) inv2

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

(* ri.rwhile now decodes 'pairp: self-interpreting a program that uses pair?
 * must match direct evaluation (and stay reversible via the H history stack). *)
let test_ri_self_interp_pairp () =
  let prog = parse_program
    "read X; cons A B <= X; P1 ^= pair? A; X <= cons P1 (cons A B); write X" in
  let prog_data = Program2DataRwhile.program2data prog in
  let input = parse_val "(('x . 'y) . 'z)" in
  let direct = EvalRwhile.evalProgram prog input in
  Alcotest.(check valT_testable) "ri self-interp pair? = direct" direct
    (run_via_ri prog_data input)

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

(* RETIRED (2026-07-06): the old first-Futamura-projection tests
 * (check_first_projection / test_fp1_id / test_fp1_swap / test_fp1_reverse) used
 * the DEPRECATED array-based spec.rwhile and ran the residual through `run_via_ri`,
 * which is unfaithful on the residual's self-clears (the documented ri.rwhile bug2:
 * ri.rwhile cannot reverse-interpret X^=X).  They failed for that reason, not a real
 * fp1 defect.  fp1 for the CURRENT specialiser spec_av is covered, all green, by the
 * `first-projection-min` group (which judges by DIRECT eval, not run_via_ri). *)

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

(* R-WHILE truth convention: nil=false, ANY non-nil=true. A conditional/loop test
   need not be the boolean (nil.nil). `if Y fi Y` and `from Y until Y` are the
   identity for any non-nil Y (the self-interpreter ri.rwhile relies on this:
   it dispatches with `if W ... fi W` on the raw test value). *)
let test_nonnil_truth_cond_atom () =
  Alcotest.(check valT_testable) "if Y fi Y on 'a = 'a"
    (atom "'a") (eval_string "read Y; if Y fi Y; write Y" "'a")

let test_nonnil_truth_cond_cons () =
  Alcotest.(check valT_testable) "if Y fi Y on ('x.'y) = ('x.'y)"
    (pair (atom "'x") (atom "'y"))
    (eval_string "read Y; if Y fi Y; write Y" "('x.'y)")

let test_nonnil_truth_loop_atom () =
  Alcotest.(check valT_testable) "from Y until Y on 'a = 'a"
    (atom "'a") (eval_string "read Y; from Y until Y; write Y" "'a")

(* New: plain mode is unchanged (no structured wrapper). *)
let test_plain_error_unchanged () =
  Alcotest.check_raises "plain hd nil message unchanged"
    (Failure "No head. Expression hd nil has value nil")
    (fun () -> ignore (eval_string "read X; Y ^= hd nil; write X" "'a"))

(* ===== Hygienic macro expansion (-hygienic-macros, opt-in) =====
 * INNER uses a local Tmp; the caller also uses a local Tmp. Without hygiene the
 * two collide and the value is corrupted (store-not-cleared); with hygiene they
 * are alpha-renamed apart and the copy round-trips correctly. *)
(* The colliding scratch Tmp is purely macro-internal (it must NOT appear in the
   top-level body, or the globals policy would treat it as a shared global and
   leave it un-renamed). INNER and OUTER both use a local Tmp; without hygiene
   the two collide and corrupt the value. *)
let hygiene_collision_prog =
  "macro INNER(A, R) Tmp ^= A; R ^= Tmp; Tmp ^= A " ^
  "macro OUTER(P, Q) Tmp ^= P; INNER(Tmp, Q); Tmp ^= P " ^
  "read In; OUTER(In, Out); In ^= Out; write Out"

(* Run f with the hygiene flag forced to a given value, restoring the previous
   value afterwards (so these tests behave correctly whether or not the suite is
   run with RWHILE_HYGIENIC=1). *)
let with_flag value f =
  let prev = !MacroRwhile.hygienic in
  MacroRwhile.hygienic := value;
  Fun.protect ~finally:(fun () -> MacroRwhile.hygienic := prev) f
let with_hygiene f = with_flag true f

(* With the flag ON the local collision is resolved and Out = In. *)
let test_hygienic_fixes_collision () =
  let result = with_hygiene (fun () ->
    EvalRwhile.evalProgram (parse_program hygiene_collision_prog) (atom "'a")) in
  Alcotest.(check valT_testable) "hygienic copy round-trips" (atom "'a") result

(* With the flag OFF the same program corrupts the store and aborts. *)
let test_nonhygienic_collision_aborts () =
  Alcotest.(check bool) "non-hygienic collision raises" true
    (with_flag false (fun () ->
       try ignore (EvalRwhile.evalProgram
                     (parse_program hygiene_collision_prog) (atom "'a")); false
       with Failure _ -> true))

(* A generated fresh name must not alias an existing program variable. Here the
   user variable Tmp-1 matches the "<base>-<n>" pattern the generator produces;
   the macro local Tmp must be renamed to something OTHER than Tmp-1, so CP's
   private scratch does not stomp the live user variable. *)
let hygiene_dashed_collision_prog =
  "macro CP(A,B) Tmp ^= A; B ^= Tmp; Tmp ^= A " ^
  "read In; Tmp-1 ^= In; CP(Tmp-1, Out); Tmp-1 ^= In; In ^= Out; write Out"

let test_hygiene_avoids_dashed_var_collision () =
  let r = with_hygiene (fun () ->
    EvalRwhile.evalProgram (parse_program hygiene_dashed_collision_prog) (atom "'a")) in
  Alcotest.(check valT_testable) "fresh name avoids user Tmp-1; CP copies correctly"
    (atom "'a") r

(* The flag actually rewrites local identifiers: expansion introduces "Tmp-"
   renamed locals when ON, and leaves the bare "Tmp" alone when OFF. *)
let test_hygienic_renames_in_expansion () =
  let expand () =
    show_program (MacroRwhile.expMacProgram (parse_program hygiene_collision_prog)) in
  let off = with_flag false expand in
  let on = with_flag true expand in
  Alcotest.(check bool) "OFF keeps bare Tmp"   true (find_substring off "Tmp-" = None);
  Alcotest.(check bool) "ON renames to Tmp-N"  true (find_substring on  "Tmp-" <> None)

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
(* AV-LIFT must PRESERVE its input AV (the comment in spec_av.rwhile promises
   "AsAV preserved").  ASSEMBLE-FP1 relies on this: it does
     LOOKUP(Vl,J',AsAV); AV-LIFT(AsAV,AsCode); LOOKUP(Vl,J',AsAV)
   where the second LOOKUP only clears AsAV (XOR same value -> nil) if AV-LIFT
   left AsAV exactly as the first LOOKUP set it.  Drift here is the root cause of
   the fp2 '10 (the OUTER specializer's abstract slot for AsAV ends up holding
   AV-LIFT internals (LfTag.LfPay) instead of the original slot value; see
   plan_fp1_stage_c.md 6.3.2).  This guards the concrete preservation property
   the fix must keep. *)
let check_av_lift_preserves name av_str =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read A; AV-LIFT(A, Code); Out <= cons A Code; write Out" in
  let av = parse_val av_str in
  let result = EvalRwhile.evalProgram prog av in
  (* result = (A_after . Code); A_after must equal the input AV *)
  let a_after = match result with VCons (a, _) -> a | _ -> result in
  Alcotest.(check valT_testable) name av a_after

let test_av_lift_preserves_static () =
  check_av_lift_preserves "lift preserves static input" "('S . 'a)"
let test_av_lift_preserves_dynamic () =
  check_av_lift_preserves "lift preserves dynamic input" "('D . ('var . nil))"
let test_av_lift_preserves_partial () =
  check_av_lift_preserves "lift preserves partial-static input"
    "('C . (('S . 'a) . ('D . ('var . nil))))"
let test_av_lift_preserves_nested () =
  check_av_lift_preserves "lift preserves nested partial-static input"
    "('C . (('S . 'a) . ('C . (('S . 'b) . ('D . ('var . nil))))))"

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
let test_av_uncons_partial () =
  (* split a partially-static cons into static car + dynamic cdr (the input split) *)
  check_av "uncons partial-static"
    "('uncons . ('C . (('S . 'a) . ('D . ('var . nil)))))"
    "(('S . 'a) . ('D . ('var . nil)))"
let test_av_uncons_static () =
  check_av "uncons static cons"
    "('uncons . ('S . ('a . 'b)))" "(('S . 'a) . ('S . 'b))"
let test_av_uncons_dynamic () =
  check_av "uncons dynamic (symbolic hd/tl)"
    "('uncons . ('D . ('var . nil)))"
    "(('D . ('hd . ('var . nil))) . ('D . ('tl . ('var . nil))))"
let test_av_uncons_static_noncons () =
  (* SAFETY: splitting a static non-cons (atom/nil) is a static pattern-match
   * failure (dead position during PE); produce a degenerate ('S.nil) split
   * instead of crashing on `cons H Tl <= nil`. *)
  check_av "uncons static non-cons -> degenerate"
    "('uncons . ('S . nil))" "(('S . nil) . ('S . nil))"

(* MKAV: the binding-time-aware partial-input builder (the fp2 fix; mirrors
 * RWhileRevProj2BT.agda `mkAV`).  Harness input = (BT . (Src . Ic)).
 *   BT='S -> ('C.(('S.Src).('D.('var.Ic))))  (fp1 partial-static, as before)
 *   BT='D -> ('D.('var.Ic))                  (whole input dynamic; Src dropped) *)
let check_mkav name in_str expected_str =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; cons BT Rest <= In; cons Src Ic <= Rest; MKAV(BT, Src, Ic, Out); write Out" in
  let result = EvalRwhile.evalProgram prog (parse_val in_str) in
  Alcotest.(check valT_testable) name (parse_val expected_str) result

let test_mkav_static () =
  check_mkav "MKAV 'S -> partial-static cons AV (= the old unconditional build)"
    "('S . ('a . nil))" "('C . (('S . 'a) . ('D . ('var . nil))))"
let test_mkav_static_idx1 () =
  check_mkav "MKAV 'S keeps the residual var index"
    "('S . ('a . (nil . nil)))" "('C . (('S . 'a) . ('D . ('var . (nil . nil)))))"
let test_mkav_dynamic () =
  check_mkav "MKAV 'D -> fully-dynamic AV (Src dropped)"
    "('D . ('a . nil))" "('D . ('var . nil))"

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
  (* Use an explicit SPEC-EXP-AV harness (spec_av's default main is now fp1). *)
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; cons Vl E <= In; SPEC-EXP-AV(E, RE); Out <= cons Vl (cons E RE); write Out" in
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
let test_se_av_pairp_static_atom () =
  (* pair? of a static atom (slot0 = ('S.'a)) is statically FALSE *)
  check_spec_exp_av "pair? static atom -> static false"
    "('pairp . ('var . nil))" "('S . nil)"
let test_se_av_pairp_static_cons () =
  (* pair? of a static cons literal is statically TRUE *)
  check_spec_exp_av "pair? static cons -> static true"
    "('pairp . ('val . ('a . 'b)))" "('S . (nil . nil))"
let test_se_av_pairp_partial () =
  (* pair? of a partially-static cons is statically TRUE (it IS a cons) *)
  check_spec_exp_av "pair? partial-static cons -> static true"
    "('pairp . ('cons . (('var . nil) . ('var . (nil . nil)))))" "('S . (nil . nil))"
let test_se_av_pairp_dynamic () =
  (* pair? of a dynamic var (slot1) stays dynamic: residual pair? *)
  check_spec_exp_av "pair? dynamic -> residual pair?"
    "('pairp . ('var . (nil . nil)))" "('D . ('pairp . ('var . (nil . nil))))"

(* ===== AV-based SPEC-STEP (Stage B step 3: 'seq, 'ass, 'rep, 'cond) =====
 * Harness: input (Vl . Cmd), output (Vl' . RCode) (residual, reverse order). *)
let check_spec_step_av name vl_str cmd_str expected_str =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; cons Vl Cmd <= In; SPEC-CMD-AV(Cmd); Out <= cons Vl RCode; write Out" in
  let out = EvalRwhile.evalProgram prog (pair (parse_val vl_str) (parse_val cmd_str)) in
  Alcotest.(check valT_testable) name (parse_val expected_str) out

(* Decode a unary nil-list index to an int; -1 if not a unary index. *)
let rec unary_to_int = function
  | VNil -> 0
  | VCons (VNil, rest) -> (match unary_to_int rest with -1 -> -1 | n -> n + 1)
  | _ -> -1

(* Pretty-print a p2d command/expr with decoded var indices. *)
let rec pp_cmd v =
  let open Printf in
  match v with
  | VCons (VAtom (Atom "'seq"), VCons (c, d)) -> sprintf "%s; %s" (pp_cmd c) (pp_cmd d)
  | VCons (VAtom (Atom "'ass"), VCons (lhs, e)) -> sprintf "%s ^= %s" (pp_cmd lhs) (pp_cmd e)
  | VCons (VAtom (Atom "'rep"), VCons (p, r)) -> sprintf "%s <= %s" (pp_cmd p) (pp_cmd r)
  | VCons (VAtom (Atom "'cons"), VCons (a, b)) -> sprintf "cons(%s, %s)" (pp_cmd a) (pp_cmd b)
  | VCons (VAtom (Atom "'var"), k) -> sprintf "V%d" (unary_to_int k)
  | VCons (VAtom (Atom "'val"), x) -> sprintf "{%s}" (show_val x)
  | VCons (VAtom (Atom "'hd"), x) -> sprintf "hd(%s)" (pp_cmd x)
  | VCons (VAtom (Atom "'tl"), x) -> sprintf "tl(%s)" (pp_cmd x)
  | VCons (VAtom (Atom "'cond"), rest) -> sprintf "cond(%s)" (show_val rest)
  | VCons (VAtom (Atom "'loop"), rest) -> sprintf "loop(%s)" (show_val rest)
  | other -> show_val other

(* DIAGNOSTIC: run fp1 main up to (not incl.) ASSEMBLE, dump the abstract store
 * V[FpJ] (ri_fp3's output var) to decide STEP-bug vs lift-bug. *)
let unary_lit n =
  let rec go n = if n = 0 then "nil" else "(nil." ^ go (n - 1) ^ ")" in go n

let rec nth_slot vl k = match vl, k with
  | VCons (s, _), 0 -> s
  | VCons (_, rest), n -> nth_slot rest (n - 1)
  | _ -> VNil

(* Run fp1 main up to (not incl.) ASSEMBLE; return the abstract store slot
 * V[FpJ] (ri_fp3's output var) after the STEP loop. *)
let fp1_store_out_slot src_name =
  let n = unary_lit 50 in
  let body =
    "read In; cons Prog Src <= In;" ^
    "cons FpPR FpPT <= Prog; cons FpVI FpI <= FpPR; FpVI ^= 'var;" ^
    "cons FpBody FpPW <= FpPT; cons FpVJ FpJ <= FpPW; FpVJ ^= 'var;" ^
    "FpN ^= " ^ n ^ "; AV-INIT(FpN, Vl); FpN ^= " ^ n ^ ";" ^
    "LOOKUP(Vl, FpI, FpOld); UPDATE(Vl, FpI, FpOld); FpOld ^= FpOld;" ^
    "FpIc ^= FpI; FpPart <= cons 'C (cons (cons 'S Src) (cons 'D (cons 'var FpIc)));" ^
    "UPDATE(Vl, FpI, FpPart); FpPart ^= FpPart;" ^
    "SPEC-CMD-AV(FpBody);" ^
    "FpIc2 ^= FpI; Out <= cons Vl (cons FpJ (cons FpIc2 RCode)); FpI ^= FpI; write Out" in
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile") body in
  let ri_fp3 = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/ri_fp3.rwhile")) in
  let src = parse_file_program (examples_dir ^ "/" ^ src_name ^ ".rwhile") in
  let src_data = Program2DataRwhile.program2data src in
  match EvalRwhile.evalProgram prog (pair ri_fp3 src_data) with
  | VCons (vl, VCons (fpj, _)) -> nth_slot vl (unary_to_int fpj)
  | _ -> VNil

(* WAS A KNOWN BUG, FIXED 2026-08-08.  The bug was in STEP, not in lift/assemble:
 * after STEP, the output slot V[FpJ] for swap was a partial-static cons whose
 * Result half (tl) was a PLAIN opaque dynamic ('D.('var.N)) -- NOT the swapped
 * structure ('C.((D tl).(D hd))).  ri_fp3's stack machine let the dynamic value
 * flow through opaquely, so the hd/tl/cons were never tracked symbolically.
 *
 * Giving EVAL-PAT-STEP-FP3 a second working register (so the two leaves of a
 * flat cons no longer share one slot, hence no stale AV) and moving values
 * through PAT-MOVE-FP3 replacements rather than XOR pairs (so a compound AV is
 * consumed, not lifted into an expression) makes STEP track the structure: the
 * Result half is now a structural 'C cons.  Assert that. *)
let test_fp1_step_structural_result () =
  let slot = fp1_store_out_slot "swap" in
  let result = (match slot with VCons (_, VCons (_, tl)) -> tl | _ -> slot) in
  (* Assert the SHAPE, not the variable numbers: pinning the numerals would make
     this test track Optimize's numbering instead of the property (it did once:
     the old opaque result moved from index 0 to 36 when access-weight numbering
     became the default). *)
  Alcotest.(check bool)
    "STEP now tracks swap's Result as a structural cons ('C.(_._))"
    true
    (match result with
     | VCons (VAtom (Atom "'C"), VCons (_, _)) -> true
     | _ -> false)

(* ROOT-CAUSE test: PAT-WRITE-STRUCT must handle a NESTED cons pattern.
 * `cons (cons V1e V2e) St <= var0` with var0 = ('C.((D var0).(S nil))) (a
 * one-element "stack" whose top is dynamic). The inner pattern (cons V1e V2e)
 * receives the dynamic top (D var0) and must split it (residualize), leaving
 * V1e,V2e dynamic. The BUG: PAT-WRITE-STRUCT delegates sub-patterns to
 * PAT-WRITE-LEAF-REHOME, which only handles var leaves and DISCARDS the value
 * for a cons sub-pattern -> V1e,V2e stay ('S.nil) and the split is lost. *)
let test_pat_write_nested_split () =
  (* indices: var0=0 (value), V1e=1, V2e=2, St=3 *)
  let store =
    "(('C . (('D . ('var . nil)) . ('S . nil))) . (('S . nil) . (('S . nil) . (('S . nil) . nil))))" in
  let cmd =
    "('rep . (('cons . (('cons . (('var . (nil . nil)) . ('var . (nil . (nil . nil))))) . " ^
    "('var . (nil . (nil . (nil . nil)))))) . ('var . nil)))" in
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; cons Vl Cmd <= In; SPEC-CMD-AV(Cmd); Out <= cons Vl RCode; write Out" in
  let out = EvalRwhile.evalProgram prog (pair (parse_val store) (parse_val cmd)) in
  (* FIXED 2026-08-07 by wiring PAT-WRITE-ITER into the 'rep path: the nested
   * cons sub-pattern's dynamic value is no longer discarded.  V1e and V2e become
   * dynamic references to themselves and the split is residualized -- exactly
   * what the old KNOWN-BUG comment said should happen once PAT-WRITE handled
   * nested patterns. *)
  match out with
  | VCons (vl, rcode) ->
     Alcotest.(check (list valT_testable))
       "nested split: V1e,V2e go dynamic and the split is residualized"
       [parse_val "('D . ('var . (nil . nil)))";
        parse_val "('D . ('var . (nil . (nil . nil))))";
        parse_val ("(('rep . (('cons . (('var . (nil . nil)) . "
                   ^ "('var . (nil . (nil . nil))))) . ('var . nil))) . nil)")]
       [nth_slot vl 1; nth_slot vl 2; rcode]
  | _ -> Alcotest.fail "unexpected output shape"

(* fp1 via ri_fp3: residual body of a source program (the "compiled" code).
 * Returns (residual_body_pretty, comp). *)
let fp1_ri_fp3_body src_name =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_fp3 = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/ri_fp3.rwhile")) in
  let src = parse_file_program (examples_dir ^ "/" ^ src_name ^ ".rwhile") in
  let src_data = Program2DataRwhile.program2data src in
  let comp = EvalRwhile.evalProgram spec_av (spec_in ri_fp3 src_data) in
  match comp with
  | VCons (_, VCons (body, _)) -> pp_cmd body
  | _ -> "unexpected comp shape"

(* CHARACTERIZATION of the open fp1-via-ri_fp3 specialization bug (candidate B).
 * `swap` and `sx_splitjoin` (uncons-then-rejoin = identity) differ only by the
 * order of the rebuilt cons, yet their fp1-via-ri_fp3 residual BODIES are
 * currently BYTE-IDENTICAL: spec_av folds ri_fp3's stack-based EVAL-PAT /
 * INV-EVAL-PAT away, so the dynamic structural ops (hd/tl/cons) vanish and the
 * residual is pure data-routing -- swap is not actually performed.  Direct
 * specialization (test_fp1_main_swap) is correct, so the bug is specific to
 * ri_fp3's stack-machine indirection.  When the bug is fixed this test SHOULD
 * fail (bodies must then differ); update it to assert the correct residuals.
 *
 * STATUS 2026-08-06: wiring PAT-WRITE-ITER into the 'rep path DOES fix this --
 * the two bodies become different (1597 nodes each, distinct) instead of
 * byte-identical (763 nodes, same).  It is not wired because fp1 for ri_seq
 * then produces a residual that fails with `error in update: var=Elem cur='a
 * new='b`.  The blocker recorded in spec_av.rwhile until today -- that wiring
 * it makes full-ri_fp3 fp1 diverge -- was re-measured and does NOT happen. *)
let test_fp1_ri_fp3_known_bug () =
  (* PARTLY FIXED 2026-08-07.  `swap` and `sx_splitjoin` differ only by the order
     of the rebuilt cons, and their fp1-via-ri_fp3 residual bodies now differ too
     -- the dynamic structural ops survive.  They used to be BYTE-IDENTICAL,
     which meant spec_av had folded ri_fp3's stack-based EVAL-PAT away and swap
     was not actually performed. *)
  Alcotest.(check bool)
    "swap and splitjoin residual bodies now differ (structural ops preserved)"
    true
    (fp1_ri_fp3_body "sx_splitjoin" <> fp1_ri_fp3_body "swap")

(* ...BUT THE RESIDUAL STILL DOES NOT RUN.  Preserving the structural ops is not
 * the whole bug.  Traced 2026-08-07 on the swap residual:
 *
 *     4 ^= 15;  15 ^= 4;      -- stage 15's value ('b) through working slot 4
 *     4 ^= 16;  16 ^= 4;      -- stage 16's value ('a) through 4 ... which still
 *                             --   holds 'b  ->  error in update: var=4
 *     6 <= 4;   5 <= 4;       -- and 4 is then consumed twice as well
 *
 * Two rehomes stage through the SAME working slot without it being freed in
 * between.  Same family as the transposition bug fixed in PAT-WRITE-ITER (a
 * move emitted without checking the target is available), but at the level of
 * residual sequencing rather than of one cons split.  This test pins the
 * remaining failure so "structural ops preserved" is not mistaken for "fp1 via
 * ri_fp3 works".
 *
 * Reordering the emitted fragment DOES make it compute swap --
 *   V4^=V15; V15^=V4; V5<=V4; V4^=V16; V16^=V4; V6<=V4   ->  ('b . 'a)
 * -- but that is not the whole story, and the "scheduling, not content" reading
 * first recorded here was too optimistic.  Program order turns out to equal
 * emission order (MAKE-SEQ undoes the prepend-accumulation), and the real defect
 * is that the pattern write holds TWO AVs referencing the SAME dynamic slot: a
 * reversible language cannot consume one slot twice, so no ordering repairs it.
 * The fix must capture at READ time into a per-read temp, which needs a temp
 * allocator inside spec_av.  See the note in examples/spec_av.rwhile. *)
(* NEW CAPABILITY, measured 2026-08-07 against 128802a~1 (before PAT-WRITE-ITER
 * was wired).  fp1 via ri_fp3 now produces residuals that RUN and agree with
 * direct evaluation, for every source that does not transpose:
 *
 *     source   before the fix                     after
 *     id       ran, but from a degenerate body    real body, correct
 *     id2      FAIL Pattern write conflict        correct
 *     id3      FAIL Pattern write conflict        correct
 *     rep      FAIL Pattern write conflict        correct
 *     swap     ran and SILENTLY RETURNED ('a.'b)  fails loudly
 *              -- the input unchanged, when swap
 *              must give ('b.'a)
 *
 * So the old "structural ops lost" bug was not merely cosmetic: the residual
 * computed the WRONG ANSWER and said nothing.  It is now either right or loud. *)
let test_fp1_ri_fp3_nontransposing_ok () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_fp3 = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_fp3.rwhile")) in
  let d = VCons (atom "'a", atom "'b") in
  let check name =
    let srcp = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
    let comp = EvalRwhile.evalProgram spec_av
        (spec_in ri_fp3 (Program2DataRwhile.program2data srcp)) in
    let got = (match EvalRwhile.evalProgram
                       (Program2DataRwhile.data2program comp) d with
               | VCons (_, res) -> res | v -> v) in
    Alcotest.(check valT_testable)
      (name ^ ": fp1-via-ri_fp3 residual runs and agrees with direct evaluation")
      (EvalRwhile.evalProgram srcp d) got in
  check "id2"; check "id3"; check "rep"

(* FIXED 2026-08-08 by giving ri_fp3's pattern stack machine a SECOND working
 * register, selected by the stack depth at which the value is pushed (`Dp`).
 * The two leaves of a flat `cons` pattern are pushed at different depths, so
 * they stage through different slots and neither AV goes stale.  Note the
 * trigger was never transposition: `sx_splitjoin` (uncons-then-rejoin = the
 * identity) failed too.  It is TWO LEAVES IN ONE BUILT PATTERN. *)
let test_fp1_ri_fp3_two_leaf_patterns_run () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_fp3 = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_fp3.rwhile")) in
  let d = VCons (atom "'a", atom "'b") in
  let check name =
    let srcp = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
    let comp = EvalRwhile.evalProgram spec_av
        (spec_in ri_fp3 (Program2DataRwhile.program2data srcp)) in
    let got = (match EvalRwhile.evalProgram
                       (Program2DataRwhile.data2program comp) d with
               | VCons (_, res) -> res | v -> v) in
    Alcotest.(check valT_testable)
      (name ^ ": fp1-via-ri_fp3 residual runs and agrees with direct evaluation")
      (EvalRwhile.evalProgram srcp d) got in
  check "swap"; check "sx_splitjoin"

(* ri_fp3 IS AN INTERPRETER FIRST.  Every other ri_fp3 test runs it only through
 * spec_av, so a change to it could pass them all while breaking the thing it is
 * for.  This pins direct self-interpretation, including a program with a loop
 * (`reverse`), which is what actually exercises STEP-FP3's control flow. *)
let test_ri_fp3_self_interprets () =
  let interp = parse_file_program (examples_dir ^ "/ri_fp3.rwhile") in
  let check name d =
    let srcp = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
    let src = Program2DataRwhile.program2data srcp in
    let got = (match EvalRwhile.evalProgram interp (VCons (src, d)) with
               | VCons (_, res) -> res | v -> v) in
    Alcotest.(check valT_testable)
      (name ^ ": [ri_fp3](p2d(p), d) agrees with [p](d)")
      (EvalRwhile.evalProgram srcp d) got in
  let ab = VCons (atom "'a", atom "'b") in
  let ab_nil = VCons (atom "'a", VCons (atom "'b", VNil)) in
  let abc = VCons (atom "'a", VCons (atom "'b", VCons (atom "'c", VNil))) in
  check "id" ab; check "id2" ab; check "rep" ab;
  check "swap" ab; check "sx_splitjoin" ab; check "sx_three" ab_nil;
  check "reverse" abc

(* THE BOUND OF THE 2026-08-08 FIX (open).  Two working registers separate the
 * two leaves of a FLAT cons pattern.  With a NESTED one (`cons V1 (cons V2 nil)`,
 * examples/sx_three.rwhile) ri_fp3's 'consE step routes every split through the
 * same two slots V1e/V2e, so the compound AV built at one nesting level goes
 * stale when the next level reuses those slots.  The residual comes out
 * NON-LINEAR (`cons 5 (cons 5 nil)` -- the interpreter even warns) and then
 * fails with a pattern write conflict.  This is a SECOND, independent sharing,
 * of the same kind the leaf-register fix removed.
 *
 * ri_fp3 interprets sx_three correctly (see the test above); only the fp1
 * residual is broken.  Keep sx_three to THREE variables: ri_fp3 dispatches over
 * exactly V0/V1/V2, so a four-variable subject would fail for that unrelated
 * reason and this test would pin nothing.
 * If this test fails, the bound has moved: check what now works and re-pin. *)
let test_fp1_ri_fp3_nested_pattern_runs () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_fp3 = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_fp3.rwhile")) in
  let srcp = parse_file_program (examples_dir ^ "/sx_three.rwhile") in
  let comp = EvalRwhile.evalProgram spec_av
      (spec_in ri_fp3 (Program2DataRwhile.program2data srcp)) in
  let d = VCons (atom "'a", VCons (atom "'b", VNil)) in
  Alcotest.(check valT_testable)
    "sx_three: a NESTED pattern's fp1-via-ri_fp3 residual runs correctly"
    (EvalRwhile.evalProgram srcp d)
    (match EvalRwhile.evalProgram (Program2DataRwhile.data2program comp) d with
     | VCons (_, res) -> res | v -> v)

(* ===== JONES OPTIMALITY, measured with the SELF-interpreter (2026-08-09) =====
 *
 * Jones's criterion (Jones 1988; JGS ch.6) is NOT "the residual beats the
 * interpreter" -- that is only the specialisation gain, which any specialiser
 * that unfolds a dispatch achieves.  It is:
 *
 *     spec is Jones-optimal  iff  [spec](sint, p)  is at least as good as p
 *
 * for a SELF-interpreter sint, i.e. specialising sint to p removes the whole
 * interpretive layer rather than part of it.  It could not be evaluated on this
 * artifact before, because ri_min/ri_seq/ri_perm interpret op-languages that are
 * not R-WHILE, so "run p directly" is not defined for their sources.
 * `ri_fp3.rwhile` IS an R-WHILE self-interpreter, and since 2026-08-08 its fp1
 * residuals run correctly, so the criterion can now be measured.
 *
 * THE REVERSIBLE FORM OF THE CRITERION.  A reversible projection needs a
 * PROGRAM-PRESERVING interpreter ([sint](p2d p, d) = (p2d p . [p](d))), so the
 * residual must reproduce the source program as well as the answer -- work that
 * p itself never does.  Comparing it with p therefore measures the projection's
 * definition, not the specialiser.  The fair baseline is p+ =
 * Simp.program_preserving p, the smallest EXTENSION of p with the SAME obligation; the
 * criterion becomes  residual <= p+.  That p+ is the right baseline is not
 * assumed: the first test below checks that p+, the self-interpreter and the
 * residual all return the SAME value.
 *
 * MEASURED (./measure_proj jones-self; steps = command nodes, work = value nodes
 * examined by comparison; residual = after Simp.copyprop_program):
 *
 *   program       |resid| lp_p lp_r st_dir st_p+ st_si st_raw st_res  wk_p+ wk_si wk_res
 *   id                53     0    0      1     5     89     11      3     23    64     23
 *   id2               87     0    0      1     5     90     19      7     25    75     25
 *   id3              139     0    0      1     5    184     27     11     38   150     37
 *   rep               87     0    0      1     5     90     19      7     25    75     25
 *   swap             379     0    0      3     7    260     41     25     57   234     57
 *   sx_splitjoin     343     0    0      3     7    260     41     23     57   234     57
 *   sx_three         543     0    0      3     7    354     51     35     72   311     71
 *   loop_static2     121     1    0      6    10   1240     15      1    104  1164     95
 *   loop_static3     131     1    0      8    12   1852     15      1    118  1723    101
 *
 * (lp_p / lp_r = CLoop nodes in p / in the residual.)
 *
 * Four readings, each pinned by a test below:
 *   (1) On the WORK meter the criterion HOLDS: wk_res <= wk_p+ in every case
 *       (and strictly below on id3/sx_three and on both loop subjects).  The
 *       residual examines no more value nodes than the program-preserving
 *       baseline.
 *   (2) On the STEPS meter it FAILS for the STRAIGHT-LINE subjects: 1.4x-5.0x
 *       of p+ (only `id` is under, at 0.6x).  The residual pays extra COMMANDS
 *       -- the interpreter's data staging, made explicit -- while touching the
 *       same amount of data.  This is the same metric-dependence RWHILE_S.md
 *       already records for the op-language interpreters, now at the
 *       self-interpreter.
 *   (2') ...and it HOLDS for the LOOP subjects, by a wide margin (0.1x of p+):
 *       there the specialiser has something to remove.  loop_static2/3 have a
 *       statically-controlled loop over a dynamic body; unrolling collapses the
 *       whole thing into ONE residual command (st_res = 1), and adding a third
 *       iteration does not change that.  So the steps-meter failure in (2) is
 *       not "the specialiser is bad at everything" -- it is the fixed cost of
 *       staging, which straight-line subjects cannot amortise.
 *   (3) The interpretive layer is nevertheless mostly gone: 25-30x fewer steps
 *       than self-interpretation (over 1000x on the loop subjects).
 * A negative is pinned as a test on purpose: if (2) flips, the specialiser got
 * better and the claim in RWHILE_S.md must be re-measured, not silently kept.
 *
 * WHAT IS STILL NOT IN THE TABLE (2026-08-09): a DATA-DEPENDENT loop.  The
 * boundary is not "loops" -- loop_static2/3 are loops and they specialise --
 * it is DYNAMIC CONTROL; see the `jones-self-open` tests below, which pin the
 * failure and localise it. *)
let jones_self_cases =
  let ab = VCons (atom "'a", atom "'b") in
  let ab_nil = VCons (atom "'a", VCons (atom "'b", VNil)) in
  [ "id", ab; "id2", ab; "id3", ab; "rep", ab;
    "swap", ab; "sx_splitjoin", ab; "sx_three", ab_nil;
    "loop_static2", ab; "loop_static3", ab ]

(* CLoop nodes in a program body.  The loop subjects need this: the claim about
   them is not only that they are cheap but that the loop is GONE. *)
let rec js_count_loops = function
  | CSeq (a, b)        -> js_count_loops a + js_count_loops b
  | CCond (_, t, e, _) -> js_bthen t + js_belse e
  | CLoop (_, d, l, _) -> 1 + js_bdo d + js_bloop l
  | CLocal (_, c)      -> js_count_loops c
  | _ -> 0
and js_bthen = function BThen c -> js_count_loops c | BThenNone -> 0
and js_belse = function BElse c -> js_count_loops c | BElseNone -> 0
and js_bdo   = function BDo c -> js_count_loops c | BDoNone -> 0
and js_bloop = function BLoop c -> js_count_loops c | BLoopNone -> 0
let js_body_loops (Prog (_, _, b, _)) = js_count_loops b

type jones_row = {
  jname : string;
  lp_p : int; lp_r : int;              (* CLoop nodes in p / in the residual *)
  st_dir : int; wk_dir : int;          (* p, run directly *)
  st_pp : int;  wk_pp : int;           (* p+ : program-preserving p *)
  st_si : int;  wk_si : int;           (* self-interpretation via ri_fp3 *)
  st_raw : int;                        (* residual as spec_av emits it *)
  st_res : int; wk_res : int;          (* residual after copy propagation *)
  agree : bool;                        (* p+, sint and the residual agree *)
}

(* Specialising ri_fp3 seven times takes about a second, so the table is
   computed once and shared by the tests in the group. *)
let jones_self_table = lazy (
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let sint = parse_file_program (examples_dir ^ "/ri_fp3.rwhile") in
  let pd_sint = Program2DataRwhile.program2data sint in
  let meter f = EvalRwhile.reset_steps (); EvalRwhile.reset_work ();
    let v = f () in (v, EvalRwhile.get_steps (), EvalRwhile.get_work ()) in
  List.map (fun (name, d) ->
      let srcp = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
      let pd = Program2DataRwhile.program2data srcp in
      let (dres, sd, wd) = meter (fun () -> EvalRwhile.evalProgram srcp d) in
      let (ppres, sp, wp) =
        meter (fun () -> EvalRwhile.evalProgram (Simp.program_preserving srcp) d) in
      let (sires, ss, ws) =
        meter (fun () -> EvalRwhile.evalProgram sint (VCons (pd, d))) in
      let raw = Program2DataRwhile.data2program
          (EvalRwhile.evalProgram spec_av (spec_in pd_sint pd)) in
      let (_, sraw, _) = meter (fun () -> EvalRwhile.evalProgram raw d) in
      let cpp = Simp.copyprop_program raw in
      let (rres, sr, wr) = meter (fun () -> EvalRwhile.evalProgram cpp d) in
      { jname = name; lp_p = js_body_loops srcp; lp_r = js_body_loops cpp;
        st_dir = sd; wk_dir = wd; st_pp = sp; wk_pp = wp;
        st_si = ss; wk_si = ws; st_raw = sraw; st_res = sr; wk_res = wr;
        agree = (ppres = sires && ppres = rres
                 && rres = VCons (pd, dres)) })
    jones_self_cases)

(* (0) THE BASELINE IS THE RIGHT ONE.  p+ , the self-interpreter and the fp1
 * residual all compute (p2d p . [p](d)) -- so comparing their costs compares
 * three ways of doing one and the same job.  Without this the ratios below
 * would be meaningless. *)
let test_jones_self_baseline_agrees () =
  List.iter (fun r ->
      Alcotest.(check bool)
        (r.jname ^ ": [p+](d) = [ri_fp3](p2d p, d) = [residual](d) = (p2d p . [p](d))")
        true r.agree)
    (Lazy.force jones_self_table);
  (* ...and p+ is a legitimate R-WHILE program: its syntactic inverse undoes it.
     A baseline that were not reversible would not be one for this language. *)
  List.iter (fun (name, d) ->
      let pp = Simp.program_preserving
          (parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile")) in
      Alcotest.(check valT_testable)
        (name ^ ": [inv p+]([p+](d)) = d (p+ is reversible)")
        d (EvalRwhile.evalProgram (InvRwhile.invProgram pp)
             (EvalRwhile.evalProgram pp d)))
    jones_self_cases

(* (1) THE RESULT.  On the work meter (value nodes examined by comparison) the
 * fp1 residual of the SELF-interpreter is at least as good as p+: reversible
 * Jones optimality holds. *)
let test_jones_self_work_optimal () =
  List.iter (fun r ->
      Alcotest.(check bool)
        (Printf.sprintf "%s: work(residual)=%d <= work(p+)=%d" r.jname r.wk_res r.wk_pp)
        true (r.wk_res <= r.wk_pp))
    (Lazy.force jones_self_table)

(* (2) THE HONEST OTHER HALF.  On the steps meter (command nodes) it does NOT
 * hold for the STRAIGHT-LINE subjects: each of them but `id` needs more
 * commands than p+.  It DOES hold for the loop subjects, where unrolling has
 * something to remove.  Both directions are pinned, so that an improvement to
 * the specialiser -- or a regression on the loop subjects -- shows up as a
 * failing test rather than as a stale claim in RWHILE_S.md. *)
let test_jones_self_steps_not_optimal () =
  let under_pp = ["id"; "loop_static2"; "loop_static3"] in
  List.iter (fun r ->
      let expect_over = not (List.mem r.jname under_pp) in
      Alcotest.(check bool)
        (Printf.sprintf "%s: steps(residual)=%d vs steps(p+)=%d (over p+ expected: %b)"
           r.jname r.st_res r.st_pp expect_over)
        expect_over (r.st_res > r.st_pp))
    (Lazy.force jones_self_table)

(* (2') THE LOOP SUBJECTS.  They are what makes the table say anything about
 * loops at all, so their two defining properties are checked rather than
 * assumed: p really contains a loop, and the residual really does not (spec_av
 * unrolled it).  The residual then beats p+ on BOTH meters -- the only subjects
 * that do -- which is the honest counterweight to (2). *)
let test_jones_self_loop_subjects_unrolled () =
  let loops = List.filter (fun r -> List.mem r.jname ["loop_static2"; "loop_static3"])
      (Lazy.force jones_self_table) in
  Alcotest.(check int) "two loop subjects are in the table" 2 (List.length loops);
  List.iter (fun r ->
      Alcotest.(check int) (r.jname ^ ": p contains a loop") 1 r.lp_p;
      Alcotest.(check int) (r.jname ^ ": residual is loop-free (unrolled)") 0 r.lp_r;
      Alcotest.(check bool)
        (Printf.sprintf "%s: steps(residual)=%d <= steps(p+)=%d" r.jname r.st_res r.st_pp)
        true (r.st_res <= r.st_pp);
      Alcotest.(check bool)
        (Printf.sprintf "%s: work(residual)=%d < work(p+)=%d" r.jname r.wk_res r.wk_pp)
        true (r.wk_res < r.wk_pp))
    loops

(* (2'') ...and the residual is a COMPILED program, not a table lookup for the
 * one input the measurement used.  The table above runs each residual on a
 * single d; here the loop subjects' residuals are run on three different d and
 * must agree with p+ on each.  Without this the 0.1x ratios could be an
 * artefact of having specialised away the input as well as the loop. *)
let test_jones_self_loop_residual_is_general () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let sint = parse_file_program (examples_dir ^ "/ri_fp3.rwhile") in
  let pd_sint = Program2DataRwhile.program2data sint in
  let inputs = [ VCons (atom "'a", atom "'b"); VNil; parse_val "(('x . nil) . 'y)" ] in
  List.iter (fun name ->
      let srcp = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
      let pd = Program2DataRwhile.program2data srcp in
      let resid = Simp.copyprop_program (Program2DataRwhile.data2program
          (EvalRwhile.evalProgram spec_av (spec_in pd_sint pd))) in
      let pp = Simp.program_preserving srcp in
      List.iter (fun d ->
          Alcotest.(check valT_testable)
            (name ^ ": [residual](d) = [p+](d) for a d the measurement did not use")
            (EvalRwhile.evalProgram pp d) (EvalRwhile.evalProgram resid d);
          (* and it is still a reversible program *)
          Alcotest.(check valT_testable) (name ^ ": [inv residual]([residual](d)) = d")
            d (EvalRwhile.evalProgram (InvRwhile.invProgram resid)
                 (EvalRwhile.evalProgram resid d)))
        inputs)
    ["loop_static2"; "loop_static3"]

(* (3) The interpretive layer is nevertheless removed almost entirely: the
 * residual runs in under a fifth of the self-interpretation's steps (measured:
 * a 10x-30x reduction) and examines fewer value nodes. *)
let test_jones_self_removes_interpretation () =
  List.iter (fun r ->
      Alcotest.(check bool)
        (Printf.sprintf "%s: steps(residual)=%d << steps(self-interp)=%d" r.jname r.st_res r.st_si)
        true (r.st_res * 5 <= r.st_si);
      Alcotest.(check bool)
        (Printf.sprintf "%s: work(residual)=%d < work(self-interp)=%d" r.jname r.wk_res r.wk_si)
        true (r.wk_res < r.wk_si))
    (Lazy.force jones_self_table)

(* (4) COPY PROPAGATION IS WHAT BUYS IT.  The residual as spec_av emits it costs
 * strictly more steps than the copy-propagated one, on every subject -- the
 * capture-on-escape temps introduced in spec_av 2026-08-08 are pure moves.  So
 * the numbers above are a claim about the PAIR (spec_av, Simp.copyprop_program),
 * which is what `./ri -copyprop` exposes. *)
let test_jones_self_copyprop_needed () =
  List.iter (fun r ->
      Alcotest.(check bool)
        (Printf.sprintf "%s: steps(raw)=%d > steps(copyprop)=%d" r.jname r.st_raw r.st_res)
        true (r.st_raw > r.st_res))
    (Lazy.force jones_self_table)

(* ===== jones-self-open: WHERE THE BATTERY STOPS, AND WHY (2026-08-09) =====
 *
 * The jones-self table has loop subjects now (loop_static2/3), but they have
 * STATIC loop control.  examples/reverse.rwhile -- the obvious loop subject --
 * still cannot be specialised, and the handover note that came with it said the
 * cause was "fp1-via-ri_fp3 does not handle loops yet".  Measured here, that is
 * NOT the cause; these three tests pin what is:
 *
 *   (a) ri_fp3 self-interprets reverse CORRECTLY.  The interpreter is fine.
 *   (b) [spec_av]((ri_fp3 . reverse)) dies with spec_av's own `'error <= '41`,
 *       which is raised at exactly ONE place in examples/spec_av.rwhile: the
 *       'lcheck handler, when a loop's EXIT test is dynamic.  'lcheck is the
 *       continuation that static unrolling pushes, so the message means "I
 *       started unrolling a loop and its exit test then stopped being static",
 *       for which spec_av has no residualisation path.
 *   (c) the SAME failure appears for examples/dyncond3.rwhile, which has NO
 *       loop at all -- just a conditional on the dynamic input.  So the
 *       boundary is DYNAMIC CONTROL, not loops: a dynamic branch inside the
 *       interpreted program makes spec_av dynamicize the store, ri_fp3's code
 *       stack Cd is part of that store, and ri_fp3's own main loop
 *       (`from =? Cd' nil loop STEP-FP3 until =? Cd nil`) is the loop whose
 *       exit test goes dynamic mid-unroll.
 *   (d) and it is not an ri_fp3 artefact either: specialising reverse DIRECTLY
 *       (no interpreter in the picture) fails with the same '41, because
 *       reverse's own `until =? Y nil` goes dynamic after the static head of
 *       the partial-static input is consumed.
 *
 * Contrast: a dynamic conditional in a subject specialised DIRECTLY is handled
 * (test_fp1_dyncond_direct_ok below, and ./measure_proj dyncond) -- spec_av's
 * dynamic-'cond path residualises fine.  What has no path is a dynamic exit
 * test reached AFTER unrolling began.  See FINDINGS_reversible_projections.md
 * for the analysis and the size estimate of a fix.
 *
 * These are pinned as EXPECTED FAILURES.  If one of them stops raising, the
 * specialiser gained a loop/dynamic-control path and the tables in RWHILE_S.md
 * must be re-measured rather than left standing. *)
let spec_av_error_41 =
  Failure "Pattern matching failed: '41 and 'error are not equal (in inv_evalPat)"

let test_jones_self_open_interpreter_is_fine () =
  let sint = parse_file_program (examples_dir ^ "/ri_fp3.rwhile") in
  let rev = parse_file_program (examples_dir ^ "/reverse.rwhile") in
  let pd = Program2DataRwhile.program2data rev in
  let d = parse_val "('a . ('b . nil))" in
  (* [ri_fp3](p2d reverse, d) = (p2d reverse . [reverse](d)) -- so the loop
     subject that cannot be SPECIALISED is nevertheless INTERPRETED correctly. *)
  Alcotest.(check valT_testable)
    "ri_fp3 self-interprets reverse (the interpreter is not the wall)"
    (VCons (pd, EvalRwhile.evalProgram rev d))
    (EvalRwhile.evalProgram sint (VCons (pd, d)))

let test_jones_self_open_dynamic_control_via_ri_fp3 () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let pd_sint = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_fp3.rwhile")) in
  let fp1 name =
    let pd = Program2DataRwhile.program2data
        (parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile")) in
    fun () -> ignore (EvalRwhile.evalProgram spec_av (spec_in pd_sint pd)) in
  (* a DATA-DEPENDENT loop ... *)
  Alcotest.check_raises
    "OPEN: fp1-via-ri_fp3 of reverse dies at spec_av's 'lcheck ('error <= '41)"
    spec_av_error_41 (fp1 "reverse");
  (* ... and a program with NO loop but a dynamic conditional dies identically,
     which is what identifies the boundary as dynamic control rather than loops *)
  Alcotest.check_raises
    "OPEN: fp1-via-ri_fp3 of dyncond3 (loop-free!) dies the same way"
    spec_av_error_41 (fp1 "dyncond3")

let test_jones_self_open_direct_fp1_too () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let pd_rev = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/reverse.rwhile")) in
  (* No interpreter in the picture: reverse is the SUBJECT.  Its exit test
     `=? Y nil` is static (false) while Y is the partial-static input cons, and
     dynamic once the static head has been consumed -> the same '41. *)
  Alcotest.check_raises
    "OPEN: direct fp1 of reverse dies at 'lcheck too (not an ri_fp3 artefact)"
    spec_av_error_41
    (fun () -> ignore (EvalRwhile.evalProgram spec_av (spec_in pd_rev (atom "'c"))));
  (* ...whereas a genuinely dynamic CONDITIONAL in a direct subject IS handled:
     fp_dyncond_bug's `if D` tests the dynamic half of the input, and spec_av
     residualises it into a correct two-way residual.  This control case keeps
     (d) from being read as "spec_av cannot do anything dynamic": what has no
     path is a dynamic test reached after unrolling has begun. *)
  let pd_dyn = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/fp_dyncond_bug.rwhile")) in
  let comp = Program2DataRwhile.data2program
      (EvalRwhile.evalProgram spec_av (spec_in pd_dyn VNil)) in
  Alcotest.(check valT_testable)
    "control: a dynamic cond in a DIRECT subject residualises correctly ('one)"
    (atom "'one") (EvalRwhile.evalProgram comp (atom "'q"));
  Alcotest.(check valT_testable)
    "control: ...and takes the other branch on the other input ('two)"
    (atom "'two") (EvalRwhile.evalProgram comp VNil)

(* Evaluate a program-as-data value (a spec residual / comp) DIRECTLY by
 * decoding it back to an AST -- the reliable alternative to run_via_ri, which
 * routes through the ri.rwhile self-interpreter (see the known bug below). *)
let run_comp_direct comp d =
  EvalRwhile.evalProgram (Program2DataRwhile.data2program comp) d

(* CORRECTED DIAGNOSIS (was mislabelled "spec_av dynamic-cond residualization").
 * For examples/fp_dyncond_bug.rwhile, spec_av's residual comp is actually
 * CORRECT: comp = [spec_av]((prog.('S.nil))) and [comp](d) evaluated DIRECTLY
 * gives 'one (resp. 'two).  The failure only appears through run_via_ri: the
 * ri.rwhile self-interpreter is unfaithful here.  Two distinct ri.rwhile bugs
 * were found:
 *   BUG 1 (FIXED): 'cond cleared the saved entry-test value W against the
 *     exit-assertion value V by bit-equality (`Arg ^= V`), but R-WHILE only
 *     requires equal TRUTHINESS.  Fixed via the CANON macro in ri.rwhile.
 *   BUG 2 (OPEN, dominant): the reversible self-clear `X ^= X` (and any
 *     `X ^= E` whose E reads X) is mis-interpreted.  'ass does
 *     EVAL-EXP(E); DUPDATE(K); INV-EVAL-EXP(E); the DUPDATE changes what E
 *     reads, so INV-EVAL-EXP (which re-reads the store) cannot clear its temp
 *     -> "error in update".  Minimal repros: `A ^= A`, `Y ^= 'k; Y ^= Y`.
 *     fp_dyncond_bug.rwhile uses `D ^= D`, so run_via_ri still raises.  Fixing
 *     it needs EVAL-EXP to reverse store-reads via saved values, not re-reads.
 * So run_via_ri (the fp2 success criterion) is unreliable; direct decode+eval
 * (run_comp_direct) is reliable.  This test pins BOTH facts (comp correct
 * directly; raises via run_via_ri).  Flip the check_raises to a value check
 * once BUG 2 is fixed.  See HANDOFF_fp2.md and the example header. *)
let test_fp1_dyncond_known_bug () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let prog = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/fp_dyncond_bug.rwhile")) in
  let comp = EvalRwhile.evalProgram spec_av (spec_in prog VNil) in
  (* (1) the residual is CORRECT under direct evaluation *)
  Alcotest.(check valT_testable) "dyn-cond comp correct directly: [comp]('q)='one"
    (atom "'one") (run_comp_direct comp (atom "'q"));
  Alcotest.(check valT_testable) "dyn-cond comp correct directly: [comp](nil)='two"
    (atom "'two") (run_comp_direct comp VNil);
  (* (2) KNOWN BUG 2 (self-clear `X ^= X`): the SAME correct comp still fails
   *     through ri.rwhile (run_via_ri) -- the residual uses `D ^= D` *)
  Alcotest.check_raises
    "KNOWN BUG (ri.rwhile self-clear X^=X): correct comp fails via run_via_ri"
    (Failure "error in update")
    (fun () -> ignore (run_via_ri comp (atom "'q")))

(* Depth-general read-pattern residualization (PAT-READ-ITER).  After a dynamic
 * conditional (DYNAMICIZE-ALL), the output is assembled from a deeply nested
 * read pattern `cons R (cons (cons Sv H) Tl)` of dynamic components.  The old
 * depth-1 PAT-READ-AV baked the nested sub-conses as static-literal AVs, so the
 * residual never assembled them (variables left non-nil).  PAT-READ-ITER reads
 * arbitrary depth -> the residual is correct.  This is the same fix that makes
 * the 2nd reversible Futamura projection produce a correct compiler (spec_av's
 * own ASSEMBLE-FP1 builds such a nested output pattern).  No self-clear, so it
 * is checked via BOTH direct eval and run_via_ri. *)
let test_fp1_nested_read () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let prog = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/fp_nested_read.rwhile")) in
  let comp = EvalRwhile.evalProgram spec_av (spec_in prog VNil) in
  let expected = parse_val "('one . ((nil . 'y) . 'z))" in
  Alcotest.(check valT_testable) "nested-read comp correct (direct eval)"
    expected (run_comp_direct comp (parse_val "('y . 'z)"));
  Alcotest.(check valT_testable) "nested-read comp correct (via ri.rwhile)"
    expected (run_via_ri comp (parse_val "('y . 'z)"))

(* ===== Reversible Futamura projections 2 & 3 (fp2 = compiler, fp3 = cogen) =====
 * fp2: comp2 = [spec_av]((spec_av . ('S . ri_min))) is a COMPILER mapping each
 *      source op to its fp1 residual: [comp2](('S.op)) == B = [spec_av]((ri_min
 *      . ('S.op))).
 * fp3: comp3 = [spec_av]((spec_av . ('S . spec_av))) is a COGEN: [comp3](('S.p))
 *      == [spec_av]((spec_av . ('S.p))).  In particular [comp3](('S.ri_min)) is
 *      the ri_min compiler comp2, so [[comp3]('S.ri_min)](('S.op)) == B.
 * spec_av's AV store (AV-INIT N = FpN) must cover the variable count of the
 * program being specialized; for fp3 that program is spec_av itself (~223 vars),
 * so FpN is set to 256 in the source (the temp-var index TmpT=250 is above the
 * program vars too).  Judged by DIRECT eval (data2program): run_via_ri is
 * unfaithful on the self-clears the residual contains (ri.rwhile cannot
 * reverse-interpret X^=X; see test_fp1_dyncond_known_bug).  SLOW (~minutes). *)
let test_fp2_second_projection () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let inner = Program2DataRwhile.program2data spec_av in
  let rimin = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let comp = EvalRwhile.evalProgram spec_av (spec_in inner rimin) in
  (* [comp](('S.op)) must equal the fp1 residual B = [spec_av]((ri_min.('S.op))) *)
  let check_op op =
    let b = EvalRwhile.evalProgram spec_av (spec_in rimin (atom op)) in
    let comp_op = run_comp_direct comp (VCons (atom "'S", atom op)) in
    Alcotest.(check valT_testable)
      (Printf.sprintf "fp2: [comp](('S.%s)) == fp1 residual B" op) b comp_op;
    comp_op in
  let comp_swap = check_op "'swap" in
  ignore (check_op "'id");
  (* end-to-end: the compiled swap actually swaps, the compiled id is identity *)
  Alcotest.(check valT_testable) "fp2 end-to-end: [[comp]'swap](('a.'b)) = ('swap.('b.'a))"
    (parse_val "('swap . ('b . 'a))") (run_comp_direct comp_swap (parse_val "('a . 'b)"))

(* #5 (benchmark + regression guard): specialisation is EFFECTIVE -- the fp1
 * residual is strictly SMALLER than the interpreter it specialises (static
 * dispatch resolved at specialisation time), i.e. not a mere interpreter
 * embedding.  Generalises the IEICE draft's single "103 < 163" datapoint to a
 * checked invariant.  Sizes are p2d node counts (EvalRwhile.count_nodes). *)
let test_specialization_gain () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let rimin = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let int_size = EvalRwhile.count_nodes rimin in
  (* Measured on the residual AFTER copy propagation (2026-08-08).  spec_av now
     CAPTURES every dynamic annotated value as it escapes into a compound, which
     is what removes the nested-pattern bound of fp1-via-ri_fp3; the price is one
     `Tmp <= ('var.k)` per escape, overwhelmingly for slots that are never
     reused.  Those are a write-once/read-once temp, i.e. a copy, and
     Simp.copyprop_program removes them -- taking the residual well BELOW where
     it was before capture (swap 103 -> 59 nodes, 0.63x -> 0.36x |ri_min|).
     Judging the raw residual here would measure the intermediate, not the
     specialiser's output. *)
  let resid_size op =
    EvalRwhile.count_nodes
      (Program2DataRwhile.program2data
         (Simp.copyprop_program
            (Program2DataRwhile.data2program
               (EvalRwhile.evalProgram spec_av (spec_in rimin (atom op)))))) in
  let b_swap = resid_size "'swap" and b_id = resid_size "'id" in
  Printf.eprintf
    "[SPEC-GAIN] ri_min interpreter = %d nodes; fp1 residual: swap=%d, id=%d\n%!"
    int_size b_swap b_id;
  Alcotest.(check bool) "fp1 residual (swap) is smaller than the interpreter" true (b_swap < int_size);
  Alcotest.(check bool) "fp1 residual (id) is smaller than the interpreter"   true (b_id   < int_size)

(* fp3 (cogen): comp3 = [spec_av]((spec_av . ('S . spec_av))).  [comp3](('S.ri_min))
 * is the ri_min compiler comp2, and [comp2](('S.op)) == B.  Verified end-to-end
 * by DIRECT eval.  VERY SLOW (self-application of the full specialiser). *)
let test_fp3_cogen () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let inner = Program2DataRwhile.program2data spec_av in
  let rimin = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  (* comp3 = cogen; comp2' = [comp3](('S.ri_min)) = the ri_min compiler *)
  let comp3  = EvalRwhile.evalProgram spec_av (spec_in inner inner) in
  let comp2' = run_comp_direct comp3 (VCons (atom "'S", rimin)) in
  let check_op op =
    let b = EvalRwhile.evalProgram spec_av (spec_in rimin (atom op)) in
    Alcotest.(check valT_testable)
      (Printf.sprintf "fp3: [[comp3]('S.ri_min)](('S.%s)) == fp1 residual B" op)
      b (run_comp_direct comp2' (VCons (atom "'S", atom op))) in
  check_op "'swap";
  check_op "'id"

(* fp2 for the REVERSIBLE specializer spec_av_rev (self-application of the reversible
 * PE -- the core novelty).  comp_rev = [spec_av_rev]((spec_av_rev . ('S.ri_min))) is
 * a reversible compiler; [comp_rev](('S.op)) must equal the fp1-rev residual
 * B_rev = [spec_av_rev]((ri_min.('S.op))), and the compiled op must run correctly.
 * SLOW. *)
let test_fp2_rev_second_projection () =
  let rev = parse_file_program (examples_dir ^ "/spec_av_rev.rwhile") in
  let inner = Program2DataRwhile.program2data rev in
  let rimin = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let comp = EvalRwhile.evalProgram rev (spec_in inner rimin) in
  let check_op op =
    let b = EvalRwhile.evalProgram rev (spec_in rimin (atom op)) in
    let comp_op = run_comp_direct comp (VCons (atom "'S", atom op)) in
    Alcotest.(check valT_testable)
      (Printf.sprintf "fp2-rev: [comp_rev](('S.%s)) == fp1-rev residual B" op) b comp_op;
    comp_op in
  let comp_swap = check_op "'swap" in
  ignore (check_op "'id");
  Alcotest.(check valT_testable) "fp2-rev end-to-end: [[comp_rev]'swap](('a.'b)) = ('swap.('b.'a))"
    (parse_val "('swap . ('b . 'a))") (run_comp_direct comp_swap (parse_val "('a . 'b)"))

(* fp3 (cogen) for the reversible specializer: comp3_rev = [spec_av_rev]((spec_av_rev
 * . ('S.spec_av_rev))); [comp3_rev](('S.ri_min)) is the reversible ri_min compiler,
 * and [that](('S.op)) == B_rev.  VERY SLOW. *)
let test_fp3_rev_cogen () =
  let rev = parse_file_program (examples_dir ^ "/spec_av_rev.rwhile") in
  let inner = Program2DataRwhile.program2data rev in
  let rimin = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let comp3  = EvalRwhile.evalProgram rev (spec_in inner inner) in
  let comp2' = run_comp_direct comp3 (VCons (atom "'S", rimin)) in
  let check_op op =
    let b = EvalRwhile.evalProgram rev (spec_in rimin (atom op)) in
    Alcotest.(check valT_testable)
      (Printf.sprintf "fp3-rev: [[comp3_rev]('S.ri_min)](('S.%s)) == B_rev" op)
      b (run_comp_direct comp2' (VCons (atom "'S", atom op))) in
  check_op "'swap";
  check_op "'id"

(* Reversible specializer prototype (examples/spec_av_rev.rwhile): CLEAR pushes the
 * discarded value onto a garbage stack GARB instead of X^=X, and main embeds GARB
 * into the residual's DEAD (constant-true) else-branch (EMBED-GARB).  This makes
 * spec REVERSIBLE: it runs with a clean store (so evalProgram does not raise
 * "variables not nil"), [comp](d) is unchanged (the dead branch never runs), and
 * -- the decisive property -- inverting the specializer and running it on its own
 * output RECONSTRUCTS the original input from the dead-branch garbage. *)
let test_rev_spec_dead_garbage () =
  let rev   = parse_file_program (examples_dir ^ "/spec_av_rev.rwhile") in
  let rimin = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let input = spec_in rimin (atom "'swap") in
  let comp  = EvalRwhile.evalProgram rev input in   (* raises if the store is not clean *)
  (* [comp](d) still computes swap, ignoring the dead garbage branch *)
  Alcotest.(check valT_testable) "rev: [comp](('a.'b)) = ('swap.('b.'a))"
    (parse_val "('swap . ('b . 'a))") (run_comp_direct comp (parse_val "('a . 'b)"));
  (* reversibility: inverting spec_av_rev and running it on comp recovers the input *)
  let inv = InvRwhile.invProgram rev in
  Alcotest.(check valT_testable) "rev: [INV-spec_av_rev](comp) == input (round-trip)"
    input (EvalRwhile.evalProgram inv comp)

(* Refactoring gate: examples/spec_av_clean.rwhile (the readability/paper rewrite)
 * MUST stay behaviorally identical to the canonical examples/spec_av.rwhile
 * (git tag spec_av-fp123-working).  Asserts byte-identical fp1 residuals for
 * ri_min and ri_seq.  While refactoring spec_av_clean, keep this green; when the
 * refactor touches the deeper machinery, also re-check fp2/fp3 by direct eval. *)
let test_clean_equiv_spec_av () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let clean   = parse_file_program (examples_dir ^ "/spec_av_clean.rwhile") in
  let p2d f = Program2DataRwhile.program2data
      (parse_file_program (examples_dir ^ "/" ^ f ^ ".rwhile")) in
  let ri_min = p2d "ri_min" and ri_seq = p2d "ri_seq" in
  let check name prog src =
    Alcotest.(check valT_testable) ("spec_av_clean == spec_av: " ^ name)
      (EvalRwhile.evalProgram spec_av (spec_in prog src))
      (EvalRwhile.evalProgram clean   (spec_in prog src)) in
  check "ri_min swap" ri_min (atom "'swap");
  check "ri_min id"   ri_min (atom "'id");
  check "ri_seq [id,swap]"   ri_seq (parse_val "('id . ('swap . nil))");
  check "ri_seq [swap,swap]" ri_seq (parse_val "('swap . ('swap . nil))")

(* Strong refactor gate: spec_av_clean and spec_av must produce the IDENTICAL fp2
 * compiler.  Specialising spec_av (itself) to ri_min exercises essentially every
 * path of the specialiser, so this catches any behavioral drift the fast fp1
 * gate might miss.  SLOW (~seconds).  Forced to canonical (non-hygienic) mode:
 * each side specialises p2d of ITSELF, and spec_av_clean has extra macros, so
 * under hygiene the two p2d encodings get different variable numbering -- a
 * cross-comparison artifact, not a behavioral difference (the fp1 gate, same
 * ri_min both sides, is hygiene-stable and covers hygiene-cleanliness). *)
let test_clean_equiv_fp2 () =
  with_flag false (fun () ->
    let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
    let clean   = parse_file_program (examples_dir ^ "/spec_av_clean.rwhile") in
    let rimin = Program2DataRwhile.program2data
        (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
    Alcotest.(check valT_testable) "spec_av_clean fp2 comp == spec_av fp2 comp"
      (EvalRwhile.evalProgram spec_av (spec_in (Program2DataRwhile.program2data spec_av) rimin))
      (EvalRwhile.evalProgram clean   (spec_in (Program2DataRwhile.program2data clean)   rimin)))

(* ===== First Futamura projection, GREEN via the minimal self-interpreter =====
 * ri_min interprets a tiny one-op language (Op = 'swap | else 'id) using only
 * depth-1 cons patterns and a single static dispatch (no loops, no nested
 * patterns).  spec_av therefore specializes it cleanly with the depth-1
 * PAT-WRITE-STRUCT -- it terminates and is correct, unlike ri_fp3 whose
 * stack-machine deep patterns make PAT-WRITE-ITER diverge.
 *   comp = [spec_av]((ri_min . Op));  [comp](d) = [ri_min]((Op . d)) = (Op . op(d))
 * This is a genuine fp1: specializing an INTERPRETER w.r.t. a static source. *)
let fp1_min op_str d =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_min = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let comp = EvalRwhile.evalProgram spec_av (spec_in ri_min (parse_val op_str)) in
  run_via_ri comp d

(* fp1 via ri_seq: specialize the sequence interpreter w.r.t. a static op LIST.
 * Exercises a STATIC loop (unrolled by spec_av) over the op list, plus depth-1
 * swaps on the dynamic data.  Output = (Prog . result). *)
let fp1_seq proglist_str d =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_seq = Program2DataRwhile.program2data
    (parse_file_program (examples_dir ^ "/ri_seq.rwhile")) in
  let comp = EvalRwhile.evalProgram spec_av (spec_in ri_seq (parse_val proglist_str)) in
  run_via_ri comp d

let test_fp1_seq_empty () =
  Alcotest.(check valT_testable)
    "[[spec_av]((ri_seq.[]))](('a.'b)) = ([].('a.'b))"
    (parse_val "(nil . ('a . 'b))") (fp1_seq "nil" (parse_val "('a . 'b)"))

let test_fp1_seq_idswap () =
  (* a 2-element program [id,swap]: static loop runs twice; net effect = one swap *)
  Alcotest.(check valT_testable)
    "[[spec_av]((ri_seq.[id,swap]))](('a.'b)) = ([id,swap].('b.'a))"
    (parse_val "(('id . ('swap . nil)) . ('b . 'a))")
    (fp1_seq "('id . ('swap . nil))" (parse_val "('a . 'b)"))

(* [swap,swap] (a value PERMUTATION = identity) used to make the no-alias move
 * logic emit a naive variable swap `V4 <= V3; V3 <= V4` in the residual, which
 * conflicts at runtime (both non-nil) -> "error in update".  PAT-WRITE-STRUCT now
 * detects the two-leaf TRANSPOSITION and realizes it as a swap-via-temp
 * (`tmp <= V4; V4 <= V3; V3 <= tmp`) via SWAP-VIA-TEMP, so value-permuting
 * sequences are green too. *)
let test_fp1_seq_swapswap () =
  (* [swap,swap] = identity (two transpositions of the data pair); the residual
   * must swap-via-temp, not emit a conflicting naive variable swap. *)
  Alcotest.(check valT_testable)
    "[[spec_av]((ri_seq.[swap,swap]))](('a.'b)) = ([swap,swap].('a.'b))"
    (parse_val "(('swap . ('swap . nil)) . ('a . 'b))")
    (fp1_seq "('swap . ('swap . nil))" (parse_val "('a . 'b)"))

let test_fp1_min_swap () =
  Alcotest.(check valT_testable)
    "[[spec_av]((ri_min.'swap))](('a.'b)) = ('swap.('b.'a))"
    (parse_val "('swap . ('b . 'a))") (fp1_min "'swap" (parse_val "('a . 'b)"))

let test_fp1_min_id () =
  Alcotest.(check valT_testable)
    "[[spec_av]((ri_min.'id))]('q) = ('id.'q)"
    (parse_val "('id . 'q)") (fp1_min "'id" (atom "'q"))

(* Strengthen fp1 correctness from a few hand-picked inputs to EXHAUSTIVE over a
 * set of small input shapes: the residual must reversibly simulate the source
 * (snd = result, fst = src) on every input.  comp is computed ONCE per source. *)
let small_vals = List.map parse_val
  [ "nil"; "'a"; "('a . 'b)"; "(nil . nil)"; "('a . ('b . 'c))";
    "(('a . 'b) . 'c)"; "(('a . 'b) . ('c . 'd))"; "('x . ('y . ('z . nil)))" ]

let test_fp1_min_exhaustive () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_min  = Program2DataRwhile.program2data
                  (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let comp op = EvalRwhile.evalProgram spec_av (spec_in ri_min (parse_val op)) in
  let comp_id = comp "'id" and comp_swap = comp "'swap" in
  (* id: [comp_id](d) = (id . d) for EVERY input d *)
  List.iter (fun d ->
    Alcotest.(check valT_testable) "fp1 ri_min id (exhaustive)"
      (pair (atom "'id") d) (run_via_ri comp_id d)) small_vals;
  (* swap: [comp_swap]((a.b)) = (swap . (b.a)) for every cons input *)
  List.iter (fun d -> match d with
    | VCons (a, b) ->
       Alcotest.(check valT_testable) "fp1 ri_min swap (exhaustive)"
         (pair (atom "'swap") (pair b a)) (run_via_ri comp_swap d)
    | _ -> ()) small_vals

(* fp1 for ri_seq, exhaustive over many op-lists x many cons inputs: the
 * residual must reversibly simulate running the whole op-sequence. *)
let test_fp1_seq_exhaustive () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let ri_seq  = Program2DataRwhile.program2data
                  (parse_file_program (examples_dir ^ "/ri_seq.rwhile")) in
  let oplist_data ops = List.fold_right (fun op acc -> pair (atom ("'" ^ op)) acc) ops VNil in
  let apply_op v = function
    | "swap" -> (match v with VCons (a, b) -> VCons (b, a) | _ -> v)
    | _      -> v in
  let apply_ops ops v = List.fold_left apply_op v ops in
  let oplists = [ []; ["id"]; ["swap"]; ["id";"swap"]; ["swap";"id"];
                  ["swap";"swap"]; ["id";"id"]; ["swap";"swap";"swap"] ] in
  let cons_inputs = List.map parse_val
    [ "('a . 'b)"; "(('a . 'b) . 'c)"; "('a . ('b . 'c))"; "(('a . 'b) . ('c . 'd))" ] in
  List.iter (fun ops ->
    let prog = oplist_data ops in
    let comp = EvalRwhile.evalProgram spec_av (spec_in ri_seq prog) in
    List.iter (fun d ->
      Alcotest.(check valT_testable) "fp1 ri_seq (exhaustive)"
        (pair prog (apply_ops ops d)) (run_via_ri comp d)) cons_inputs) oplists

(* PAT-WRITE-ITER unit test: the worklist write handles a NESTED (depth-2) cons
 * pattern that PAT-WRITE-STRUCT drops.  `cons (cons V1e V2e) St <= var0` with
 * var0 = ('C.((D var0).(S nil))) must split the dynamic top into V1e,V2e
 * (residualizing `cons V1e V2e <= var0`) and put the rest into St.  This is the
 * core of the fp1-via-ri_fp3 fix; it is not yet wired into the 'rep path (see
 * spec_av.rwhile note) pending ri_fp3's marker-pattern edge case. *)
let test_pat_write_iter_nested () =
  let store =
    "(('C . (('D . ('var . nil)) . ('S . nil))) . (('S . nil) . (('S . nil) . (('S . nil) . nil))))" in
  let cmd =
    "('cons . (('cons . (('var . (nil . nil)) . ('var . (nil . (nil . nil))))) . " ^
    "('var . (nil . (nil . (nil . nil))))))" in   (* pattern: cons (cons V1e V2e) St *)
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    ("read In; cons Vl Pr <= In; cons P WA <= Pr; PAT-WRITE-ITER(P, WA, RCode); " ^
     "Out <= cons Vl RCode; P ^= P; write Out") in
  (* WA = the AV at var0's slot = ('C.((D var0).(S nil))) *)
  let wa = "('C . (('D . ('var . nil)) . ('S . nil)))" in
  let input = pair (parse_val store) (pair (parse_val cmd) (parse_val wa)) in
  let out = EvalRwhile.evalProgram prog input in
  match out with
  | VCons (vl, rcode) ->
     Alcotest.(check (list valT_testable))
       "PAT-WRITE-ITER splits nested pattern (V1e,V2e dynamic; St gets rest; split residualized)"
       [parse_val "('D . ('var . (nil . nil)))";
        parse_val "('D . ('var . (nil . (nil . nil))))";
        parse_val "('S . nil)";
        parse_val "(('rep . (('cons . (('var . (nil . nil)) . ('var . (nil . (nil . nil))))) . ('var . nil))) . nil)"]
       [nth_slot vl 1; nth_slot vl 2; nth_slot vl 3; rcode]
  | _ -> Alcotest.fail "unexpected output shape"

(* DYNAMICIZE-ALL: make every slot dynamic self-ref, materialising static/partial
 * ones. Store: slot0=('S.'a) [materialise], slot1=('S.nil) [skip], slot2 dynamic
 * [skip].  Output (Vl' . RCode): all slots ('D.('var.k)); RCode = one rep
 * materialising slot0 (var0 <= 'a). *)
let test_dynamicize_all () =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read Vl; DYNAMICIZE-ALL(Vl, RCode); Out <= cons Vl RCode; write Out" in
  let input = parse_val
    "(('S . 'a) . (('S . nil) . (('D . ('var . (nil . (nil . nil)))) . nil)))" in
  let expected = parse_val
    ("((('D . ('var . nil)) . (('D . ('var . (nil . nil))) . " ^
     "(('D . ('var . (nil . (nil . nil)))) . nil))) . " ^
     "(('rep . (('var . nil) . ('val . 'a))) . nil))") in
  Alcotest.(check valT_testable) "dynamicize-all materialises static, marks all dynamic"
    expected (EvalRwhile.evalProgram prog input)

let test_ss_av_ass_static_exec () =
  (* var0 static-nil, "var0 ^= 'a" -> executed statically, slot ('S.'a), no residual *)
  check_spec_step_av "ass static execution"
    "(('S . nil) . nil)"
    "('ass . (('var . nil) . ('val . 'a)))"
    "((('S . 'a) . nil) . nil)"

let test_ss_av_ass_residualize () =
  (* var0 dynamic, "var0 ^= 'a" -> residualized as var0 ^= (val 'a) *)
  check_spec_step_av "ass residualize (dynamic var)"
    "(('D . ('var . nil)) . nil)"
    "('ass . (('var . nil) . ('val . 'a)))"
    "((('D . ('var . nil)) . nil) . (('ass . (('var . nil) . ('val . 'a))) . nil))"

let test_ss_av_ass_dynamic_expr () =
  (* var0 static-nil, "var0 ^= var1" with var1 dynamic -> residualized, var0 -> dynamic *)
  check_spec_step_av "ass dynamic expr promotes var"
    "(('S . nil) . (('D . ('var . (nil . nil))) . nil))"
    "('ass . (('var . nil) . ('var . (nil . nil))))"
    "((('D . ('var . nil)) . (('D . ('var . (nil . nil))) . nil)) . (('ass . (('var . nil) . ('var . (nil . nil)))) . nil))"

let test_ss_av_seq_static () =
  (* seq of two static assignments, both executed statically (no residual) *)
  check_spec_step_av "seq static execution"
    "(('S . nil) . nil)"
    "('seq . (('ass . (('var . nil) . ('val . 'a))) . ('ass . (('var . nil) . ('var . nil)))))"
    "((('S . nil) . nil) . nil)"

(* a conditional: if =? var0 'a then var1^='x else var1^='y fi ('val.nil) *)
let cond_cmd =
  "('cond . (('eq . (('var . nil) . ('val . 'a))) . (('ass . (('var . (nil . nil)) . ('val . 'x))) . (('ass . (('var . (nil . nil)) . ('val . 'y))) . (('val . nil) . nil)))))"
let test_ss_av_cond_static_true () =
  (* static test true: take then-branch statically, no residual cond *)
  check_spec_step_av "cond static true takes then"
    "(('S . 'a) . (('S . nil) . nil))" cond_cmd
    "((('S . 'a) . (('S . 'x) . nil)) . nil)"
let test_ss_av_cond_static_false () =
  check_spec_step_av "cond static false takes else"
    "(('S . 'b) . (('S . nil) . nil))" cond_cmd
    "((('S . 'b) . (('S . 'y) . nil)) . nil)"
let test_ss_av_cond_dynamic () =
  (* dynamic test: residualize whole cond (test lifted) AND dynamicize the store
   * (branches may modify any var). slot0 already dynamic, slot1 static-nil, so
   * no materialisation; both slots become dynamic self-refs, cond unchanged. *)
  check_spec_step_av "cond dynamic test residualized + store dynamicized"
    "(('D . ('var . nil)) . (('S . nil) . nil))" cond_cmd
    ("((('D . ('var . nil)) . (('D . ('var . (nil . nil))) . nil)) . (" ^ cond_cmd ^ " . nil))")

(* counting loop: from =? I nil do (var2 ^= nil) loop I <= cons nil I until =? I (nil.nil)
 * with I = var0, var2 = var index (nil.nil) *)
let loop_cmd =
  "('loop . (('eq . (('var . nil) . ('val . nil))) . (('ass . (('var . (nil . nil)) . ('val . nil))) . (('rep . (('var . nil) . ('cons . (('val . nil) . ('var . nil))))) . (('eq . (('var . nil) . ('val . (nil . nil)))) . nil)))))"
let test_ss_av_loop_static_unroll () =
  (* I static-nil: loop unrolls once (I -> (nil.nil)), no residual *)
  check_spec_step_av "loop static unroll"
    "(('S . nil) . (('S . nil) . (('S . nil) . nil)))" loop_cmd
    "((('S . (nil . nil)) . (('S . nil) . (('S . nil) . nil))) . nil)"
let test_ss_av_loop_dynamic () =
  (* I dynamic: residualize the whole loop (entry test lifted, == original here)
   * AND dynamicize the store (the body may modify any var). All slots are
   * dynamic/static-nil here, so no materialisation; all become dynamic. *)
  check_spec_step_av "loop dynamic residualized + store dynamicized"
    "(('D . ('var . nil)) . (('S . nil) . (('S . nil) . nil)))" loop_cmd
    ("((('D . ('var . nil)) . (('D . ('var . (nil . nil))) . (('D . ('var . (nil . (nil . nil)))) . nil))) . (" ^ loop_cmd ^ " . nil))")

(* var indices: X=0=nil, Y=1=(nil.nil), Z=2=(nil.(nil.nil)) *)
let rep_yzx = "('rep . (('cons . (('var . (nil . nil)) . ('var . (nil . (nil . nil))))) . ('var . nil)))"
let swap_cmd =
  "('seq . (('rep . (('cons . (('var . (nil . nil)) . ('var . (nil . (nil . nil))))) . ('var . nil))) . ('rep . (('var . nil) . ('cons . (('var . (nil . (nil . nil))) . ('var . (nil . nil))))))))"

let test_ss_av_rep_static () =
  (* cons Y Z <= X with X static ('a.'b): split, X consumed to ('S.nil), no residual *)
  check_spec_step_av "rep static split"
    "(('S . ('a . 'b)) . (('S . nil) . (('S . nil) . nil)))"
    rep_yzx
    "((('S . nil) . (('S . 'a) . (('S . 'b) . nil))) . nil)"

let test_ss_av_rep_input_split () =
  (* THE fp1 input split: cons V1 V2 <= V0 with V0 partially static
   * ('C.(('S.'a).('D.('var.0)))). V1 := static ('S.'a). V2's dynamic half is
   * ('D.('var.0)), which aliases var0 != V2's index (2); under the NO-ALIAS
   * invariant this re-homes: emit a runtime move `V2 <= V0` and set V2's slot to
   * the self-reference ('D.('var.2)). *)
  check_spec_step_av "rep partial-static input split (re-home)"
    "(('C . (('S . 'a) . ('D . ('var . nil)))) . (('S . nil) . (('S . nil) . nil)))"
    rep_yzx
    ("((('S . nil) . (('S . 'a) . (('D . ('var . (nil . (nil . nil)))) . nil))) . ("
     ^ "('rep . (('var . (nil . (nil . nil))) . ('var . nil))) . nil))")

let test_ss_av_swap_static () =
  (* full swap of a static (a.b) -> static (b.a), fully executed, no residual *)
  check_spec_step_av "swap static fully executed"
    "(('S . ('a . 'b)) . (('S . nil) . (('S . nil) . nil)))"
    swap_cmd
    "((('S . ('b . 'a)) . (('S . nil) . (('S . nil) . nil))) . nil)"

let test_ss_av_swap_dynamic () =
  (* full swap of a dynamic X (structural Stage-C 'rep): the first rep
   * `cons Y Z <= X` cannot split a pure-dynamic X reversibly, so it RESIDUALIZES
   * (== rep_yzx) and makes Y,Z dynamic; the second rep `X <= cons Z Y` then
   * rebinds X to the partial cons ('C.((D Z).(D Y))) with no residual. So the
   * store ends X=('C.((D var2).(D var1))), Y=Z=('S.nil), and RCode=[rep_yzx]. *)
  (* UPDATED 2026-08-08 for capture-on-escape.  The two halves are now CAPTURED
     as they escape into the compound, so X refers to two freshly allocated temps
     rather than to slots 2 and 1, and RCode carries the two captures in front of
     the residualized split.  Asserting the SHAPE rather than a golden literal:
     what matters is that X is a structural cons of two DISTINCT dynamic
     references (no aliasing -- constraint C1), not which indices they got. *)
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; cons Vl Cmd <= In; SPEC-CMD-AV(Cmd); Out <= cons Vl RCode; write Out" in
  let out = EvalRwhile.evalProgram prog
    (pair (parse_val "(('D . ('var . nil)) . (('S . nil) . (('S . nil) . nil)))")
          (parse_val swap_cmd)) in
  (match out with
   | VCons (VCons (xslot, VCons (y, VCons (z, VNil))), rcode) ->
      Alcotest.(check bool)
        "X = ('C.((D var i).(D var j))) with i <> j (distinct captures, no alias)"
        true
        (match xslot with
         | VCons (VAtom (Atom "'C"),
                  VCons (VCons (VAtom (Atom "'D"), VCons (VAtom (Atom "'var"), i)),
                         VCons (VAtom (Atom "'D"), VCons (VAtom (Atom "'var"), j)))) ->
            unary_to_int i >= 0 && unary_to_int j >= 0 && i <> j
         | _ -> false);
      Alcotest.(check valT_testable) "Y is static nil" (parse_val "('S . nil)") y;
      Alcotest.(check valT_testable) "Z is static nil" (parse_val "('S . nil)") z;
      let rec len = function VCons (_, t) -> 1 + len t | _ -> 0 in
      Alcotest.(check int)
        "RCode = the residualized split plus the two captures" 3 (len rcode);
      Alcotest.(check bool) "the residualized split is still there" true
        (let rec mem = function
           | VCons (h, t) -> h = parse_val rep_yzx || mem t
           | _ -> false in mem rcode)
   | _ -> Alcotest.fail "spec step returned an unexpected shape")

(* ===== fp1 residual assembly (Stage C, C2) =====
 * End-to-end: specialize a command with a dynamic input via SPEC-CMD-AV, then
 * ASSEMBLE-FP1 turns (Vl . RCode) into a residual program; running that residual
 * (via ri.rwhile) must reproduce the command's effect. Validates that the
 * structural 'rep (C1) + assembly (C2) yield ONE correct reversible residual. *)
(* AV-INIT builds an N-slot store of static-nil AVs. *)
let test_av_init () =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    "read In; AV-INIT(In, Vl); Out <= cons Vl In; write Out" in
  (* N = 3 = (nil.(nil.(nil.nil))); expect Vl = three ('S.nil) slots *)
  let out = EvalRwhile.evalProgram prog (parse_val "(nil . (nil . (nil . nil)))") in
  Alcotest.(check valT_testable) "AV-INIT 3 -> three static-nil slots"
    (parse_val "((('S . nil) . (('S . nil) . (('S . nil) . nil))) . (nil . (nil . (nil . nil))))")
    out

let test_assemble_fp1_swap () =
  let prog = parse_macro_harness (examples_dir ^ "/spec_av.rwhile")
    ("read In; cons Vl Cmd <= In; SPEC-CMD-AV(Cmd); "
     ^ "ASSEMBLE-FP1(IIv, JJv, CompSrc); RCode ^= RCode; Vl ^= Vl; "
     ^ "Out <= CompSrc; write Out") in
  (* X=var0 dynamic, Y=var1, Z=var2 static-nil; read/write var = X (index 0=nil). *)
  let vl = parse_val "(('D . ('var . nil)) . (('S . nil) . (('S . nil) . nil)))" in
  let compsrc = EvalRwhile.evalProgram prog (pair vl (parse_val swap_cmd)) in
  (* run the assembled residual on ('a.'b): must yield the swap ('b.'a) *)
  let result = run_via_ri compsrc (parse_val "('a . 'b)") in
  Alcotest.(check valT_testable)
    "assembled fp1 residual for dynamic swap computes swap"
    (parse_val "('b . 'a)") result

(* fp1 main end-to-end on a small program: specialize Q=swap (reads/writes V0)
 * w.r.t. a static first input component 'a; the residual must still swap, so
 * [comp]('b) = ('b.'a). Q in p2d form = (('var.0) . (swap_body . ('var.0))). *)
let test_fp1_main_swap () =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let q = parse_val ("(('var . nil) . (" ^ swap_cmd ^ " . ('var . nil)))") in
  let comp = EvalRwhile.evalProgram spec_av (spec_in q (atom "'a")) in
  let result = run_via_ri comp (atom "'b") in
  Alcotest.(check valT_testable) "fp1(swap,'a): [comp]('b) = ('b.'a)"
    (parse_val "('b . 'a)") result

(* ===== fp1 round-trip ladder: localize the residual-correctness error source =====
 * comp = [spec_av]((P . Src)); then run comp via ri on a dynamic input d.
 * Correct iff [comp](d) = [P]((Src.d)). The first rung that fails pinpoints the
 * triggering pattern. Var indices: V0=nil, V1=(nil.nil), V2=(nil.(nil.nil)),
 * V3=(nil.(nil.(nil.nil))). *)
let fp1_roundtrip p_str src_str d =
  let spec_av = parse_file_program (examples_dir ^ "/spec_av.rwhile") in
  let comp = EvalRwhile.evalProgram spec_av (spec_in (parse_val p_str) (parse_val src_str)) in
  run_via_ri comp d

(* rung 1: split V0 into V1,V2 then rejoin into V0 (= identity on a pair).
 * Same-variable I/O (read=write=V0); no cross-variable dynamic move. *)
let p_split_rejoin =
  "(('var . nil) . (" ^
  "('seq . (" ^
    "('rep . (('cons . (('var.(nil.nil)) . ('var.(nil.(nil.nil))))) . ('var.nil))) . " ^
    "('rep . (('var.nil) . ('cons . (('var.(nil.nil)) . ('var.(nil.(nil.nil)))))))" ^
  "))" ^
  " . ('var . nil)))"
let test_fp1_split_rejoin () =
  Alcotest.(check valT_testable) "fp1(split-rejoin,'a): [comp]('d) = ('a.'d)"
    (parse_val "('a . 'd)") (fp1_roundtrip p_split_rejoin "'a" (atom "'d"))

(* rung 2 (the no-alias fix target): move the dynamic half to a DIFFERENT variable
 * (V3^=V2), reversibly clear the source (V2^=V3, since V3=V2), then rejoin from V3.
 * Identity on a pair, but it forces a cross-variable dynamic move. Before the
 * no-alias fix this produced a non-reversible residual (input var not consumed,
 * because V2 aliased a different variable). With PAT-WRITE-LEAF-REHOME the split
 * emits a runtime move so V2 owns its value; the residual is correct and
 * [comp]('d) = ('a.'d).  (A self-clear V2^=V2 here would be correct directly but
 * is irreversible, which ri.rwhile cannot self-interpret — so the reversible
 * clear V2^=V3 is used.) *)
let p_move_clear_rejoin =
  "(('var . nil) . (" ^
  "('seq . (" ^
    "('rep . (('cons . (('var.(nil.nil)) . ('var.(nil.(nil.nil))))) . ('var.nil))) . " ^
    "('seq . (" ^
      "('ass . (('var.(nil.(nil.(nil.nil)))) . ('var.(nil.(nil.nil))))) . " ^
      "('seq . (" ^
        "('ass . (('var.(nil.(nil.nil))) . ('var.(nil.(nil.(nil.nil)))))) . " ^
        "('rep . (('var.nil) . ('cons . (('var.(nil.nil)) . ('var.(nil.(nil.(nil.nil))))))))" ^
      "))" ^
    "))" ^
  "))" ^
  " . ('var . nil)))"
let test_fp1_move_clear () =
  Alcotest.(check valT_testable)
    "fp1(cross-var move+reversible clear,'a): [comp]('d) = ('a.'d)  (no-alias fix)"
    (parse_val "('a . 'd)") (fp1_roundtrip p_move_clear_rejoin "'a" (atom "'d"))

(* ===== The genuine first Futamura projection via spec_av + ri_fp3 =====
 * comp = [spec_av]((ri_fp3 . src)) specializes the self-interpreter ri_fp3
 * w.r.t. a static source program src; the residual is the "compiled" src:
 *   [comp](d) = [ri_fp3]((src . d)) = (src . [src](d)).
 * This is the payoff of the no-alias fix + ri_fp3's reversible clears: the
 * residual must be self-interpretable via ri.rwhile (no irreversible X^=X). *)
(* Regression for ri_fp3's reversible clears (candidate C): ri_fp3 must still
 * self-interpret correctly after replacing the irreversible V1^=V1; V2^=V2
 * copy-then-clear with reversible pattern-moves (Prog <= V1; Data <= V2).
 *   [ri_fp3]((src . d)) = (src . [src](d)).
 * NOTE: the genuine fp1 [[spec_av]((ri_fp3.src))] is NOT yet green — the
 * spec_av specialization of ri_fp3 still produces a semantically wrong residual
 * (the interpreted operation is dropped and the static src-echo is corrupted);
 * that is a separate, deeper specializer bug, tracked in plan_fp1_stage_c.md.
 * Candidate C's win is that the residual now RUNS via ri (no irreversible
 * X^=X), which it previously could not. *)
let ri_fp3_selfinterp src_name d =
  let ri_fp3 = parse_file_program (examples_dir ^ "/ri_fp3.rwhile") in
  let src = parse_file_program (examples_dir ^ "/" ^ src_name ^ ".rwhile") in
  let src_data = Program2DataRwhile.program2data src in
  let r = EvalRwhile.evalProgram ri_fp3 (pair src_data d) in
  let direct = EvalRwhile.evalProgram src d in
  (r, pair src_data direct)

let test_ri_fp3_selfinterp_id () =
  let r, expected = ri_fp3_selfinterp "id" (atom "'a") in
  Alcotest.(check valT_testable) "[ri_fp3]((id.'a)) = (id.'a)" expected r

let test_ri_fp3_selfinterp_swap () =
  let r, expected = ri_fp3_selfinterp "swap" (parse_val "('a . 'b)") in
  Alcotest.(check valT_testable) "[ri_fp3]((swap.('a.'b))) = (swap.('b.'a))" expected r

(* ===== Test runner ===== *)

(* ===== Core IR abstraction layer (Core.ml) =====
 * The Core IR mirrors the Agda-verified model; these tests check that (a) it
 * AGREES with the real evaluator (so elaboration is faithful) and (b) its
 * inversion is involutive and reverses execution (the Agda theorems, in the
 * implementation). *)
let check_core_agrees name prog_str input_str =
  let p = parse_program prog_str in
  let v = parse_val input_str in
  Alcotest.(check valT_testable) name
    (EvalRwhile.evalProgram p v) (Core.eval_program_core p v)

let core_swap_prog = "read X; cons Y Z <= X; X <= cons Z Y; write X"
let core_rev_prog  =
  "read Y; from =? X nil loop cons Z Y <= Y; X <= cons Z X until =? Y nil; write X"
let core_cond_prog =
  "read X; cons A B <= X; if =? A 'p then B ^= 'q else B ^= 'r fi =? B 'q; X <= cons A B; write X"

let test_core_agree_swap () = check_core_agrees "core = eval (swap)" core_swap_prog "('a . 'b)"
let test_core_agree_reverse () =
  check_core_agrees "core = eval (reverse/loop)" core_rev_prog "('a . ('b . ('c . nil)))"
let test_core_agree_cond_then () = check_core_agrees "core = eval (cond then)" core_cond_prog "('p . nil)"
let test_core_agree_cond_else () = check_core_agrees "core = eval (cond else)" core_cond_prog "('x . nil)"
let core_list_prog = "read X; [A, B] <= X; X <= [B, A]; write X"   (* exercises EList/PList normalization *)
let test_core_agree_list () = check_core_agrees "core = eval (list sugar)" core_list_prog "('a . ('b . nil))"

let core_body prog_str =
  let AbsRwhile.Prog (_, _, c, _) = MacroRwhile.expMacProgram (parse_program prog_str) in
  Core.elaborate c

let test_core_inv_involution () =
  List.iter (fun ps ->
    let cr = core_body ps in
    Alcotest.(check bool) ("inv_core involution: " ^ ps) true (Core.inv_core (Core.inv_core cr) = cr))
    [core_swap_prog; core_rev_prog; core_cond_prog]

let test_core_reversible_swap () =
  let p  = parse_program core_swap_prog in
  let cr = core_body core_swap_prog in
  let s0 = EvalRwhile.rupdate (AbsRwhile.RIdent "X", parse_val "('a . 'b)")
             (store_of_list (List.map (fun z -> (z, AbsRwhile.VNil))
                       (EvalRwhile.varProgram (MacroRwhile.expMacProgram p)))) in
  let t  = Core.eval_core s0 cr in
  let s' = Core.eval_core t (Core.inv_core cr) in
  Alcotest.(check bool) "core inv_core reverses the store" true
    (EvalRwhile.RIdentMap.equal (=) s' s0)

(* N1 (AGDA_CORRESPONDENCE.md, gap G2): the Agda model proves Core's elaboration
 * and normalization semantics-preserving (RWhileCoreExp / RWhileElabCom).  This
 * battery certifies, across the whole example corpus, that the OCaml Core.ml
 * really computes the same function as EvalRwhile -- so "Core.ml mirrors the
 * verified core" is checked on real programs (incl. the self-interpreter), not
 * just the few core-ir smoke tests. *)
let check_core_file name prog_file data_file =
  let p = parse_file_program (examples_dir ^ "/" ^ prog_file) in
  let v = parse_file_val (examples_dir ^ "/" ^ data_file) in
  Alcotest.(check valT_testable) name
    (EvalRwhile.evalProgram p v) (Core.eval_program_core p v)

let test_core_equiv_corpus () =
  List.iter (fun (n, pf, df) -> check_core_file n pf df)
    [ "rep",         "rep.rwhile",         "list123.val";
      "length",      "length.rwhile",      "list123.val";
      "compare",     "compare.rwhile",     "compare0.val";
      "minus",       "minus.rwhile",       "minus.val";
      "rle0",        "rle.rwhile",         "rle0.val";
      "rle1",        "rle.rwhile",         "rle1.val";
      "enumeration", "enumeration.rwhile", "nil.val" ]

(* The full self-interpreter ri.rwhile (macros, cons/hd/tl/=?/pair?, loops, case)
 * run on p2d-encoded programs -- the most complex Core==eval check. *)
let test_core_equiv_selfinterp () =
  List.iter (fun (n, pf, df) -> check_core_file n pf df)
    [ "ri id_and_nil",          "ri.rwhile", "id_and_nil.p_val";
      "ri reverse_and_list123", "ri.rwhile", "reverse_and_list123.p_val";
      "ri piorder",             "ri.rwhile", "piorder.p_val" ]

(* ===== Structured sugar (Desugar.ml): skip / assert / <-> / local / for =====
 *
 * All five forms are desugared away BEFORE macro expansion, evaluation,
 * inversion and program-to-data, so nothing downstream -- in particular the
 * self-interpreter ri.rwhile and the specialiser spec_av.rwhile -- needs to know
 * about them.  These tests pin (a) the semantics of each form, (b) that a
 * for-counter is loop-LOCAL so the store invariant survives (a program that ends
 * with a non-nil variable is rejected by all_cleared, so merely completing is
 * the check), (c) that inversion stays cost-preserving through the sugar, and
 * (d) that a sugared program self-interprets to the same answer. *)

(* evaluate, and also return the executed-command-node count (./ri -steps) *)
let eval_with_steps prog_str val_str =
  EvalRwhile.reset_steps ();
  let out = eval_string prog_str val_str in
  (out, EvalRwhile.get_steps ())

let fails f = try ignore (f ()); false with Failure _ -> true

let test_sugar_skip () =
  let (out, n) = eval_with_steps "read X; skip; write X" "'a" in
  Alcotest.(check valT_testable) "skip is the identity" (atom "'a") out;
  (* skip is  if 't fi 't : exactly one executed command node *)
  Alcotest.(check int) "skip costs one step" 1 n

let test_sugar_assert () =
  Alcotest.(check valT_testable) "assert with a true test is a no-op"
    (atom "'a") (eval_string "read X; assert =? X X; write X" "'a");
  (* a false test takes the else branch, where the exit assertion 't fails *)
  Alcotest.(check bool) "assert with a false test fails" true
    (fails (fun () -> eval_string "read X; assert =? X 'zzz; write X" "'a"))

let test_sugar_swap () =
  Alcotest.(check valT_testable) "X <-> Y exchanges two variables"
    (VCons (atom "'a", atom "'c"))
    (eval_string "read X; Y ^= 'a; X <-> Y; Z <= cons X Y; write Z" "'c");
  (* Same condition as push/pop: `cons X X <= cons X X` reads X twice.  The
     interpreter already warned about the non-linear pattern yet accepted it,
     while `push X X` was rejected -- an inconsistency, closed 2026-08-06. *)
  Alcotest.(check bool) "X <-> X is rejected" true
    (try ignore (eval_string "read X; K <-> K; Out <= X; write Out" "'a"); false
     with Desugar.Desugar_error _ -> true)

let test_sugar_local () =
  (* T is set to 'b, mutated to 'c by the swap, and cleared by delocal T = 'c *)
  Alcotest.(check valT_testable) "local/delocal brackets a scratch variable"
    (atom "'b")
    (eval_string "read X; local T = 'b in T <-> X delocal T = 'c end; write X" "'c");
  Alcotest.(check bool) "a delocal whose value is wrong fails" true
    (fails (fun () ->
       eval_string "read X; local T = 'b in T <-> X delocal T = 'b end; write X" "'c"))

(* The two `assert (=? X nil)` guards a local/delocal expands to are NOT
   defensive decoration.  `X ^= E` is an XOR update: when X already holds E's
   value it CLEARS X, so without the entry guard the body silently runs with
   X = nil and the closing assignment restores the old value -- a wrong answer
   with no error anywhere.  The exit guard rules out the mirror case, where the
   body has cleared X and the closing assignment sets it instead. *)
let test_sugar_local_guards () =
  let prog = "read X; local X = 'b in Y ^= X delocal X = 'b end; \
              Z <= cons X Y; write Z" in
  (* entering with X = nil is the intended use: the body really sees X = 'b *)
  Alcotest.(check valT_testable) "the body sees the bound value"
    (VCons (VNil, atom "'b")) (eval_string prog "nil");
  (* entering with X already bound to 'b used to return ('b . nil) silently *)
  Alcotest.(check bool) "entering with X already bound is rejected" true
    (fails (fun () -> eval_string prog "'b"));
  (* the body clears T, so the closing T ^= 'b would SET it and leak a non-nil
     variable out of the block *)
  Alcotest.(check bool) "a body that clears the local is rejected" true
    (fails (fun () -> eval_string
       "read In; local T = 'b in T <-> Q delocal T = 'b end; Q ^= 'b; write In" "'b"));
  (* same guard on a for-counter *)
  Alcotest.(check bool) "entering a for with a bound counter is rejected" true
    (fails (fun () -> eval_string
       "read I; for I = nil to (nil.nil) do Y <= cons 'q Y end; \
        Z <= cons I Y; write Z" "'b"));
  (* the message names the assertion the user wrote, not the 't scaffolding *)
  Alcotest.(check bool) "the error names the failing assertion" true
    (try ignore (eval_string prog "'b"); false
     with Failure m -> find_substring m "=? X nil" <> None)

let test_sugar_local_name_mismatch () =
  Alcotest.(check bool) "local and delocal must name the same variable" true
    (try ignore (eval_string
                   "read X; local T = 'b in skip delocal U = 'b end; write X" "'a");
         false
     with Desugar.Desugar_error _ -> true)

let test_sugar_for () =
  (* the counter takes nil, (nil.nil), (nil.(nil.nil)) -- three iterations -- and
     is cleared again afterwards, otherwise all_cleared would reject the run *)
  Alcotest.(check valT_testable) "for runs the body once per counter value"
    (parse_val "('a . ('a . ('a . nil)))")
    (eval_string
       "read X; for I = nil to (nil.(nil.nil)) do X <= cons 'a X end; write X" "nil");
  Alcotest.(check valT_testable) "for A to A runs the body exactly once"
    (parse_val "('a . nil)")
    (eval_string "read X; for I = nil to nil do X <= cons 'a X end; write X" "nil");
  (* A body that touches the counter makes the loop's own tests see a value the
     body changed, so it silently runs a DIFFERENT number of times and the
     counter leaks out.  Measured before the check existed: adding `I <-> K` to
     a two-iteration body made it run THREE times, left K holding the counter,
     and raised no error.  Rejected at desugar time now. *)
  (* `for I = nil to I` has the exit test `=? I I`, trivially true, so the loop
     silently ran the body exactly ONCE however it was written.  (The mirror
     case `for I = I to B` errored on the loop's reversibility assertion, which
     is how the asymmetry was noticed.)  Both are rejected now. *)
  Alcotest.(check bool) "an upper bound mentioning the counter is rejected" true
    (try ignore (eval_string
       "read X; for I = nil to I do R <= cons 'q R end; Out <= cons X R; write Out" "'a");
         false
     with Desugar.Desugar_error _ -> true);
  Alcotest.(check bool) "a lower bound mentioning the counter is rejected" true
    (try ignore (eval_string
       "read X; for I = I to (nil.nil) do R <= cons 'q R end; Out <= cons X R; write Out" "'a");
         false
     with Desugar.Desugar_error _ -> true);
  Alcotest.(check bool) "a body that mentions the counter is rejected" true
    (try ignore (eval_string
       "read X; for I = nil to (nil.nil) do I <-> K; R <= cons 'q R end; \
        Out <= cons I (cons K R); write Out" "nil");
         false
     with Desugar.Desugar_error _ -> true)

(* `FOR-T-1` is a legal RIdent, so a program may already use it.  The scratch the
   for-counter increment needs must dodge whatever the program mentions rather
   than silently sharing a name -- which used to fail deep inside the increment
   with `error in update: var=FOR-T-1 ...` and no hint of the cause. *)
let test_sugar_for_scratch_fresh () =
  let clashing = "read In; FOR-T-1 ^= 'x; \
                  for I = nil to (nil.nil) do R <= cons 'q R end; \
                  FOR-T-1 ^= 'x; Out <= R; write Out" in
  Alcotest.(check valT_testable) "a user variable named FOR-T-1 is not clobbered"
    (parse_val "('q . ('q . nil))") (eval_string clashing "nil");
  Alcotest.(check bool) "the scratch prefix was lengthened" true
    (find_substring (show_program (Desugar.desugar_program (parse_program clashing)))
       "FOR-T'-" <> None);
  (* a program without such a variable keeps the plain prefix, so nothing that
     already worked changes shape or step count.  (Only the prefix is pinned:
     the counter is global and keeps climbing across desugarings, so the number
     that follows it is not stable within one process.) *)
  let plain = show_program (Desugar.desugar_program (parse_program
    "read In; for I = nil to (nil.nil) do R <= cons 'q R end; \
     Out <= R; write Out")) in
  Alcotest.(check bool) "otherwise the plain prefix is used" true
    (find_substring plain "FOR-T-" <> None);
  Alcotest.(check bool) "and it is not lengthened needlessly" true
    (find_substring plain "FOR-T'-" = None)

let test_sugar_push_pop () =
  (* pop/push move an element from one stack to the other: a list reversal *)
  let prog = parse_file_program (examples_dir ^ "/stack_reverse.rwhile") in
  let input = parse_file_val (examples_dir ^ "/list123.val") in
  Alcotest.(check valT_testable) "push/pop reverse a list"
    (parse_val "('3 . ('2 . ('1 . nil)))") (EvalRwhile.evalProgram prog input);
  (* popping something that is not a cons fails *)
  Alcotest.(check bool) "pop on a non-cons fails" true
    (fails (fun () -> eval_string "read S; pop V S; V ^= V; write S" "'a"));
  (* the two names must differ, or the pattern would read S twice *)
  Alcotest.(check bool) "push X X is rejected" true
    (try ignore (eval_string "read S; push S S; write S" "'a"); false
     with Desugar.Desugar_error _ -> true)

let test_sugar_push_pop_inverse () =
  (* inverting a replacement swaps its patterns, so push and pop map onto each
     other with no inversion rule of their own *)
  let pushp = parse_program "read S; push V S; write T"
  and popp  = parse_program "read T; pop V S; write S" in
  Alcotest.(check program_testable) "inv (push V S) = pop V S"
    (Desugar.desugar_program popp) (InvRwhile.invProgram pushp);
  Alcotest.(check program_testable) "inv (pop V S) = push V S"
    (Desugar.desugar_program pushp) (InvRwhile.invProgram popp)

let test_sugar_inverse_cost () =
  let prog = parse_file_program (examples_dir ^ "/sugar.rwhile") in
  let input = parse_val "'c" in
  EvalRwhile.reset_steps ();
  let out = EvalRwhile.evalProgram prog input in
  let fwd = EvalRwhile.get_steps () in
  Alcotest.(check valT_testable) "sugar.rwhile forward"
    (VCons (atom "'a", atom "'p")) out;
  EvalRwhile.reset_steps ();
  let back = EvalRwhile.evalProgram (InvRwhile.invProgram prog) out in
  let bwd = EvalRwhile.get_steps () in
  Alcotest.(check valT_testable) "the inverse restores the input" input back;
  Alcotest.(check int) "inversion preserves the step count" fwd bwd

let test_sugar_via_ri () =
  let prog = parse_program
    "read X; Y ^= 'a; X <-> Y; skip; Z <= cons X Y; write Z" in
  let input = parse_val "'c" in
  let direct = EvalRwhile.evalProgram prog input in
  Alcotest.(check valT_testable) "sugar self-interprets to the same answer"
    direct (run_via_ri (Program2DataRwhile.program2data prog) input)

(* ===== R-WHILE-S compiler (Optimize.ml) =====
 *
 * Pass 1 numbers a program's variables by static access weight instead of first
 * occurrence.  The self-interpreter's store is a list indexed by that number, so
 * a lookup of variable i walks i cells; putting the hot ones first shortens
 * every walk.  It is a pure renaming, so the only thing that may change is the
 * step count -- never the answer.  Measured here: 2-10% fewer SI steps, more for
 * programs with more variables (compare, 8 variables, 10%). *)

let with_hot_vars (f : unit -> 'a) : 'a =
  let old = !Program2DataRwhile.hot_vars in
  Program2DataRwhile.hot_vars := true;
  let r = (try f () with e -> Program2DataRwhile.hot_vars := old; raise e) in
  Program2DataRwhile.hot_vars := old; r

let test_hot_vars_same_answer () =
  let check name valfile =
    let prog = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
    let input = parse_file_val (examples_dir ^ "/" ^ valfile) in
    let direct = EvalRwhile.evalProgram prog input in
    let d = with_hot_vars (fun () -> Program2DataRwhile.program2data prog) in
    Alcotest.(check valT_testable)
      (name ^ ": hot-vars numbering self-interprets to the same answer")
      direct (run_via_ri d input) in
  check "reverse" "list123.val";
  check "length"  "list123.val";
  check "minus"   "minus.val"

let test_hot_vars_permutation () =
  let prog = MacroRwhile.expMacProgram
      (parse_file_program (examples_dir ^ "/compare.rwhile")) in
  let base = EvalRwhile.varProgram prog in
  let hot  = Optimize.var_order prog in
  Alcotest.(check int) "no variable gained or lost"
    (List.length base) (List.length hot);
  Alcotest.(check bool) "the same set of variables" true
    (List.for_all (fun v -> List.mem v hot) base
     && List.for_all (fun v -> List.mem v base) hot);
  (* deterministic: ties keep first-occurrence order, so re-running agrees *)
  Alcotest.(check bool) "deterministic" true (hot = Optimize.var_order prog)

(* Access-weight numbering is the DEFAULT since 2026-08-06, and the old
   first-occurrence numbering is still reachable through -first-occurrence-vars.
   Both encodings are pinned, so a change to either is deliberate. *)
let test_var_numbering_default () =
  Alcotest.(check bool) "access-weight numbering is on by default" true
    !Program2DataRwhile.hot_vars;
  let prog = parse_file_program (examples_dir ^ "/reverse.rwhile") in
  Alcotest.(check valT_testable) "default encoding"
    (parse_file_val (examples_dir ^ "/reverse.val"))
    (Program2DataRwhile.program2data prog);
  let old = !Program2DataRwhile.hot_vars in
  Program2DataRwhile.hot_vars := false;
  let d = (try Program2DataRwhile.program2data prog
           with e -> Program2DataRwhile.hot_vars := old; raise e) in
  Program2DataRwhile.hot_vars := old;
  Alcotest.(check valT_testable) "-first-occurrence-vars reproduces the old one"
    (parse_file_val (examples_dir ^ "/reverse_first_occurrence.val")) d

(* Pass 2 (Optimize.slot_alloc): variables whose live ranges are disjoint share
   one store slot.  Sound because an R-WHILE variable is nil before its first
   occurrence and nil after its last (it starts nil, can only change at its own
   occurrences, and all_cleared forces it back to nil) -- with loops widened to
   their whole extent, since a loop-carried variable is non-nil between
   iterations.  Conditional arms are alternatives, which is where the win is.
   Measured: spec 155->119 slots (23%), spec_av_rev 233->198, spec_av 219->193;
   loop-dominated programs share nothing, correctly. *)

let with_share_slots (f : unit -> 'a) : 'a =
  let old = !Program2DataRwhile.share_slots in
  Program2DataRwhile.share_slots := true;
  let r = (try f () with e -> Program2DataRwhile.share_slots := old; raise e) in
  Program2DataRwhile.share_slots := old; r

let test_share_slots_same_answer () =
  let check name valfile =
    let prog = parse_file_program (examples_dir ^ "/" ^ name ^ ".rwhile") in
    let input = parse_file_val (examples_dir ^ "/" ^ valfile) in
    let direct = EvalRwhile.evalProgram prog input in
    let d = with_share_slots (fun () -> Program2DataRwhile.program2data prog) in
    Alcotest.(check valT_testable)
      (name ^ ": slot sharing self-interprets to the same answer")
      direct (run_via_ri d input) in
  check "reverse" "list123.val";
  check "length"  "list123.val";
  check "minus"   "minus.val";
  check "compare" "compare1.val"

(* scratch confined to opposite arms of a conditional is never live together, so
   it collapses onto one slot; the answer must not change *)
let test_share_slots_branches () =
  let src = "read In;              if 't then A1 ^= 'a; A1 ^= 'a; A2 ^= 'a; A2 ^= 'a              else B1 ^= 'b; B1 ^= 'b; B2 ^= 'b; B2 ^= 'b fi 't;              write In" in
  let prog = parse_program src in
  let expanded = MacroRwhile.expMacProgram prog in
  let nvars = List.length (EvalRwhile.varProgram expanded) in
  let slots = List.length
      (List.sort_uniq compare (List.map snd (Optimize.slot_alloc expanded))) in
  Alcotest.(check bool) "the two arms' scratch shares slots" true (slots < nvars);
  let input = parse_val "'q" in
  let d = with_share_slots (fun () -> Program2DataRwhile.program2data prog) in
  Alcotest.(check valT_testable) "and the answer is unchanged"
    (EvalRwhile.evalProgram prog input) (run_via_ri d input)

(* a loop-carried variable must NOT be merged with one used later in the same
   loop body: widening every interval that meets a loop is what prevents it *)
let test_share_slots_loop_widening () =
  let prog = MacroRwhile.expMacProgram
      (parse_file_program (examples_dir ^ "/reverse.rwhile")) in
  let nvars = List.length (EvalRwhile.varProgram prog) in
  let slots = List.length
      (List.sort_uniq compare (List.map snd (Optimize.slot_alloc prog))) in
  Alcotest.(check int) "a loop-dominated program shares nothing" nvars slots

(* Slot sharing was once judged to have "essentially no realised benefit" -- a
   judgement made from seven loop-dominated examples, where it correctly shares
   nothing.  Measured across every example in the repository (2026-08-06) it
   reduces slots on SIXTEEN of them, and examples/sugar.rwhile self-interprets
   in 8102 steps instead of 9192 (-11%) with the same answer.  This pins the
   reduction so the judgement cannot silently drift back. *)
let test_share_slots_pays_off () =
  let prog = MacroRwhile.expMacProgram
      (parse_file_program (examples_dir ^ "/sugar.rwhile")) in
  let nvars = List.length (EvalRwhile.varProgram prog) in
  let slots = List.length
      (List.sort_uniq compare (List.map snd (Optimize.slot_alloc prog))) in
  Alcotest.(check bool)
    (Printf.sprintf "sugar.rwhile: %d variables collapse onto fewer slots" nvars)
    true (slots < nvars);
  (* and the answer is unchanged through the self-interpreter *)
  let input = parse_file_val (examples_dir ^ "/atom_c.val") in
  let d = with_share_slots (fun () ->
      Program2DataRwhile.program2data
        (parse_file_program (examples_dir ^ "/sugar.rwhile"))) in
  Alcotest.(check valT_testable) "and the answer is unchanged"
    (EvalRwhile.evalProgram
       (parse_file_program (examples_dir ^ "/sugar.rwhile")) input)
    (run_via_ri d input)

let test_share_slots_off_by_default () =
  Alcotest.(check bool) "share_slots defaults to off" false
    !Program2DataRwhile.share_slots

(* Pass 3 (Optimize.order_static_last): the variables the caller declares STATIC
   are numbered last, so the dynamic ones -- the only ones that survive into a
   residual -- get the short unary indices.  Measured over all 120 numberings of
   ri_min: the fp1 residual for swap ranges 83..115 nodes purely from numbering,
   and the mean falls exactly 5 nodes for each position the one static variable
   moves later (109.0 / 104.0 / 99.0 / 94.0 / 89.0).  Marking Op static takes
   the swap residual 103 -> 87 nodes (0.63x -> 0.51x of |ri_min|) and id 63 -> 55,
   still round-tripping. *)
let test_static_vars_last () =
  let prog = MacroRwhile.expMacProgram
      (parse_file_program (examples_dir ^ "/ri_min.rwhile")) in
  let vs = Optimize.var_order prog in
  let ordered = Optimize.order_static_last [RIdent "Op"] vs in
  Alcotest.(check bool) "the static variable is numbered last" true
    (match List.rev ordered with RIdent "Op" :: _ -> true | _ -> false);
  Alcotest.(check int) "still a permutation" (List.length vs) (List.length ordered);
  Alcotest.(check bool) "of the same variables" true
    (List.for_all (fun v -> List.mem v ordered) vs
     && List.for_all (fun v -> List.mem v vs) ordered)

let test_static_vars_same_answer () =
  let prog = parse_file_program (examples_dir ^ "/reverse.rwhile") in
  let input = parse_file_val (examples_dir ^ "/list123.val") in
  let direct = EvalRwhile.evalProgram prog input in
  let old = !Program2DataRwhile.static_vars in
  Program2DataRwhile.static_vars := ["X"];
  let d = (try Program2DataRwhile.program2data prog
           with e -> Program2DataRwhile.static_vars := old; raise e) in
  Program2DataRwhile.static_vars := old;
  Alcotest.(check valT_testable)
    "static-vars numbering self-interprets to the same answer"
    direct (run_via_ri d input)

(* RWHILE_HYGIENIC=1 ./test-suite runs the WHOLE suite with -hygienic-macros on,
   used to verify that the core programs (spec/ri/spec_av) are hygiene-clean.
   The hygiene-specific group below already toggles the flag per-test, so it is
   unaffected. *)
let () =
  if Sys.getenv_opt "RWHILE_HYGIENIC" <> None then MacroRwhile.hygienic := true

let () =
  Alcotest.run "R-WHILE Interpreter" [
    "core-ir", [
      Alcotest.test_case "Core agrees with eval: swap" `Quick test_core_agree_swap;
      Alcotest.test_case "Core agrees with eval: reverse (loop)" `Quick test_core_agree_reverse;
      Alcotest.test_case "Core agrees with eval: cond then" `Quick test_core_agree_cond_then;
      Alcotest.test_case "Core agrees with eval: cond else" `Quick test_core_agree_cond_else;
      Alcotest.test_case "Core agrees with eval: list sugar" `Quick test_core_agree_list;
      Alcotest.test_case "inv_core is involutive" `Quick test_core_inv_involution;
      Alcotest.test_case "inv_core reverses execution" `Quick test_core_reversible_swap;
    ];
    "core-equiv", [
      Alcotest.test_case "Core == eval on corpus (rep/length/compare/minus/rle/enum)" `Quick test_core_equiv_corpus;
      Alcotest.test_case "Core == eval on self-interpreter ri.rwhile (p2d inputs)" `Quick test_core_equiv_selfinterp;
    ];
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
      Alcotest.test_case "eval pair? cons" `Quick test_eval_pair_cons;
      Alcotest.test_case "eval pair? atom" `Quick test_eval_pair_atom;
      Alcotest.test_case "eval pair? nil" `Quick test_eval_pair_nil;
      Alcotest.test_case "pair? parse+program+p2d" `Quick test_pair_program;
      Alcotest.test_case "pair? self-interp via ri" `Quick test_ri_self_interp_pairp;
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
    "wire-bridge", [
      Alcotest.test_case "decode ex1 (matches Agda parseEx)" `Quick test_wire_ex1_decode;
      Alcotest.test_case "decode ex2 (matches Agda parseEx)" `Quick test_wire_ex2_decode;
      Alcotest.test_case "transExp/d_exp structural round trip" `Quick test_wire_roundtrip_structural;
      Alcotest.test_case "decode com c0 (matches Agda parseCom)" `Quick test_wire_com_decode;
      Alcotest.test_case "transCom/d_com structural round trip" `Quick test_wire_com_roundtrip_structural;
      Alcotest.test_case "COLLECT-REFS forward->INV preserves tree" `Quick test_collect_refs_roundtrip;
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
    "simp-copyprop", [
      Alcotest.test_case "basic move fusion" `Quick test_copyprop_basic;
      Alcotest.test_case "fuses into a cons pattern" `Quick test_copyprop_into_cons_pattern;
      Alcotest.test_case "blocked when source is rewritten" `Quick test_copyprop_blocked_source_rewritten;
      Alcotest.test_case "expression read is not fused" `Quick test_copyprop_blocked_temp_read_twice;
      Alcotest.test_case "preserves semantics and inversion" `Quick test_copyprop_preserves_semantics;
      Alcotest.test_case "fuses inside a conditional branch" `Quick test_copyprop_inside_conditional;
      Alcotest.test_case "loop body: preserves semantics" `Quick test_copyprop_inside_loop_semantics;
      Alcotest.test_case "identity without single-use temps" `Quick test_copyprop_is_identity_without_moves;
    ];
    "simp-cli", [
      Alcotest.test_case "preserves answers on the examples" `Quick test_opt_preserves_answers;
      Alcotest.test_case "preserves invertibility" `Quick test_opt_preserves_invertibility;
      Alcotest.test_case "never costs more steps" `Quick test_opt_preserves_cost_or_improves;
      Alcotest.test_case "identity when there is nothing to do" `Quick test_opt_is_identity_on_a_clean_program;
    ];
    (* Jones optimality measured against the SELF-interpreter ri_fp3, in its
       reversible form (baseline p+ = the program-preserving version of p).
       Table and reading: ./measure_proj jones-self, RWHILE_S.md. *)
    "jones-self", [
      Alcotest.test_case "p+, self-interpretation and the residual agree" `Quick test_jones_self_baseline_agrees;
      Alcotest.test_case "work meter: residual <= p+ (optimal)" `Quick test_jones_self_work_optimal;
      Alcotest.test_case "steps meter: residual > p+ (NOT optimal)" `Quick test_jones_self_steps_not_optimal;
      Alcotest.test_case "the interpretive layer is removed (>=5x fewer steps)" `Quick test_jones_self_removes_interpretation;
      Alcotest.test_case "copy propagation is what buys it" `Quick test_jones_self_copyprop_needed;
      Alcotest.test_case "loop subjects: p loops, residual does not, and it wins on both meters" `Quick test_jones_self_loop_subjects_unrolled;
      Alcotest.test_case "loop subjects: the residual is general, not input-specific" `Quick test_jones_self_loop_residual_is_general;
    ];
    (* The boundary of the battery, pinned as expected failures.  See the note
       above test_jones_self_open_interpreter_is_fine. *)
    "jones-self-open", [
      Alcotest.test_case "ri_fp3 self-interprets reverse (the interpreter is fine)" `Quick test_jones_self_open_interpreter_is_fine;
      Alcotest.test_case "OPEN: dynamic control via ri_fp3 dies at 'lcheck ('error <= '41)" `Quick test_jones_self_open_dynamic_control_via_ri_fp3;
      Alcotest.test_case "OPEN: direct fp1 of reverse dies the same way" `Quick test_jones_self_open_direct_fp1_too;
    ];
    "work-meter", [
      Alcotest.test_case "equal values cost their size" `Quick test_work_equal_values_cost_their_size;
      Alcotest.test_case "a mismatch stops early" `Quick test_work_mismatch_stops_early;
      Alcotest.test_case "the reversible update is charged" `Quick test_work_charges_the_reversible_update;
      Alcotest.test_case "exposes the quadratic -steps misses" `Quick test_work_exposes_the_hidden_quadratic;
      Alcotest.test_case "the meter resets" `Quick test_work_counter_resets;
    ];
    "encoding-breakdown", [
      Alcotest.test_case "categories add up to count_nodes" `Quick test_encoding_adds_up;
      Alcotest.test_case "variable cost is the unary index" `Quick test_encoding_var_cost_is_unary;
      Alcotest.test_case "literals are charged to const" `Quick test_encoding_const_is_charged_to_const;
      Alcotest.test_case "pass 1 shows up as smaller var_index" `Quick test_encoding_hot_numbering_shrinks_var_index;
      Alcotest.test_case "optimal renumbering is a lower bound" `Quick test_encoding_optimal_is_a_lower_bound;
      Alcotest.test_case "optimal renumbering, by hand" `Quick test_encoding_optimal_by_hand;
      Alcotest.test_case "bit-list numeral cost model" `Quick test_encoding_bits_nodes_by_hand;
      Alcotest.test_case "malformed input is rejected" `Quick test_encoding_rejects_non_program;
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
      Alcotest.test_case "rep static split" `Quick test_ss_av_rep_static;
      Alcotest.test_case "rep partial-static input split" `Quick test_ss_av_rep_input_split;
      Alcotest.test_case "swap static fully executed" `Quick test_ss_av_swap_static;
      Alcotest.test_case "swap dynamic structural" `Quick test_ss_av_swap_dynamic;
      Alcotest.test_case "cond static true" `Quick test_ss_av_cond_static_true;
      Alcotest.test_case "cond static false" `Quick test_ss_av_cond_static_false;
      Alcotest.test_case "cond dynamic" `Quick test_ss_av_cond_dynamic;
      Alcotest.test_case "loop static unroll" `Quick test_ss_av_loop_static_unroll;
      Alcotest.test_case "loop dynamic" `Quick test_ss_av_loop_dynamic;
    ];
    "assemble-fp1", [
      Alcotest.test_case "AV-INIT builds static-nil store" `Quick test_av_init;
      Alcotest.test_case "assembled residual computes swap" `Quick test_assemble_fp1_swap;
      Alcotest.test_case "fp1 main specializes swap" `Quick test_fp1_main_swap;
      Alcotest.test_case "fp1 split-rejoin round-trip" `Quick test_fp1_split_rejoin;
      Alcotest.test_case "fp1 cross-var move+clear (no-alias fix)" `Quick test_fp1_move_clear;
      Alcotest.test_case "ri_fp3 reversible-clear self-interp: id" `Quick test_ri_fp3_selfinterp_id;
      Alcotest.test_case "ri_fp3 reversible-clear self-interp: swap" `Quick test_ri_fp3_selfinterp_swap;
      Alcotest.test_case "fp1-via-ri_fp3: structural ops preserved (was a KNOWN BUG)" `Quick test_fp1_ri_fp3_known_bug;
      Alcotest.test_case "fp1-via-ri_fp3: non-transposing sources now run correctly" `Quick test_fp1_ri_fp3_nontransposing_ok;
      Alcotest.test_case "fp1-via-ri_fp3: two-leaf patterns run (was a KNOWN BUG)" `Quick test_fp1_ri_fp3_two_leaf_patterns_run;
      Alcotest.test_case "ri_fp3 self-interprets (incl. a loop) correctly" `Quick test_ri_fp3_self_interprets;
      Alcotest.test_case "fp1-via-ri_fp3: nested pattern runs (was a KNOWN BUG)" `Quick test_fp1_ri_fp3_nested_pattern_runs;
      Alcotest.test_case "dyn-cond comp correct directly; KNOWN ri.rwhile 'cond bug via run_via_ri" `Quick test_fp1_dyncond_known_bug;
      Alcotest.test_case "depth-general nested read residualizes (PAT-READ-ITER)" `Quick test_fp1_nested_read;
      Alcotest.test_case "fp1-via-ri_fp3: STEP tracks Result structurally (was a KNOWN BUG)" `Quick test_fp1_step_structural_result;
      Alcotest.test_case "PAT-WRITE-ITER nested split (was a KNOWN BUG)" `Quick test_pat_write_nested_split;
      Alcotest.test_case "PAT-WRITE-ITER handles nested split" `Quick test_pat_write_iter_nested;
      Alcotest.test_case "DYNAMICIZE-ALL materialises + marks dynamic" `Quick test_dynamicize_all;
    ];
    "first-projection-min", [
      Alcotest.test_case "fp1 GREEN: [[spec_av]((ri_min.'swap))](('a.'b))=('swap.('b.'a))" `Quick test_fp1_min_swap;
      Alcotest.test_case "fp1 GREEN: [[spec_av]((ri_min.'id))]('q)=('id.'q)" `Quick test_fp1_min_id;
      Alcotest.test_case "fp1 GREEN seq: [[spec_av]((ri_seq.[]))](('a.'b))" `Quick test_fp1_seq_empty;
      Alcotest.test_case "fp1 GREEN seq: [[spec_av]((ri_seq.[id,swap]))](('a.'b))=([id,swap].('b.'a))" `Quick test_fp1_seq_idswap;
      Alcotest.test_case "fp1 GREEN seq: [[spec_av]((ri_seq.[swap,swap]))](('a.'b))=([swap,swap].('a.'b))" `Quick test_fp1_seq_swapswap;
      Alcotest.test_case "fp1 ri_min correct on ALL small inputs (exhaustive)" `Slow test_fp1_min_exhaustive;
      Alcotest.test_case "fp1 ri_seq correct on many op-lists x inputs (exhaustive)" `Slow test_fp1_seq_exhaustive;
    ];
    "specialization-gain", [
      Alcotest.test_case "fp1 residual is smaller than the interpreter (specialisation effective)" `Slow test_specialization_gain;
    ];
    "second-projection", [
      (* 2nd reversible Futamura projection: comp=[spec_av]((spec_av.('S.ri_min)))
       * is a correct compiler ([comp](('S.op))==fp1 residual B).  SLOW (~minutes,
       * specializes spec_av by self-application); skipped under `./test-suite -q`. *)
      Alcotest.test_case "fp2 GREEN: [spec_av]((spec_av.ri_min)) compiles ri_min (comp==B)" `Slow test_fp2_second_projection;
      Alcotest.test_case "fp3 GREEN: [spec_av]((spec_av.spec_av)) = cogen ([comp3]('S.ri_min)=comp2)" `Slow test_fp3_cogen;
    ];
    "reversible-spec", [
      Alcotest.test_case "spec_av_rev: clean-store run, [comp] correct, INV round-trips input" `Slow test_rev_spec_dead_garbage;
      Alcotest.test_case "fp2-rev: [spec_av_rev]((spec_av_rev.ri_min)) compiles ri_min (comp==B)" `Slow test_fp2_rev_second_projection;
      Alcotest.test_case "fp3-rev: [spec_av_rev]((spec_av_rev.spec_av_rev)) = reversible cogen" `Slow test_fp3_rev_cogen;
    ];
    "refactor-gate", [
      Alcotest.test_case "spec_av_clean == spec_av (fp1 residuals identical)" `Quick test_clean_equiv_spec_av;
      Alcotest.test_case "spec_av_clean == spec_av (fp2 comp identical, all paths)" `Slow test_clean_equiv_fp2;
    ];
    "spec-av-exp", [
      Alcotest.test_case "var static" `Quick test_se_av_var_static;
      Alcotest.test_case "var dynamic" `Quick test_se_av_var_dynamic;
      Alcotest.test_case "val literal" `Quick test_se_av_val;
      Alcotest.test_case "cons -> partial-static" `Quick test_se_av_cons_partial;
      Alcotest.test_case "hd recovers static" `Quick test_se_av_hd_recovers_static;
      Alcotest.test_case "hd dynamic" `Quick test_se_av_hd_dynamic;
      Alcotest.test_case "pair? static atom -> false" `Quick test_se_av_pairp_static_atom;
      Alcotest.test_case "pair? static cons -> true" `Quick test_se_av_pairp_static_cons;
      Alcotest.test_case "pair? partial-static -> true" `Quick test_se_av_pairp_partial;
      Alcotest.test_case "pair? dynamic -> residual" `Quick test_se_av_pairp_dynamic;
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
      Alcotest.test_case "lift preserves static input" `Quick test_av_lift_preserves_static;
      Alcotest.test_case "lift preserves dynamic input" `Quick test_av_lift_preserves_dynamic;
      Alcotest.test_case "lift preserves partial input" `Quick test_av_lift_preserves_partial;
      Alcotest.test_case "lift preserves nested input" `Quick test_av_lift_preserves_nested;
      Alcotest.test_case "eq static true" `Quick test_av_eq_static_true;
      Alcotest.test_case "eq static false" `Quick test_av_eq_static_false;
      Alcotest.test_case "eq mixed dynamic" `Quick test_av_eq_mixed_dynamic;
      Alcotest.test_case "uncons partial-static" `Quick test_av_uncons_partial;
      Alcotest.test_case "uncons static cons" `Quick test_av_uncons_static;
      Alcotest.test_case "uncons dynamic" `Quick test_av_uncons_dynamic;
      Alcotest.test_case "uncons static non-cons -> degenerate" `Quick test_av_uncons_static_noncons;
      Alcotest.test_case "mkav static" `Quick test_mkav_static;
      Alcotest.test_case "mkav static idx1" `Quick test_mkav_static_idx1;
      Alcotest.test_case "mkav dynamic" `Quick test_mkav_dynamic;
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
      Alcotest.test_case "non-nil truth: if Y fi Y on atom" `Quick test_nonnil_truth_cond_atom;
      Alcotest.test_case "non-nil truth: if Y fi Y on cons" `Quick test_nonnil_truth_cond_cons;
      Alcotest.test_case "non-nil truth: from Y until Y on atom" `Quick test_nonnil_truth_loop_atom;
    ];
    "hygienic-macros", [
      Alcotest.test_case "hygiene fixes local collision" `Quick test_hygienic_fixes_collision;
      Alcotest.test_case "non-hygienic collision aborts" `Quick test_nonhygienic_collision_aborts;
      Alcotest.test_case "fresh name avoids dashed user var" `Quick test_hygiene_avoids_dashed_var_collision;
      Alcotest.test_case "flag renames locals in expansion" `Quick test_hygienic_renames_in_expansion;
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
    (* "first-projection" group RETIRED: deprecated spec.rwhile + unfaithful
     * run_via_ri (ri.rwhile bug2).  fp1 is covered by "first-projection-min". *)
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
    "compiler", [
      Alcotest.test_case "hot-vars: same answer" `Quick test_hot_vars_same_answer;
      Alcotest.test_case "hot-vars: permutation" `Quick test_hot_vars_permutation;
      Alcotest.test_case "numbering: weighted by default" `Quick test_var_numbering_default;
      Alcotest.test_case "share-slots: same answer" `Quick test_share_slots_same_answer;
      Alcotest.test_case "share-slots: branches merge" `Quick test_share_slots_branches;
      Alcotest.test_case "share-slots: loops do not merge" `Quick test_share_slots_loop_widening;
      Alcotest.test_case "share-slots: pays off" `Quick test_share_slots_pays_off;
      Alcotest.test_case "share-slots: off by default" `Quick test_share_slots_off_by_default;
      Alcotest.test_case "static-vars: numbered last" `Quick test_static_vars_last;
      Alcotest.test_case "static-vars: same answer" `Quick test_static_vars_same_answer;
    ];
    "sugar", [
      Alcotest.test_case "skip" `Quick test_sugar_skip;
      Alcotest.test_case "assert" `Quick test_sugar_assert;
      Alcotest.test_case "swap <->" `Quick test_sugar_swap;
      Alcotest.test_case "local/delocal" `Quick test_sugar_local;
      Alcotest.test_case "local/delocal name mismatch" `Quick test_sugar_local_name_mismatch;
      Alcotest.test_case "local/for nil guards" `Quick test_sugar_local_guards;
      Alcotest.test_case "for" `Quick test_sugar_for;
      Alcotest.test_case "for scratch is fresh" `Quick test_sugar_for_scratch_fresh;
      Alcotest.test_case "push/pop" `Quick test_sugar_push_pop;
      Alcotest.test_case "push and pop are inverses" `Quick test_sugar_push_pop_inverse;
      Alcotest.test_case "inversion preserves cost" `Quick test_sugar_inverse_cost;
      Alcotest.test_case "self-interpretation" `Quick test_sugar_via_ri;
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
