let parse (c : in_channel) : AbsRwhile.program =
    ParRwhile.pProgram LexRwhile.token (Lexing.from_channel c)

let parseValT (c : in_channel) : AbsRwhile.valT =
    ParRwhile.pValT LexRwhile.token (Lexing.from_channel c)

let showTree (t : AbsRwhile.program) : string =
    PrintRwhile.printTree PrintRwhile.prtProgram t

let showValT (t : AbsRwhile.valT) : string =
    PrintRwhile.printTree PrintRwhile.prtValT t

let () =
  let files = ref [] in
  let f_inv = ref false in
  let f_p2d = ref false in
  let f_exp = ref false in
  let f_stats = ref false in
  let f_steps = ref false in
  let f_core = ref false in
  let f_simp = ref false in
  Arg.parse
    [("-inverse", Arg.Set f_inv,  "inversion");
     ("-p2d",     Arg.Set f_p2d,  "translation from programs to data");
     ("-exp",     Arg.Set f_exp,  "expand macro");
     ("-local",   Arg.Set EvalRwhile.enable_local,
      "extension: scoped local variables  (local X in C end)");
     ("-autofi",  Arg.Set EvalRwhile.enable_autofi,
      "extension: automatic fi-assertion  (iff E then C else D)");
     ("-array",   Arg.Set EvalRwhile.enable_array,
      "extension: array index operations  (A[I] ^= E  /  get A[I])");
     ("-hygienic-macros", Arg.Set MacroRwhile.hygienic,
      "expand macros hygienically: alpha-rename internal local variables");
     ("-hot-vars", Arg.Set Program2DataRwhile.hot_vars,
      "p2d: number variables by static access weight, not first occurrence \
       (shortens the self-interpreter's store walks; see Optimize.ml)");
     ("-share-slots", Arg.Set Program2DataRwhile.share_slots,
      "p2d: give variables with disjoint live ranges the same store slot \
       (shortens the self-interpreter's store.  Sound for EXECUTION only -- \
        do not feed the result to spec_av; see Optimize.ml pass 2)");
     ("-llm-errors", Arg.Set EvalRwhile.llm_errors,
      "emit structured, machine-/LLM-friendly error messages");
     ("-stats",   Arg.Set f_stats,
      "after evaluation, print result size (node count / bytes) to stderr");
     ("-steps",   Arg.Set f_steps,
      "after evaluation, print the executed-command step count to stderr (unit-cost time)");
     ("-core",    Arg.Set f_core,
      "evaluate via the Core IR abstraction layer (Core.ml; mirrors the Agda-verified core)");
     ("-simp",    Arg.Set f_simp,
      "simplify the (residual) program: constant-fold and remove dead reversible branches")]
    (fun s -> files := !files @ [s])
    ("R-WHILE Interpreter (C) Tetsuo Yokoyama\n" ^
       Printf.sprintf "usage: %s [-inverse] [-p2d] [-exp] [-local] [-autofi] [-array] [-hygienic-macros] [-hot-vars] [-share-slots] [-llm-errors] [-stats] [-steps] [-core] program [data]"
         Sys.argv.(0));
  match !files with
  | [prog_filename] ->
     let channel = open_in prog_filename in
     let prog1 = parse channel in
     let _ = close_in channel in
     let prog2 = if !f_exp then MacroRwhile.expMacProgram prog1 else prog1 in
     let prog3 = if !f_inv then InvRwhile.invProgram prog2 else prog2 in
     let prog4 = if !f_simp then Simp.simpProgram prog3 else prog3 in
     print_endline (if !f_p2d
		   then showValT (Program2DataRwhile.program2data prog4)
		   else showTree prog4)
  | [prog_filename; data_filename] -> 
     let channel = open_in prog_filename in
     let prog = parse channel in 
     let _ = close_in channel in
     let channel = open_in data_filename in
     let data = parseValT channel in 
     let _ = close_in channel in
     (try
        EvalRwhile.reset_steps ();
        let result =
          if !f_core then Core.eval_program_core prog data
          else EvalRwhile.evalProgram prog data in
        print_endline (showValT result);
        if !f_stats then
          Printf.eprintf "[RWHILE-STATS] nodes=%d bytes=%d\n%!"
            (EvalRwhile.count_nodes result) (String.length (showValT result));
        if !f_steps then
          Printf.eprintf "[RWHILE-STEPS] steps=%d\n%!" (EvalRwhile.get_steps ())
      with
      | Failure str ->
         (* eval_error already produced the structured block in LLM mode. *)
         print_endline (if !EvalRwhile.llm_errors then str else "Error:\n" ^ str)
      | e ->
         (* Any other exception (Not_found, Invalid_argument, ...) is unexpected;
            format it too so callers always get a parseable error in LLM mode. *)
         let msg = Printexc.to_string e in
         print_endline (if !EvalRwhile.llm_errors
                        then EvalRwhile.format_uncaught msg
                        else "Error:\n" ^ msg))
  | _ -> failwith "Invalid arguments"
