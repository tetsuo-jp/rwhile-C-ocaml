let parse (c : in_channel) : AbsRwhile.program =
    ParRwhile.pProgram LexRwhile.token (Lexing.from_channel c)

let parseValT (c : in_channel) : AbsRwhile.valT =
    ParRwhile.pValT LexRwhile.token (Lexing.from_channel c)

let showTree (t : AbsRwhile.program) : string =
    PrintRwhile.printTree PrintRwhile.prtProgram t

let showValT (t : AbsRwhile.valT) : string =
    PrintRwhile.printTree PrintRwhile.prtValT t

(* The optimisation pipeline, shared by the two modes so that `./ri -simp
   -copyprop p.rwhile d.val` RUNS what `./ri -simp -copyprop p.rwhile` PRINTS.
   Copy propagation gates on "this variable occurs exactly twice in the whole
   program", which cannot see through a macro call, so it expands macros first
   -- evalProgram would expand them anyway, so nothing changes but the reach. *)
let optimise ~simp ~cprop (p : AbsRwhile.program) : AbsRwhile.program =
  let p = if cprop then MacroRwhile.expMacProgram p else p in
  let p = if simp then Simp.simpProgram p else p in
  if cprop then Simp.copyprop_program p else p

let () =
  let files = ref [] in
  let f_inv = ref false in
  let f_p2d = ref false in
  let f_exp = ref false in
  let f_stats = ref false in
  let f_steps = ref false in
  let f_work = ref false in
  let f_core = ref false in
  let f_simp = ref false in
  let f_cprop = ref false in
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
     ("-first-occurrence-vars", Arg.Clear Program2DataRwhile.hot_vars,
      "p2d: number variables in first-occurrence order (the pre-2026-08 \
       numbering).  The default is by static access weight, which halves the \
       encoding; see Optimize.ml pass 1");
     ("-static-vars",
      Arg.String (fun s -> Program2DataRwhile.static_vars :=
        String.split_on_char ',' s),
      "p2d: comma-separated names of the subject's STATIC variables; they are \
       numbered last so the dynamic ones get short indices and the residual of \
       a specialisation shrinks (see Optimize.ml pass 3)");
     ("-share-slots", Arg.Set Program2DataRwhile.share_slots,
      "p2d: give variables with disjoint live ranges the same store slot \
       (shortens the self-interpreter's store.  Sound for EXECUTION only -- \
        do not feed the result to spec_av; see Optimize.ml pass 2)");
     ("-llm-errors", Arg.Set EvalRwhile.llm_errors,
      "emit structured, machine-/LLM-friendly error messages");
     ("-stats",   Arg.Set f_stats,
      "after evaluation, print result size (node count / bytes) to stderr");
     ("-work",    Arg.Set f_work,
      "count value nodes examined by comparison (the cost -steps does not count)");
     ("-steps",   Arg.Set f_steps,
      "after evaluation, print the executed-command step count to stderr (unit-cost time)");
     ("-core",    Arg.Set f_core,
      "evaluate via the Core IR abstraction layer (Core.ml; mirrors the Agda-verified core)");
     ("-simp",    Arg.Set f_simp,
      "simplify the (residual) program: constant-fold and remove dead reversible branches");
     ("-copyprop", Arg.Set f_cprop,
      "fuse write-once/read-once variable moves (expands macros first; combine with -simp)")]
    (fun s -> files := !files @ [s])
    ("R-WHILE Interpreter (C) Tetsuo Yokoyama\n" ^
       Printf.sprintf "usage: %s [-inverse] [-p2d] [-exp] [-local] [-autofi] [-array] [-hygienic-macros] [-first-occurrence-vars] [-share-slots] [-llm-errors] [-stats] [-steps] [-work] [-simp] [-copyprop] [-core] program [data]"
         Sys.argv.(0));
  match !files with
  | [prog_filename] ->
     let channel = open_in prog_filename in
     let prog1 = parse channel in
     let _ = close_in channel in
     let prog2 = if !f_exp then MacroRwhile.expMacProgram prog1 else prog1 in
     let prog3 = if !f_inv then InvRwhile.invProgram prog2 else prog2 in
     let prog4 = optimise ~simp:!f_simp ~cprop:!f_cprop prog3 in
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
        let prog' = optimise ~simp:!f_simp ~cprop:!f_cprop prog in
        let result =
          if !f_core then Core.eval_program_core prog' data
          else EvalRwhile.evalProgram prog' data in
        print_endline (showValT result);
        if !f_stats then
          Printf.eprintf "[RWHILE-STATS] nodes=%d bytes=%d\n%!"
            (EvalRwhile.count_nodes result) (String.length (showValT result));
        if !f_steps then
          Printf.eprintf "[RWHILE-STEPS] steps=%d\n%!" (EvalRwhile.get_steps ());
        if !f_work then
          Printf.eprintf "[RWHILE-WORK] work=%d\n%!" (EvalRwhile.get_work ())
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
