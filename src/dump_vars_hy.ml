let parse c = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel c)
let () =
  if Array.length Sys.argv > 2 && Sys.argv.(2) = "hy" then MacroRwhile.hygienic := true;
  let ch = open_in Sys.argv.(1) in
  let prog = parse ch in close_in ch;
  let p2 = MacroRwhile.expMacProgram prog in
  let vs = EvalRwhile.varProgram p2 in
  Printf.printf "TOTAL VARS = %d\n" (List.length vs)
