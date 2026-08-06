(* one-off diagnostic: print varProgram order (the p2d numbering) of a program *)
let parse (c : in_channel) : AbsRwhile.program =
  ParRwhile.pProgram LexRwhile.token (Lexing.from_channel c)

let () =
  let ch = open_in Sys.argv.(1) in
  let prog = parse ch in
  close_in ch;
  let p2 = MacroRwhile.expMacProgram prog in
  let vs = EvalRwhile.varProgram p2 in
  List.iteri (fun i x ->
      let s = match x with AbsRwhile.RIdent s -> s in
      Printf.printf "%3d  %s\n" (i+1) s) vs
