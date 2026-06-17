(* d2p: decode a program-as-data value (p2d output / a spec residual) back to
 * R-WHILE source, or evaluate it directly.  Uses Program2DataRwhile.data2program
 * (the inverse of program2data).  Handy for inspecting/running residuals without
 * the ri.rwhile self-interpreter (whose 'cond handling is unfaithful for
 * conditionals whose entry-test and exit-assertion values differ).
 *
 *   ./d2p <comp.val>             pretty-print the decoded program
 *   ./d2p <comp.val> <data.val>  decode and EVALUATE on the given input *)

let parseValT (c : in_channel) : AbsRwhile.valT =
  ParRwhile.pValT LexRwhile.token (Lexing.from_channel c)

let () =
  let ch = open_in Sys.argv.(1) in
  let v = parseValT ch in close_in ch;
  let prog = Program2DataRwhile.data2program v in
  if Array.length Sys.argv >= 3 then begin
    let dch = open_in Sys.argv.(2) in
    let d = parseValT dch in close_in dch;
    print_endline (PrintRwhile.printTree PrintRwhile.prtValT
                     (EvalRwhile.evalProgram prog d))
  end else
    print_endline (PrintRwhile.printTree PrintRwhile.prtProgram prog)
