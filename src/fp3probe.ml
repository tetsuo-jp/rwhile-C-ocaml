(* fp3probe: reproduction harness for the open fp1-via-ri_fp3 bug.
 *
 *   ./fp3probe [interpreter] [src ...]
 *
 * For each source program, computes comp = [spec_av]((ri_fp3 . src)), prints the
 * residual, then runs it on ('a.'b) and compares with direct evaluation.
 * Defaults: interpreter = ri_fp3, sources = id id2 id3 rep swap sx_splitjoin.
 * FP3PROBE_SPEC=<name> uses ../examples/<name>.rwhile as the specialiser instead
 * of spec_av (e.g. spec_av_bti, to ask whether selective dynamicize changes the
 * '41 wall). *)

open AbsRwhile

let dir = "../examples"

let parse_prog filename =
  let ch = open_in filename in
  let p = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel ch) in
  close_in ch; p

let atom s = VAtom (Atom s)

(* spec input: ((interp . src) . ('S . nil))-shaped, matching TestSuite's spec_in *)
let spec_in interp src = VCons (interp, VCons (atom "'S", src))

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let interp_name, srcs = match args with
    | [] -> "ri_fp3", ["id"; "id2"; "id3"; "rep"; "swap"; "sx_splitjoin"]
    | i :: [] -> i, ["id"; "id2"; "id3"; "rep"; "swap"; "sx_splitjoin"]
    | i :: rest -> i, rest in
  let spec_name = match Sys.getenv_opt "FP3PROBE_SPEC" with
    | Some s -> s | None -> "spec_av" in
  let spec_av = parse_prog (dir ^ "/" ^ spec_name ^ ".rwhile") in
  let interp = Program2DataRwhile.program2data
      (parse_prog (dir ^ "/" ^ interp_name ^ ".rwhile")) in
  let d = (match Sys.getenv_opt "FP3PROBE_D" with
     | Some "abnil" -> VCons (atom "'a", VCons (atom "'b", VNil))
     | _ -> VCons (atom "'a", atom "'b")) in
  List.iter (fun name ->
      Printf.printf "=== %s (via %s) ===\n" name interp_name;
      let srcp = parse_prog (dir ^ "/" ^ name ^ ".rwhile") in
      let expected =
        try PrintRwhile.printTree PrintRwhile.prtValT
              (EvalRwhile.evalProgram srcp d)
        with Failure m -> "<direct eval failed: " ^ m ^ ">" in
      (match (try Ok (EvalRwhile.evalProgram spec_av
                        (spec_in interp (Program2DataRwhile.program2data srcp)))
              with Failure m -> Error m) with
       | Error m -> Printf.printf "  SPECIALIZATION FAILED: %s\n" m
       | Ok comp ->
         let rec nodes = function
           | VNil -> 1 | VAtom _ -> 1
           | VCons (a, b) -> 1 + nodes a + nodes b
           | VList vs -> List.fold_left (fun n v -> n + nodes v) 1 vs in
         let prog0 = Program2DataRwhile.data2program comp in
         let progcp = Simp.copyprop_program prog0 in
         let compcp = Program2DataRwhile.program2data progcp in
         Printf.printf "  residual nodes = %d   (copyprop: %d)\n"
           (nodes comp) (nodes compcp);
         let prog = if Sys.getenv_opt "FP3PROBE_CP" <> None then progcp else prog0 in
         if Sys.getenv_opt "FP3PROBE_SHOW" <> None then
           Printf.printf "  residual:\n%s\n"
             (PrintRwhile.printTree PrintRwhile.prtProgram prog);
         (match (try Ok (EvalRwhile.evalProgram prog d) with Failure m -> Error m) with
          | Error m -> Printf.printf "  RESIDUAL FAILED: %s\n" m
          | Ok v ->
            let got = (match v with VCons (_, res) -> res | v -> v) in
            let gots = PrintRwhile.printTree PrintRwhile.prtValT got in
            Printf.printf "  got %s / expected %s  -> %s\n" gots expected
              (if gots = expected then "OK" else "WRONG ANSWER")));
      flush stdout)
    srcs
