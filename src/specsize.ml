(* specsize: size spec_av's AV store (AV-INIT N = FpN) to the SUBJECT program's
 * variable count, instead of a fixed constant.  The store must have one slot per
 * variable of the program being specialised; for self-application (fp2/fp3) that
 * program is large (spec_av ~223 vars), for fp1 it is tiny (ri_min ~5).  Fixing N
 * wastes time on small subjects and fails on subjects bigger than the constant.
 *
 *   ./specsize <spec.rwhile> <subject.rwhile> [margin]
 *        -> writes <spec.rwhile> with FpN and TmpT resized, to stdout.
 *   ./specsize -n <subject.rwhile>
 *        -> just prints the variable count N of <subject.rwhile>.
 *
 * Sizing: let n = #variables(subject) (after macro expansion).
 *   FpN  = n + margin   (store slots; default margin 8)
 *   TmpT = n + 2        (swap-via-temp scratch index: must be ABOVE the subject's
 *                        variable indices so the residual temp never aliases a
 *                        real variable; 2 keeps it clear of n yet below FpN).
 *
 * Usage for fp3 (cogen), e.g.:
 *   ./specsize ../examples/spec_av.rwhile ../examples/spec_av.rwhile > /tmp/sa.rwhile
 *   ./ri /tmp/sa.rwhile fp3.val        # fp3 with a store sized exactly to spec_av *)

let rec lit k = if k = 0 then "nil" else "(nil." ^ lit (k-1) ^ ")"

let varcount file =
  let ch = open_in file in
  let p = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel ch) in
  close_in ch;
  List.length (EvalRwhile.varProgram (MacroRwhile.expMacProgram p))

(* indentation-preserving line: if the trimmed line starts with `key ^= ` rewrite
 * the whole statement to `<indent>key ^= <value><tail>`; else return it unchanged. *)
let starts_with s pre =
  String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre

let read_lines file =
  let ch = open_in file in
  let rec go acc = match input_line ch with
    | l -> go (l :: acc)
    | exception End_of_file -> close_in ch; List.rev acc in
  go []

(* RWHILE_HYGIENIC=1 sizes the store for -hygienic-macros expansion, which is what
 * `RWHILE_HYGIENIC=1 ./test-suite` runs.  Alpha-renaming multiplies the variable
 * count by roughly 4-5x (spec_av 219 -> 897, ri 49 -> 257), so a store sized for
 * the plain count overflows and the AV-store walk falls off the end with
 * "Cannot match cons pattern cons U-N Vl against non-cons value nil". *)
let () =
  if Sys.getenv_opt "RWHILE_HYGIENIC" <> None then MacroRwhile.hygienic := true

let () =
  match Array.to_list Sys.argv with
  | [_; "-n"; subj] -> Printf.printf "%d\n" (varcount subj)
  (* how many store slots the subject needs after Optimize's slot sharing --
     i.e. the largest number of simultaneously live variables *)
  | [_; "-slots"; subj] ->
     let ch = open_in subj in
     let p = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel ch) in
     close_in ch;
     let sub = Optimize.slot_alloc (MacroRwhile.expMacProgram p) in
     let slots = List.sort_uniq compare (List.map snd sub) in
     Printf.printf "%d\n" (List.length slots)
  (* -share: size the store to the SLOT count instead of the variable count,
     for a pipeline that encodes the subject with ./ri -p2d -share-slots *)
  | _ :: "-share" :: spec :: subj :: rest ->
     let margin = match rest with m :: _ -> int_of_string m | [] -> 8 in
     let ch = open_in subj in
     let p = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel ch) in
     close_in ch;
     let sub = Optimize.slot_alloc (MacroRwhile.expMacProgram p) in
     let n = List.length (List.sort_uniq compare (List.map snd sub)) in
     let fpn = lit (n + margin) and tmp = lit (n + 2) in
     List.iter (fun line ->
       let t = String.trim line in
       if starts_with t "FpN ^= " then print_endline ("  FpN ^= " ^ fpn ^ ";")
       else if starts_with t "TmpT ^= " then print_endline ("  TmpT ^= " ^ tmp)
       else print_endline line)
       (read_lines spec)
  | _ :: spec :: subj :: rest ->
     let margin = match rest with m :: _ -> int_of_string m | [] -> 8 in
     let n = varcount subj in
     let fpn = lit (n + margin) and tmp = lit (n + 2) in
     List.iter (fun line ->
       let t = String.trim line in
       if starts_with t "FpN ^= " then print_endline ("  FpN ^= " ^ fpn ^ ";")
       else if starts_with t "TmpT ^= " then print_endline ("  TmpT ^= " ^ tmp)
       else print_endline line)
       (read_lines spec)
  | _ ->
     prerr_endline "usage: specsize <spec.rwhile> <subject.rwhile> [margin]";
     prerr_endline "       specsize -n <subject.rwhile>";
     exit 1
