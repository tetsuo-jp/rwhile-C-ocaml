(* measure_proj: quantify the Futamura-projection residual sizes, to baseline the
 * "optimising reversible specialiser" work (idea 1).  Reports node counts and the
 * key ratio comp2 / |spec_av| (≈1 for the trivial specialiser; the goal of an
 * optimising specialiser is comp2 < |spec_av|, i.e. the compiler is smaller/
 * faster than re-running the specialiser).
 *
 *   ./measure_proj            fp1 residuals only (fast)
 *   ./measure_proj full       also comp2 = [spec_av]((spec_av.ri_min))  (SLOW, minutes)
 *
 * Uses direct evaluation (Program2DataRwhile + EvalRwhile), matching the test
 * suite's judgement method. *)

open AbsRwhile

let dir = "../examples"

let parse_prog filename =
  let ch = open_in filename in
  let p = ParRwhile.pProgram LexRwhile.token (Lexing.from_channel ch) in
  close_in ch; p

let cn = EvalRwhile.count_nodes
let spec_in prog src = VCons (prog, VCons (VAtom (Atom "'S"), src))

let () =
  let spec_av = parse_prog (dir ^ "/spec_av.rwhile") in
  let rimin   = parse_prog (dir ^ "/ri_min.rwhile") in
  let pd_spec  = Program2DataRwhile.program2data spec_av in
  let pd_rimin = Program2DataRwhile.program2data rimin in
  let nspec = cn pd_spec in
  Printf.printf "|spec_av| (program-as-data) = %d nodes\n" nspec;
  Printf.printf "|ri_min|                    = %d nodes\n" (cn pd_rimin);
  let b_swap = EvalRwhile.evalProgram spec_av (spec_in pd_rimin (VAtom (Atom "'swap"))) in
  let b_id   = EvalRwhile.evalProgram spec_av (spec_in pd_rimin (VAtom (Atom "'id"))) in
  Printf.printf "fp1 residual [spec_av]((ri_min.swap)) = %d nodes (%.2fx |ri_min|)\n"
    (cn b_swap) (float_of_int (cn b_swap) /. float_of_int (cn pd_rimin));
  Printf.printf "fp1 residual [spec_av]((ri_min.id))   = %d nodes\n" (cn b_id);
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "full" then begin
    Printf.printf "computing comp2 = [spec_av]((spec_av.ri_min)) (slow)...\n%!";
    let comp2 = EvalRwhile.evalProgram spec_av (spec_in pd_spec pd_rimin) in
    Printf.printf "comp2          = %d nodes  (ratio %.3f x |spec_av|)\n"
      (cn comp2) (float_of_int (cn comp2) /. float_of_int nspec);
    (* simplify the residual compiler and re-measure *)
    let comp2_prog = Program2DataRwhile.data2program comp2 in
    let comp2_simp = Simp.simpProgram comp2_prog in
    let comp2_simp_d = Program2DataRwhile.program2data comp2_simp in
    Printf.printf "comp2 (Simp'd) = %d nodes  (%.1f%% of comp2, ratio %.3f x |spec_av|)\n"
      (cn comp2_simp_d)
      (100.0 *. float_of_int (cn comp2_simp_d) /. float_of_int (cn comp2))
      (float_of_int (cn comp2_simp_d) /. float_of_int nspec);
    (* correctness: [comp2](('S.op)) and [comp2_simp](('S.op)) must equal the fp1
     * residual B (= [spec_av]((ri_min.op))). *)
    let inp op = VCons (VAtom (Atom "'S"), VAtom (Atom op)) in
    let r_orig = EvalRwhile.evalProgram comp2_prog (inp "'swap") in
    let r_simp = EvalRwhile.evalProgram comp2_simp (inp "'swap") in
    Printf.printf "[comp2](('S.swap)) == B : %b\n" (r_orig = b_swap);
    Printf.printf "[comp2_simp](('S.swap)) == B : %b   (preserves meaning)\n" (r_simp = b_swap)
  end
