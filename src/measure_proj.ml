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

(* command-constructor histogram, to diagnose what dominates a residual *)
type hist = { mutable seq:int; mutable ass:int; mutable rep:int;
              mutable cond:int; mutable loop:int; mutable other:int }
let rec hcom h = function
  | CSeq (a, b)         -> h.seq  <- h.seq  + 1; hcom h a; hcom h b
  | CAss _              -> h.ass  <- h.ass  + 1
  | CRep _              -> h.rep  <- h.rep  + 1
  | CCond (_, t, e, _)  -> h.cond <- h.cond + 1; hbr h t; hbe h e
  | CLoop (_, d, l, _)  -> h.loop <- h.loop + 1; hbd h d; hbl h l
  | CLocal (_, c)       -> hcom h c
  | _                   -> h.other <- h.other + 1
and hbr h = function BThen c -> hcom h c | BThenNone -> ()
and hbe h = function BElse c -> hcom h c | BElseNone -> ()
and hbd h = function BDo c -> hcom h c | BDoNone -> ()
and hbl h = function BLoop c -> hcom h c | BLoopNone -> ()

(* nodes of program-as-data sitting inside loop bodies (the dynamic store walks) *)
let rec loop_nodes = function
  | CSeq (a, b)        -> loop_nodes a + loop_nodes b
  | CCond (_, t, e, _) -> brn t + ben e
  | CLoop (_, d, l, _) as c ->
     cn (Program2DataRwhile.program2data (Prog ([], RIdent "X", c, RIdent "X")))
  | CLocal (_, c)      -> loop_nodes c
  | _ -> 0
and brn = function BThen c -> loop_nodes c | BThenNone -> 0
and ben = function BElse c -> loop_nodes c | BElseNone -> 0

let report_hist name body =
  let h = { seq=0; ass=0; rep=0; cond=0; loop=0; other=0 } in
  hcom h body;
  Printf.printf "  [%s] CSeq=%d CAss=%d CRep=%d CCond=%d CLoop=%d other=%d\n"
    name h.seq h.ass h.rep h.cond h.loop h.other;
  Printf.printf "  [%s] nodes inside CLoop bodies = %d\n" name (loop_nodes body)

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
    Printf.printf "[comp2_simp](('S.swap)) == B : %b   (preserves meaning)\n" (r_simp = b_swap);
    (* breakdown: what dominates comp2 (before/after Simp)? *)
    Printf.printf "breakdown (constructor histogram + nodes under loops):\n";
    (match comp2_prog with Prog (_, _, body, _) -> report_hist "comp2     " body);
    (match comp2_simp with Prog (_, _, body, _) -> report_hist "comp2_simp" body)
  end
