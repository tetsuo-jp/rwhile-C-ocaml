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
let atom s = VAtom (Atom s)
let rec vlist = function [] -> VNil | x :: xs -> VCons (x, vlist xs)

(* Jones-optimality battery: for each (interpreter, source program, data) the fp1
 * residual B = [spec_av]((int.('S.src))) should run [B](d) in FEWER evalCom steps
 * than the interpreter [int]((src.d)) -- the interpretation layer is removed and
 * (for ri_seq) the static op-list loop is unrolled.  Prints residual size and the
 * exec-step ratio (resid/interp); ratio < 1 quantifies Jones optimality. *)
let jones spec_av =
  let ab = VCons (atom "'a", atom "'b") in
  let rimin = parse_prog (dir ^ "/ri_min.rwhile") in
  let riseq = parse_prog (dir ^ "/ri_seq.rwhile") in
  let sw = atom "'swap" and id = atom "'id" in
  let cases =
    [ ("ri_min", rimin, sw, ab, "swap");
      ("ri_min", rimin, id, ab, "id");
      ("ri_seq", riseq, vlist [sw], ab, "[swap]");
      ("ri_seq", riseq, vlist [sw; sw], ab, "[swap;swap]");
      ("ri_seq", riseq, vlist [sw; id; sw], ab, "[swap;id;swap]");
      ("ri_seq", riseq, vlist [sw; sw; sw; sw], ab, "[swap*4]");
      ("ri_seq", riseq, vlist [id; id; id; id; id; id], ab, "[id*6]") ]
  in
  Printf.printf "Jones optimality: fp1 residual exec-steps vs interpreter exec-steps\n";
  Printf.printf "  %-7s %-15s %8s %7s %7s %7s\n" "interp" "program" "|resid|" "resid" "interp" "ratio";
  List.iter (fun (iname, iprog, src, d, label) ->
      let pd = Program2DataRwhile.program2data iprog in
      let b = EvalRwhile.evalProgram spec_av (spec_in pd src) in
      let bp = Program2DataRwhile.data2program b in
      EvalRwhile.reset_steps (); let ro = EvalRwhile.evalProgram bp d in
      let sr = EvalRwhile.get_steps () in
      EvalRwhile.reset_steps (); let io = EvalRwhile.evalProgram iprog (VCons (src, d)) in
      let si = EvalRwhile.get_steps () in
      Printf.printf "  %-7s %-15s %8d %7d %7d %6.2fx%s\n" iname label (cn b) sr si
        (float_of_int sr /. float_of_int si) (if ro = io then "" else "  MISMATCH!"))
    cases;
  exit 0

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

(* diagnostic: does spec_av unroll a STATIC-bounded loop?  Specialise <subject>
 * to a static value and report the residual's size + CLoop count. *)
let looptest spec_av subj_file sval =
  let subj = parse_prog subj_file in
  let pd = Program2DataRwhile.program2data subj in
  let resid = EvalRwhile.evalProgram spec_av (spec_in pd sval) in
  Printf.printf "looptest %s  (static=%s):\n" subj_file
    (PrintRwhile.printTree PrintRwhile.prtValT sval);
  Printf.printf "  residual = %d nodes\n" (cn resid);
  (match Program2DataRwhile.data2program resid with
   | Prog (_, _, body, _) -> report_hist "residual" body)

(* fp1 safety gate: check that a CANDIDATE specialiser (e.g. a spec_av_bti work
 * copy) still produces CORRECT, REVERSIBLE fp1 residuals before/after a BTI edit.
 * Criterion (hard): for op in {swap,id} and several inputs d, the residual
 * B_op = [cand]((ri_min.op)) satisfies  [B_op](d) == [ri_min]((op.d))  (meaning)
 * and  [inv B_op]([B_op](d)) == d  (reversibility).  Baseline fp1 sizes
 * (swap=103, id=63) are reported as drift info but do NOT gate (an optimising
 * edit may legitimately change them).  Exits 0 on PASS, 1 on FAIL. *)
let gate spec_file =
  let cand = parse_prog spec_file in
  let rimin = parse_prog (dir ^ "/ri_min.rwhile") in
  let pd_rimin = Program2DataRwhile.program2data rimin in
  let tests = [ VCons (VAtom (Atom "'a"), VAtom (Atom "'b"));
                VCons (VNil, VNil);
                VCons (VCons (VAtom (Atom "'x"), VAtom (Atom "'y")), VAtom (Atom "'z")) ] in
  let check op =
    try
      let b = EvalRwhile.evalProgram cand (spec_in pd_rimin (VAtom (Atom op))) in
      let bp = Program2DataRwhile.data2program b in   (* may raise on malformed residual *)
      let meaning_ok = List.for_all (fun d ->
          let lhs = (try Some (EvalRwhile.evalProgram bp d) with _ -> None) in
          let rhs = (try Some (EvalRwhile.evalProgram rimin (VCons (VAtom (Atom op), d))) with _ -> None) in
          lhs <> None && lhs = rhs) tests in
      let rev_ok = List.for_all (fun d ->
          try EvalRwhile.evalProgram (InvRwhile.invProgram bp) (EvalRwhile.evalProgram bp d) = d
          with _ -> false) tests in
      Printf.printf "  op=%-5s size=%-4d meaning=%b reversible=%b\n" op (cn b) meaning_ok rev_ok;
      (meaning_ok && rev_ok, cn b)
    with e ->
      Printf.printf "  op=%-5s ERROR (%s)\n" op (Printexc.to_string e);
      (false, 0)
  in
  Printf.printf "fp1 gate on %s:\n" spec_file;
  let s_ok, s_sz = check "'swap" in
  let i_ok, i_sz = check "'id" in
  Printf.printf "  fp1 sizes swap=%d id=%d (baseline 103/63 unchanged=%b)\n"
    s_sz i_sz (s_sz = 103 && i_sz = 63);
  if s_ok && i_ok then (Printf.printf "GATE PASS (meaning + reversibility)\n"; exit 0)
  else (Printf.printf "GATE FAIL\n"; exit 1)

let () =
  if Array.length Sys.argv >= 3 && Sys.argv.(1) = "gate" then gate Sys.argv.(2);
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "jones" then
    jones (parse_prog (dir ^ "/spec_av.rwhile"));
  let spec_av = parse_prog (dir ^ "/spec_av.rwhile") in
  if Array.length Sys.argv >= 4 && Sys.argv.(1) = "looptest" then begin
    let sch = open_in Sys.argv.(3) in
    let sv = ParRwhile.pValT LexRwhile.token (Lexing.from_channel sch) in
    close_in sch;
    looptest spec_av Sys.argv.(2) sv; exit 0
  end;
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
  (* execution-cost (Jones-optimality dimension): the fp1 residual runs in fewer
   * evalCom steps than the interpreter, since static dispatch was resolved. *)
  let ab = VCons (VAtom (Atom "'a"), VAtom (Atom "'b")) in
  let b_prog = Program2DataRwhile.data2program b_swap in
  EvalRwhile.reset_steps (); ignore (EvalRwhile.evalProgram b_prog ab);
  let steps_resid = EvalRwhile.get_steps () in
  EvalRwhile.reset_steps ();
  ignore (EvalRwhile.evalProgram rimin (VCons (VAtom (Atom "'swap"), ab)));
  let steps_int = EvalRwhile.get_steps () in
  Printf.printf "exec steps: [B](('a.'b))=%d  vs  [ri_min]((swap.('a.'b)))=%d  (residual %.2fx)\n"
    steps_resid steps_int (float_of_int steps_resid /. float_of_int steps_int);
  (* reversibility: the generated residual is a reversible program -- its
   * syntactic inverse (InvRwhile.invProgram) undoes it. *)
  let out = EvalRwhile.evalProgram b_prog ab in
  let back = EvalRwhile.evalProgram (InvRwhile.invProgram b_prog) out in
  Printf.printf "residual reversibility: [B](('a.'b))=%s ; [inv B](that)=%s ; round-trips: %b\n"
    (PrintRwhile.printTree PrintRwhile.prtValT out)
    (PrintRwhile.printTree PrintRwhile.prtValT back) (back = ab);
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
