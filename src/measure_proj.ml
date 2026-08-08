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
(* count CLoop nodes in a program body (an interpreter loops; a compiled residual
 * should be loop-free). *)
let rec count_loops = function
  | CSeq (a, b)        -> count_loops a + count_loops b
  | CCond (_, t, e, _) -> clthen t + clelse e
  | CLoop (_, d, l, _) -> 1 + cldo d + clloop l
  | CLocal (_, c)      -> count_loops c
  | _ -> 0
and clthen = function BThen c -> count_loops c | BThenNone -> 0
and clelse = function BElse c -> count_loops c | BElseNone -> 0
and cldo = function BDo c -> count_loops c | BDoNone -> 0
and clloop = function BLoop c -> count_loops c | BLoopNone -> 0

let body_loops prog = match prog with Prog (_, _, b, _) -> count_loops b

(* #4: empirical garbage LOWER BOUND.  For a NON-INJECTIVE source S (a function we
 * wish to simulate reversibly), any reversible simulation keeps resid x=(S x,g x)
 * with resid injective; then g must be injective on every fiber of S, so the
 * garbage carries >= |fiber| distinct values (>= ceil(log2|fiber|) bits) -- the
 * Agda RWhileGarbageBound.garbage-injective-on-fiber.  We enumerate a finite
 * domain, group it into fibers, and check: (a) input-preserving g=x makes resid
 * injective and meets the bound exactly (Achievable), while (b) lossy g=nil makes
 * resid injective IFF S is already injective (necessity).  A non-reversible source
 * cannot be a valid R-WHILE program directly (it would violate all_cleared);
 * these S model the mathematical functions we must pay garbage to reverse. *)
let ceil_log2 n =
  let rec go acc p = if p >= n then acc else go (acc + 1) (p * 2) in
  if n <= 1 then 0 else go 0 1

let garbage () =
  (* enumerate trees with leaves in {nil,'a} up to a small depth, deduped *)
  let rec gen d =
    let leaves = [VNil; atom "'a"] in
    if d = 0 then leaves
    else let s = gen (d - 1) in
      leaves @ List.concat_map (fun l -> List.map (fun r -> VCons (l, r)) s) s in
  let dom = List.sort_uniq compare (gen 2) in
  let inj l = List.length (List.sort_uniq compare l) = List.length l in
  let max_fiber s =
    let outs = List.sort_uniq compare (List.map s dom) in
    List.fold_left (fun m o -> max m (List.length (List.filter (fun x -> s x = o) dom))) 0 outs,
    List.length outs in
  let sources =
    [ "hd",        (function VCons (a, _) -> a | v -> v);     (* drops cdr *)
      "tl",        (function VCons (_, b) -> b | v -> v);     (* drops car *)
      "atomize",   (function VCons _ -> atom "'c" | v -> v);  (* collapses all conses *)
      "const-nil", (fun _ -> VNil) ]                          (* maximally non-injective *)
  in
  Printf.printf "Garbage lower bound (|garbage| >= |fiber|): domain = %d trees\n" (List.length dom);
  Printf.printf "  %-10s %7s %8s %5s %6s %10s %9s\n"
    "source" "#fibers" "maxfib" "LB" "S-inj" "inputPres" "lossy";
  List.iter (fun (name, s) ->
      let mf, nf = max_fiber s in
      let s_inj = inj (List.map s dom) in
      let ip_inj = inj (List.map (fun x -> (s x, x)) dom) in        (* g = input *)
      let lossy_inj = inj (List.map (fun x -> (s x, VNil)) dom) in  (* g = nil *)
      Printf.printf "  %-10s %7d %8d %5d %6b %10s %9s\n" name nf mf (ceil_log2 mf) s_inj
        (if ip_inj then "inj(OK)" else "NONINJ") (if lossy_inj then "inj" else "NONINJ"))
    sources;
  Printf.printf "input-preserving (g=input) is injective for every source (Achievable: garbage=input\n";
  Printf.printf "  always suffices); lossy (g=nil) is injective only when S already is -- garbage is\n";
  Printf.printf "  NECESSARY exactly when maxfib>1, matching |garbage|>=|fiber| (RWhileGarbageBound).\n";
  exit 0

let jones spec_av =
  let ab = VCons (atom "'a", atom "'b") in
  let abc = vlist [atom "'a"; atom "'b"; atom "'c"] in
  let rimin = parse_prog (dir ^ "/ri_min.rwhile") in
  let riseq = parse_prog (dir ^ "/ri_seq.rwhile") in
  let riperm = parse_prog (dir ^ "/ri_perm.rwhile") in
  let sw = atom "'swap" and id = atom "'id" in
  let opab = atom "'ab" and opbc = atom "'bc" in
  let cases =
    [ ("ri_min",  rimin,  sw, ab, "swap");
      ("ri_min",  rimin,  id, ab, "id");
      ("ri_seq",  riseq,  vlist [sw], ab, "[swap]");
      ("ri_seq",  riseq,  vlist [sw; sw], ab, "[swap;swap]");
      ("ri_seq",  riseq,  vlist [sw; id; sw], ab, "[swap;id;swap]");
      ("ri_seq",  riseq,  vlist [sw; sw; sw; sw], ab, "[swap*4]");
      ("ri_seq",  riseq,  vlist [id; id; id; id; id; id], ab, "[id*6]");
      ("ri_perm", riperm, vlist [opab], abc, "[ab]");
      ("ri_perm", riperm, vlist [opbc], abc, "[bc]");
      ("ri_perm", riperm, vlist [opab; opbc], abc, "[ab;bc]");
      ("ri_perm", riperm, vlist [opab; opbc; opab], abc, "[ab;bc;ab]=rev") ]
  in
  Printf.printf "Jones optimality: fp1 residual exec-steps vs interpreter exec-steps\n";
  Printf.printf "  (loops = CLoop nodes in residual: 0 = compiled/loop-free; interpreters loop)\n";
  Printf.printf "  %-7s %-16s %8s %5s %7s %7s %7s\n" "interp" "program" "|resid|" "loops" "resid" "interp" "ratio";
  List.iter (fun (iname, iprog, src, d, label) ->
      let pd = Program2DataRwhile.program2data iprog in
      let b = EvalRwhile.evalProgram spec_av (spec_in pd src) in
      let bp = Program2DataRwhile.data2program b in
      EvalRwhile.reset_steps (); let ro = EvalRwhile.evalProgram bp d in
      let sr = EvalRwhile.get_steps () in
      EvalRwhile.reset_steps (); let io = EvalRwhile.evalProgram iprog (VCons (src, d)) in
      let si = EvalRwhile.get_steps () in
      Printf.printf "  %-7s %-16s %8d %5d %7d %7d %6.2fx%s\n" iname label (cn b) (body_loops bp) sr si
        (float_of_int sr /. float_of_int si) (if ro = io then "" else "  MISMATCH!"))
    cases;
  Printf.printf "interpreter loops: ri_min=%d ri_seq=%d ri_perm=%d (all unrolled to 0 in residuals)\n"
    (body_loops rimin) (body_loops riseq) (body_loops riperm);
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

(* diagnostic (BTI, gap B): collect the entry/exit test expressions of every
 * CLoop in a residual.  spec_av's store-walk AUX is
 *   from (=? Cnt nil) loop ... until (=? Cnt J)
 * so the EXIT test `=? Cnt J` carries the (residualised) store index J.  Under
 * self-application the 125 residual CLoops are these walks; the SHAPE of J shows
 * where the inner program pointer became dynamic (the binding-time leak). *)
let exp_str e = PrintRwhile.printTree PrintRwhile.prtExp e
let rec collect_loops acc = function
  | CSeq (a, b)        -> collect_loops (collect_loops acc a) b
  | CCond (_, t, e, _) -> cle (clt acc t) e
  | CLoop (en, d, l, ex) -> cll (cld ((en, ex) :: acc) d) l
  | CLocal (_, c)      -> collect_loops acc c
  | _ -> acc
and clt acc = function BThen c -> collect_loops acc c | BThenNone -> acc
and cle acc = function BElse c -> collect_loops acc c | BElseNone -> acc
and cld acc = function BDo c -> collect_loops acc c | BDoNone -> acc
and cll acc = function BLoop c -> collect_loops acc c | BLoopNone -> acc

let comp2_loops spec_av pd_spec pd_rimin spec_in =
  Printf.printf "computing comp2 = [spec_av]((spec_av.ri_min)) (slow)...\n%!";
  let comp2 = EvalRwhile.evalProgram spec_av (spec_in pd_spec pd_rimin) in
  let comp2_prog = Program2DataRwhile.data2program comp2 in
  let body = match comp2_prog with Prog (_, _, b, _) -> b in
  (let oc = open_out "/tmp/comp2_resid.rwhile" in
   output_string oc (PrintRwhile.printTree PrintRwhile.prtProgram comp2_prog);
   close_out oc;
   Printf.printf "(dumped residual to /tmp/comp2_resid.rwhile)\n%!");
  Printf.printf "comp2 = %d nodes  (ratio %.3f x |spec_av|)\n"
    (cn comp2) (float_of_int (cn comp2) /. float_of_int (cn pd_spec));
  (* CORRECTNESS: [comp2](('S.op)) must equal the fp1 residual B = [spec]((ri_min.op)).
   * Compares against B built with the SAME candidate specialiser. *)
  (let inp op = VCons (VAtom (Atom "'S"), VAtom (Atom op)) in
   let b_swap = EvalRwhile.evalProgram spec_av (spec_in pd_rimin (VAtom (Atom "'swap"))) in
   let b_id   = EvalRwhile.evalProgram spec_av (spec_in pd_rimin (VAtom (Atom "'id"))) in
   let r_swap = EvalRwhile.evalProgram comp2_prog (inp "'swap") in
   let r_id   = EvalRwhile.evalProgram comp2_prog (inp "'id") in
   Printf.printf "[comp2](('S.swap)) == B : %b\n" (r_swap = b_swap);
   Printf.printf "[comp2](('S.id))   == B : %b\n" (r_id = b_id);
   let snip v = let s = PrintRwhile.printTree PrintRwhile.prtValT v in
     if String.length s > 160 then String.sub s 0 160 ^ "..." else s in
   Printf.printf "  B_swap      (%d nodes): %s\n" (cn b_swap) (snip b_swap);
   Printf.printf "  [comp2]swap (%d nodes): %s\n" (cn r_swap) (snip r_swap));
  let loops = List.rev (collect_loops [] body) in
  Printf.printf "comp2 has %d CLoop(s).  Entry/exit test shapes (deduped, sorted by count):\n"
    (List.length loops);
  let tbl = Hashtbl.create 64 in
  List.iter (fun (en, ex) ->
      let key = "from " ^ exp_str en ^ "  until " ^ exp_str ex in
      Hashtbl.replace tbl key (1 + (try Hashtbl.find tbl key with Not_found -> 0)))
    loops;
  Hashtbl.fold (fun k c acc -> (c, k) :: acc) tbl []
  |> List.sort (fun (a, _) (b, _) -> compare b a)
  |> List.iter (fun (c, k) -> Printf.printf "  [x%d]  %s\n" c k)

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

(* dyncond: fp1-scale soundness probe for the DYNAMIC-cond/loop residualisation.
 * Specialise examples/fp_dyncond_bug.rwhile (a valid reversible program with a
 * dynamic-input conditional) with the candidate spec, then evaluate the residual:
 *   [comp](d) = 'one for non-nil d, 'two for d = nil.
 * If the selective-dynamicize 'cond path is unsound, this fp1-scale residual is
 * wrong (seconds, vs minutes for comp2). *)
let dyncond spec_file =
  let cand = parse_prog spec_file in
  let prog = parse_prog (dir ^ "/fp_dyncond_bug.rwhile") in
  let pd = Program2DataRwhile.program2data prog in
  let comp = EvalRwhile.evalProgram cand (spec_in pd VNil) in
  let comp_prog = Program2DataRwhile.data2program comp in
  let r1 = EvalRwhile.evalProgram comp_prog (VAtom (Atom "'x")) in
  let r2 = EvalRwhile.evalProgram comp_prog VNil in
  let s v = PrintRwhile.printTree PrintRwhile.prtValT v in
  Printf.printf "dyncond %s: comp=%d nodes ; [comp]('x)=%s (expect 'one) ; [comp](nil)=%s (expect 'two)\n"
    spec_file (cn comp) (s r1) (s r2)

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

(* encoding: attribute the nodes of the p2d encodings we care about.  comp2 is a
 * residual, but the QUESTION -- what is the encoding spending its nodes on --
 * is answered just as well by the programs comp2 is made of, and those encode in
 * milliseconds instead of minutes.  (`./measure_proj full` runs the same
 * breakdown on comp2 itself, to confirm the shape carries over.) *)
let encoding () =
  List.iter (fun name ->
      let p = parse_prog (dir ^ "/" ^ name ^ ".rwhile") in
      let r = Encoding.breakdown_program p in
      Encoding.print_report name r;
      Encoding.print_index_cost name r 8)
    [ "spec_av"; "spec"; "ri"; "ri_fp3"; "ri_min" ]

let () =
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "encoding" then (encoding (); exit 0);
  if Array.length Sys.argv >= 3 && Sys.argv.(1) = "gate" then gate Sys.argv.(2);
  if Array.length Sys.argv >= 3 && Sys.argv.(1) = "dyncond" then (dyncond Sys.argv.(2); exit 0);
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "jones" then
    jones (parse_prog (dir ^ "/spec_av.rwhile"));
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "garbage" then garbage ();
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
  (* ...and after copy propagation over the residual's moves (Simp.copyprop_program).
   * With capture-on-escape enabled in spec_av this is the number that matters: the
   * captures that are pure overhead are a write-once/read-once temp, i.e. a copy. *)
  let cp v = cn (Program2DataRwhile.program2data
                   (Simp.copyprop_program (Program2DataRwhile.data2program v))) in
  Printf.printf "  after copyprop:  swap = %d nodes (%.2fx |ri_min|)   id = %d nodes\n"
    (cp b_swap) (float_of_int (cp b_swap) /. float_of_int (cn pd_rimin)) (cp b_id);
  (* the copy-propagated residual must compute the SAME thing and still invert *)
  let cpp v = Simp.copyprop_program (Program2DataRwhile.data2program v) in
  let ab0 = VCons (VAtom (Atom "'a"), VAtom (Atom "'b")) in
  let bcp = cpp b_swap in
  Printf.printf "  copyprop correctness: [Bcp](('a.'b))=%s ; [inv Bcp](that)=%s\n"
    (PrintRwhile.printTree PrintRwhile.prtValT (EvalRwhile.evalProgram bcp ab0))
    (PrintRwhile.printTree PrintRwhile.prtValT
       (EvalRwhile.evalProgram (InvRwhile.invProgram bcp)
          (EvalRwhile.evalProgram bcp ab0)));
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
  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "comp2-loops" then begin
    (* optional argv.(2): use a CANDIDATE specialiser (e.g. spec_av_bti) for BOTH
     * outer and inner of the self-application comp2 = [SPEC]((SPEC.ri_min)). *)
    let spec_c, pd_c =
      if Array.length Sys.argv >= 3 then
        let s = parse_prog Sys.argv.(2) in (s, Program2DataRwhile.program2data s)
      else (spec_av, pd_spec) in
    comp2_loops spec_c pd_c pd_rimin spec_in; exit 0
  end;
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
    (* ...and with copy propagation on top of Simp: comp2 is itself a residual, so
     * the same write-once/read-once move fusion applies to the COMPILER. *)
    let comp2_cp = Simp.copyprop_program comp2_simp in
    let comp2_cp_d = Program2DataRwhile.program2data comp2_cp in
    Printf.printf "comp2 (+copyprop) = %d nodes  (%.1f%% of comp2, ratio %.3f x |spec_av|)\n"
      (cn comp2_cp_d)
      (100.0 *. float_of_int (cn comp2_cp_d) /. float_of_int (cn comp2))
      (float_of_int (cn comp2_cp_d) /. float_of_int nspec);
    (* WHY copy propagation cannot reach comp2's loop bodies: count the rejects *)
    let r = Simp.copyprop_report comp2_cp in
    Printf.printf
      "  copyprop rejects on comp2: moves=%d fused=%d | multi_occ=%d no_use=%d not_consuming=%d src_clobbered=%d\n"
      r.Simp.moves r.Simp.fused r.Simp.multi_occ r.Simp.no_use
      r.Simp.not_consuming r.Simp.src_clobbered;
    (* correctness: [comp2](('S.op)) and [comp2_simp](('S.op)) must equal the fp1
     * residual B (= [spec_av]((ri_min.op))). *)
    let inp op = VCons (VAtom (Atom "'S"), VAtom (Atom op)) in
    let r_orig = EvalRwhile.evalProgram comp2_prog (inp "'swap") in
    let r_simp = EvalRwhile.evalProgram comp2_simp (inp "'swap") in
    Printf.printf "[comp2](('S.swap)) == B : %b\n" (r_orig = b_swap);
    Printf.printf "[comp2_cp](('S.swap)) == B : %b\n"
      (EvalRwhile.evalProgram comp2_cp (inp "'swap") = b_swap);
    Printf.printf "[comp2_simp](('S.swap)) == B : %b   (preserves meaning)\n" (r_simp = b_swap);
    (* breakdown: what dominates comp2 (before/after Simp)? *)
    Printf.printf "breakdown (constructor histogram + nodes under loops):\n";
    (match comp2_prog with Prog (_, _, body, _) -> report_hist "comp2     " body);
    (match comp2_simp with Prog (_, _, body, _) -> report_hist "comp2_simp" body);
    (* ...and WHERE those nodes go (Encoding.breakdown; the categories add up to
     * count_nodes exactly).  ~113 nodes per command means the bulk is what each
     * command carries, so this is the table that says which term to attack. *)
    Encoding.print_report "comp2" (Encoding.breakdown comp2);
    Encoding.print_index_cost "comp2" (Encoding.breakdown comp2) 10;
    Encoding.print_report "comp2_cp" (Encoding.breakdown comp2_cp_d)
  end
