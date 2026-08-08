(* Encoding: where do the nodes of a p2d-encoded program actually GO?
 *
 * Motivation (2026-08-08).  comp2 = [spec_av]((spec_av.ri_min)) is ~400k nodes
 * for ~1040 commands, i.e. ~113 nodes per command, and copy propagation cannot
 * shrink it (measured: 21 fusable moves in the whole program -- see the note at
 * the end of Simp.ml).  So the bulk is NOT the command count; it is what each
 * command CARRIES.  Before trying to shrink the encoding, attribute the nodes.
 *
 * The categories follow Program2DataRwhile.transProgram exactly:
 *
 *   var_index   the UNARY numeral of a variable occurrence.  Index k costs
 *               2k-1 nodes (k-1 conses + k nils), so a program with n variables
 *               pays O(n) per occurrence of a cold one.  This is the term that
 *               pass 1 (access-weight numbering, Optimize.var_order) halves.
 *   var_header  the 2 nodes every variable occurrence pays besides its numeral
 *               (the cons and the 'var atom).
 *   const       the payload of a 'val, i.e. a literal embedded in the program.
 *   const_header  the 2 nodes of the 'val wrapper.
 *   exp_struct / pat_struct / com_struct / prog_struct
 *               the tag atoms and spine conses of expressions, patterns,
 *               commands and the program wrapper.
 *
 * INVARIANT (checked by the `encoding-breakdown` test group, and cheap enough to
 * assert at every call): the eight categories sum to EvalRwhile.count_nodes of
 * the same value.  An accounting that does not add up is worse than none -- it
 * would send the next optimisation after the wrong term. *)

open AbsRwhile

type report = {
  mutable var_index    : int;
  mutable var_header   : int;
  mutable const        : int;
  mutable const_header : int;
  mutable exp_struct   : int;
  mutable pat_struct   : int;
  mutable com_struct   : int;
  mutable prog_struct  : int;
  (* diagnostics that are not part of the sum *)
  mutable var_occs     : int;                 (* variable occurrences *)
  mutable const_occs   : int;                 (* 'val occurrences *)
  mutable max_index    : int;                 (* largest unary index seen *)
  mutable idx_hist     : (int, int) Hashtbl.t; (* index -> occurrences *)
}

let empty () = {
  var_index = 0; var_header = 0; const = 0; const_header = 0;
  exp_struct = 0; pat_struct = 0; com_struct = 0; prog_struct = 0;
  var_occs = 0; const_occs = 0; max_index = 0; idx_hist = Hashtbl.create 97;
}

let total r =
  r.var_index + r.var_header + r.const + r.const_header
  + r.exp_struct + r.pat_struct + r.com_struct + r.prog_struct

let cn = EvalRwhile.count_nodes

(* A variable's index is the unary numeral of Program2DataRwhile.transRIdent:
 * VNil for 0, VCons (VNil, rest) for a successor.  We count both its nodes and
 * its value, so the histogram can show the tail. *)
let rec index_value = function
  | VNil -> 0
  | VCons (VNil, t) -> 1 + index_value t
  | v -> failwith ("Encoding: malformed variable index: "
                   ^ PrintRwhile.printTree PrintRwhile.prtValT v)

let count_var r idx =
  let k = index_value idx in
  r.var_occs <- r.var_occs + 1;
  r.var_header <- r.var_header + 2;          (* the cons and the 'var atom *)
  r.var_index <- r.var_index + cn idx;
  if k > r.max_index then r.max_index <- k;
  Hashtbl.replace r.idx_hist k (1 + (try Hashtbl.find r.idx_hist k with Not_found -> 0))

let count_const r v =
  r.const_occs <- r.const_occs + 1;
  r.const_header <- r.const_header + 2;      (* the cons and the 'val atom *)
  r.const <- r.const + cn v

let rec walk_exp r = function
  | VCons (VAtom (Atom "'var"), i) -> count_var r i
  | VCons (VAtom (Atom "'val"), v) -> count_const r v
  | VCons (VAtom (Atom "'cons"), VCons (a, b))
  | VCons (VAtom (Atom "'eq"), VCons (a, b)) ->
     r.exp_struct <- r.exp_struct + 3; walk_exp r a; walk_exp r b
  | VCons (VAtom (Atom ("'hd" | "'tl" | "'pairp")), e) ->
     r.exp_struct <- r.exp_struct + 2; walk_exp r e
  | v -> failwith ("Encoding: malformed expression: "
                   ^ PrintRwhile.printTree PrintRwhile.prtValT v)

let rec walk_pat r = function
  | VCons (VAtom (Atom "'var"), i) -> count_var r i
  | VCons (VAtom (Atom "'val"), v) -> count_const r v
  | VCons (VAtom (Atom "'cons"), VCons (a, b)) ->
     r.pat_struct <- r.pat_struct + 3; walk_pat r a; walk_pat r b
  | v -> failwith ("Encoding: malformed pattern: "
                   ^ PrintRwhile.printTree PrintRwhile.prtValT v)

let rec walk_com r = function
  | VCons (VAtom (Atom "'seq"), VCons (a, b)) ->
     r.com_struct <- r.com_struct + 3; walk_com r a; walk_com r b
  | VCons (VAtom (Atom "'ass"), VCons (VCons (VAtom (Atom "'var"), i), e)) ->
     (* outer cons + 'ass atom + inner cons; the target's own cons/'var/index are
      * charged to the variable categories by count_var *)
     r.com_struct <- r.com_struct + 3; count_var r i; walk_exp r e
  | VCons (VAtom (Atom "'rep"), VCons (p, q)) ->
     r.com_struct <- r.com_struct + 3; walk_pat r p; walk_pat r q
  | VCons (VAtom (Atom ("'cond" | "'loop")),
           VCons (e, VCons (a, VCons (b, VCons (f, VNil))))) ->
     (* 5 conses + the tag atom + the terminating nil *)
     r.com_struct <- r.com_struct + 7;
     walk_exp r e; walk_com r a; walk_com r b; walk_exp r f
  | v -> failwith ("Encoding: malformed command: "
                   ^ PrintRwhile.printTree PrintRwhile.prtValT v)

(* Attribute every node of a p2d-encoded program.  Raises if the value is not a
 * well-formed encoding, or if the categories fail to add up to count_nodes. *)
let breakdown (v : valT) : report =
  let r = empty () in
  (match v with
   | VCons (VCons (VAtom (Atom "'var"), i),
            VCons (c, VCons (VAtom (Atom "'var"), j))) ->
      r.prog_struct <- r.prog_struct + 2;    (* the two spine conses *)
      count_var r i; walk_com r c; count_var r j
   | _ -> failwith "Encoding: malformed program");
  if total r <> cn v then
    failwith (Printf.sprintf "Encoding: breakdown does not add up: %d vs %d"
                (total r) (cn v));
  r

let breakdown_program (p : program) : report =
  breakdown (Program2DataRwhile.program2data p)

(* The most expensive variables, as (index, occurrences, nodes spent).  Sorted by
 * nodes spent, descending -- the renumbering passes are exactly a permutation of
 * this table, so it shows how much is still on the table. *)
let index_cost (r : report) : (int * int * int) list =
  Hashtbl.fold (fun k occs acc -> (k, occs, occs * (2 * k + 1)) :: acc) r.idx_hist []
  |> List.sort (fun (_, _, a) (_, _, b) -> compare b a)

(* THE HEADROOM LEFT IN RENUMBERING, exactly.
 *
 * var_index is  sum over variables of  occ(v) * (2 * rank(v) + 1),  where rank is
 * the position in the p2d numbering.  Renumbering is exactly a permutation of the
 * ranks, so by the rearrangement inequality the MINIMUM over all numberings is
 * obtained by sorting the occurrence counts descending and handing out ranks
 * 0, 1, 2, ...  That is a closed-form lower bound on what ANY renumbering pass
 * (pass 1, pass 3, or a future one) can achieve, computable from the histogram
 * alone -- no search over the 240! permutations.
 *
 * It is a bound on the ENCODING SIZE objective only.  Pass 3 optimises a
 * different one (the size of the RESIDUAL, where only dynamic variables survive),
 * so a numbering can be worse here and better there. *)
let optimal_var_index (r : report) : int =
  let occs = Hashtbl.fold (fun _ occ acc -> occ :: acc) r.idx_hist [] in
  let sorted = List.sort (fun a b -> compare b a) occs in
  let (total, _) =
    List.fold_left (fun (sum, rank) occ -> (sum + occ * (2 * rank + 1), rank + 1))
      (0, 0) sorted in
  total

(* WHAT A NON-UNARY NUMERAL WOULD COST, exactly.
 *
 * Renumbering can only permute the ranks; it cannot change that rank k costs
 * 2k+1 nodes.  The other lever is the numeral itself.  This computes the
 * var_index total under a bit-list representation, so the two levers can be
 * compared with one number each instead of with a guess:
 *
 *   index k  ->  its bits, least significant first, as a nil-terminated list.
 *                bit 0 is nil (1 node), bit 1 is (nil.nil) (3 nodes); the list
 *                of m bits adds m conses and the terminating nil.
 *   nodes(k) = 1 + sum over bits (1 + (1 or 3)),  nodes(0) = 1.
 *
 * NOT IMPLEMENTED, and the number is only half the decision: every artifact that
 * WALKS an index -- ri.rwhile's and ri_fp3.rwhile's store access, spec_av's AV
 * store, the Agda core -- decrements a unary numeral, and would need reversible
 * binary decrement instead.  The point of computing it here is to know whether
 * that work could possibly pay before starting it. *)
let bits_nodes (k : int) : int =
  if k = 0 then 1
  else begin
    let n = ref k and acc = ref 1 in
    while !n > 0 do
      acc := !acc + 1 + (if !n land 1 = 1 then 3 else 1);
      n := !n lsr 1
    done;
    !acc
  end

let binary_var_index (r : report) : int =
  Hashtbl.fold (fun k occ acc -> acc + occ * bits_nodes k) r.idx_hist 0

(* ...and the same under the best renumbering, since the two levers compose:
 * with a bit-list numeral, cost grows with log(rank), so the hottest variables
 * should still get the smallest ranks. *)
let binary_var_index_optimal (r : report) : int =
  let occs = Hashtbl.fold (fun _ occ acc -> occ :: acc) r.idx_hist [] in
  let sorted = List.sort (fun a b -> compare b a) occs in
  let (total, _) =
    List.fold_left (fun (sum, rank) occ -> (sum + occ * bits_nodes rank, rank + 1))
      (0, 0) sorted in
  total

let print_report name (r : report) =
  let t = total r in
  let pc n = 100.0 *. float_of_int n /. float_of_int t in
  Printf.printf "  [%s] %d nodes total\n" name t;
  let opt = optimal_var_index r in
  Printf.printf "  [%s]   var_index    %8d (%5.1f%%)  %d occurrences, max index %d\n"
    name r.var_index (pc r.var_index) r.var_occs r.max_index;
  Printf.printf "  [%s]     best possible renumbering: %d (%.1f%% of current; saves %d nodes = %.1f%% of the program)\n"
    name opt (100.0 *. float_of_int opt /. float_of_int r.var_index)
    (r.var_index - opt) (pc (r.var_index - opt));
  let bin = binary_var_index r and binopt = binary_var_index_optimal r in
  Printf.printf "    [%s]   hypothetical bit-list numeral: %d (%d renumbered) -> program %d -> %d nodes (%.2fx)\n"
    name bin binopt (t - r.var_index + bin) (t - r.var_index + binopt)
    (float_of_int (t - r.var_index + binopt) /. float_of_int t);
  Printf.printf "  [%s]   var_header   %8d (%5.1f%%)\n" name r.var_header (pc r.var_header);
  Printf.printf "  [%s]   const        %8d (%5.1f%%)  %d occurrences\n"
    name r.const (pc r.const) r.const_occs;
  Printf.printf "  [%s]   const_header %8d (%5.1f%%)\n" name r.const_header (pc r.const_header);
  Printf.printf "  [%s]   exp_struct   %8d (%5.1f%%)\n" name r.exp_struct (pc r.exp_struct);
  Printf.printf "  [%s]   pat_struct   %8d (%5.1f%%)\n" name r.pat_struct (pc r.pat_struct);
  Printf.printf "  [%s]   com_struct   %8d (%5.1f%%)\n" name r.com_struct (pc r.com_struct);
  Printf.printf "  [%s]   prog_struct  %8d (%5.1f%%)\n" name r.prog_struct (pc r.prog_struct)

let print_index_cost name (r : report) k =
  let rows = index_cost r in
  let shown = List.filteri (fun i _ -> i < k) rows in
  Printf.printf "  [%s] most expensive variable indices (index, occurrences, nodes):\n" name;
  List.iter (fun (idx, occs, nodes) ->
      Printf.printf "  [%s]   %5d %7d %9d\n" name idx occs nodes) shown;
  let rest = List.fold_left (fun acc (_, _, n) -> acc + n) 0
               (List.filteri (fun i _ -> i >= k) rows) in
  Printf.printf "  [%s]   ... %d further indices, %d nodes\n"
    name (List.length rows - List.length shown) rest
