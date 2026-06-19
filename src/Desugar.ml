(* Desugar.ml -- surface-syntax desugaring that runs BEFORE macro expansion,
   inversion, evaluation and program-to-data.  Currently handles the symmetric
   reversible match, with any number (>= 2) of arms:

       case Scrut yields Result of
           InPat1 => Body1 => OutPat1
         | InPat2 => Body2 => OutPat2
         | ...
         | InPatN => BodyN => OutPatN
       end

   It expands to a NEST of plain reversible conditionals, so every downstream
   pass (EvalRwhile / InvRwhile / Program2DataRwhile / the self-interpreter and
   spec_av) sees only core constructs and needs no change.  For two arms:

       if  <test InPat1 on Scrut>  then
           InPat1 <= Scrut ;  Body1 ;  Result <= OutPat1
       else
           InPat2 <= Scrut ;  Body2 ;  Result <= OutPat2
       fi  <test OutPat1 on Result>

   For N arms the else-branch recursively becomes the desugaring of arms 2..N;
   the LAST arm needs no test (it is the fall-through and may use a variable
   input pattern as a catch-all).

   Each arm's entry test is synthesised from its input pattern and its exit
   assertion from its output pattern.  Reversibility / invertibility is
   guaranteed by a well-formedness check on top-level shapes (cons / nil / atom):

     - the OUTPUT patterns of all arms must have pairwise-DISTINCT shapes, so the
       exit assertion at every nesting level is FALSE in the else-branch;
     - the INPUT patterns of every arm but the last must be concrete and have
       pairwise-distinct shapes (the last arm's input may be a variable). *)

open AbsRwhile

exception Desugar_error of string
let err msg = raise (Desugar_error ("case: " ^ msg))

(* Top-level shape of a pattern, used to synthesise the dispatch tests. *)
type shape = SCons | SNil | SAtom of string

let shape_of_pat : pat -> shape = function
  | PCons _              -> SCons
  | PVal (VCons _)       -> SCons
  | PVal (VList (_ :: _))-> SCons
  | PVal VNil            -> SNil
  | PVal (VList [])      -> SNil
  | PVal (VAtom (Atom a))-> SAtom a
  | PList (_ :: _)       -> SCons
  | PList []             -> SNil
  | PVar _               -> err "a variable pattern has no fixed shape here"

(* An expression that is TRUE iff variable [v] currently has shape [s]. *)
let test_of_shape (v : rIdent) (s : shape) : exp =
  let var = EVar (Var v) in
  match s with
  | SCons   -> EPair var
  | SNil    -> EEq (var, EVal VNil)
  | SAtom a -> EEq (var, EVal (VAtom (Atom a)))

let rec pairwise_distinct = function
  | [] | [_] -> true
  | x :: xs  -> (not (List.mem x xs)) && pairwise_distinct xs

let seq3 a b c = CSeq (CSeq (a, b), c)

let rec desugar_com (c : com) : com =
  match c with
  | CCase (scrut, result, arms) -> desugar_case scrut result arms
  (* structural recursion *)
  | CSeq (a, b)            -> CSeq (desugar_com a, desugar_com b)
  | CCond (e, t, el, f)    -> CCond (e, desugar_then t, desugar_else el, f)
  | CLoop (e, d, l, f)     -> CLoop (e, desugar_do d, desugar_loop l, f)
  | CLocal (x, body)       -> CLocal (x, desugar_com body)
  | CAutoFi (e, t, el)     -> CAutoFi (e, desugar_then t, desugar_else el)
  (* leaves with no nested command *)
  | CMac _ | CAss _ | CRep _ | CShow _ | CArrAss _ -> c

and desugar_then = function BThen c -> BThen (desugar_com c) | BThenNone -> BThenNone
and desugar_else = function BElse c -> BElse (desugar_com c) | BElseNone -> BElseNone
and desugar_do   = function BDo c   -> BDo   (desugar_com c) | BDoNone   -> BDoNone
and desugar_loop = function BLoop c -> BLoop (desugar_com c) | BLoopNone -> BLoopNone

and desugar_case scrut result arms =
  let n = List.length arms in
  if n < 2 then err "needs at least two arms (InPat => Body => OutPat | ...)";
  (* Output shapes must be pairwise distinct: this is what makes every exit
     assertion FALSE in its else-branch, hence the nest invertible. *)
  let out_shapes = List.map (fun (ACase (_, _, out)) -> shape_of_pat out) arms in
  if not (pairwise_distinct out_shapes) then
    err "the output patterns must have pairwise-distinct top shapes \
         (cons / nil / atom) so each exit assertion separates its arm";
  (* Input shapes: every arm but the last needs a concrete shape for its entry
     test, and those shapes (plus the last if concrete) must be distinct so no
     earlier arm shadows a later one.  The last arm's input may be a variable. *)
  let in_shapes =
    List.concat (List.mapi
      (fun i (ACase (inp, _, _)) ->
         match inp with
         | PVar _ when i = n - 1 -> []          (* last arm: variable catch-all *)
         | PVar _ -> err "only the LAST arm's input may be a variable; \
                          every earlier arm needs a concrete pattern (cons/nil/atom)"
         | _ -> [shape_of_pat inp])
      arms) in
  if not (pairwise_distinct in_shapes) then
    err "the input patterns must have pairwise-distinct top shapes \
         (only the last arm may be a variable catch-all)";
  desugar_arms scrut result arms

(* Build the nested conditional.  The last arm is the fall-through (no test). *)
and desugar_arms scrut result = function
  | [ ACase (inp, body, out) ] ->
     seq3 (CRep (inp, PVar (Var scrut))) (desugar_com body) (CRep (PVar (Var result), out))
  | ACase (inp, body, out) :: rest ->
     let then_com =
       seq3 (CRep (inp, PVar (Var scrut))) (desugar_com body) (CRep (PVar (Var result), out)) in
     CCond (test_of_shape scrut (shape_of_pat inp),
            BThen then_com,
            BElse (desugar_arms scrut result rest),
            test_of_shape result (shape_of_pat out))
  | [] -> err "needs at least two arms"   (* unreachable: guarded above *)

let desugar_macro (Mac (name, params, body)) = Mac (name, params, desugar_com body)

let desugar_program (Prog (macros, x, c, y)) =
  Prog (List.map desugar_macro macros, x, desugar_com c, y)
