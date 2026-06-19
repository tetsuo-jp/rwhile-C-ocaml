(* Desugar.ml -- surface-syntax desugaring that runs BEFORE macro expansion,
   inversion, evaluation and program-to-data.  Currently handles the symmetric
   reversible match:

       case Scrut yields Result of
           InPat1 => Body1 => OutPat1
         | InPat2 => Body2 => OutPat2
       end

   It expands to a plain reversible conditional, so every downstream pass
   (EvalRwhile / InvRwhile / Program2DataRwhile / the self-interpreter and
   spec_av) sees only core constructs and needs no change:

       if  <test InPat1 on Scrut>  then
           InPat1 <= Scrut ;  Body1 ;  Result <= OutPat1
       else
           InPat2 <= Scrut ;  Body2 ;  Result <= OutPat2
       fi  <test OutPat1 on Result>

   The entry test is synthesised from the FIRST arm's input pattern and the exit
   assertion from the FIRST arm's output pattern.  Reversibility of the result is
   guaranteed by a well-formedness check: the two input patterns and the two
   output patterns must each have DISJOINT top-level shapes (cons / nil / atom),
   so a single shape test cleanly separates the branches both ways.  (The second
   input pattern may instead be a variable: a catch-all "else" arm.) *)

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
  match arms with
  | [ ACase (in1, body1, out1); ACase (in2, body2, out2) ] ->
     let s_in1 = shape_of_pat in1 in
     (* second input pattern: either a catch-all variable, or a disjoint shape *)
     (match in2 with
      | PVar _ -> ()
      | _ -> if shape_of_pat in2 = s_in1 then
               err "the two input patterns must have disjoint top shapes \
                    (or make the second arm a variable catch-all)");
     let s_out1 = shape_of_pat out1 and s_out2 = shape_of_pat out2 in
     if s_out1 = s_out2 then
       err "the two output patterns must have disjoint top shapes \
            (cons / nil / atom) so the exit assertion can separate the arms";
     let entry = test_of_shape scrut s_in1 in
     let exit  = test_of_shape result s_out1 in
     let scrut_pat  = PVar (Var scrut) in
     let result_pat = PVar (Var result) in
     let then_com =
       seq3 (CRep (in1, scrut_pat)) (desugar_com body1) (CRep (result_pat, out1)) in
     let else_com =
       seq3 (CRep (in2, scrut_pat)) (desugar_com body2) (CRep (result_pat, out2)) in
     CCond (entry, BThen then_com, BElse else_com, exit)
  | _ -> err "v1 supports exactly two arms (InPat => Body => OutPat | ... )"

let desugar_macro (Mac (name, params, body)) = Mac (name, params, desugar_com body)

let desugar_program (Prog (macros, x, c, y)) =
  Prog (List.map desugar_macro macros, x, desugar_com c, y)
