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

     - the OUTPUT patterns of all arms must have pairwise-DISJOINT discriminants,
       so the exit assertion at every nesting level is FALSE in the else-branch;
     - the INPUT patterns of every arm but the last must be concrete with
       pairwise-disjoint discriminants (the last arm may be a variable catch-all).

   A discriminant is the top shape (cons / nil / atom) OR -- for a cons pattern
   whose head is a literal atom -- that head atom, tested by (=? (hd v) atom).
   This lets a case dispatch on a node tag (cons VAR A => ... | cons VAL B ...). *)

open AbsRwhile

exception Desugar_error of string
let err msg = raise (Desugar_error ("case: " ^ msg))

(* The discriminant of a pattern: the single test on the scrutinee/result
   variable that decides this arm.  Beyond the top shape (cons/nil/atom) we also
   support a cons whose HEAD is a literal atom (pattern  cons TAG P), dispatched
   by  =? (hd v) TAG.  That is exactly what the pattern-tag steppers need, e.g.
   the PAT- macros that do  if =? (hd PP) VAR then ... . *)
type disc =
  | DAtom of string   (* v = the atom                              *)
  | DNil              (* v = nil                                   *)
  | DHead of string   (* hd v = the atom (cons with literal head)  *)
  | DPair             (* pair? v        (cons with non-literal head) *)

let disc_of_pat : pat -> disc = function
  | PCons (PVal (VAtom (Atom a)), _) -> DHead a
  | PCons _                          -> DPair
  | PVal (VCons (VAtom (Atom a), _)) -> DHead a
  | PVal (VCons _)                   -> DPair
  | PVal (VList (_ :: _))            -> DPair
  | PList (_ :: _)                   -> DPair
  | PVal VNil | PVal (VList []) | PList [] -> DNil
  | PVal (VAtom (Atom a))            -> DAtom a
  | PVar _ -> err "a variable pattern has no fixed discriminant here"

(* An expression that is TRUE iff variable [v] currently matches discriminant [d]. *)
let test_of_disc (v : rIdent) (d : disc) : exp =
  let var = EVar (Var v) in
  match d with
  | DPair   -> EPair var
  | DNil    -> EEq (var, EVal VNil)
  | DAtom a -> EEq (var, EVal (VAtom (Atom a)))
  | DHead a -> EEq (EHd var, EVal (VAtom (Atom a)))

(* Two discriminants are disjoint when no value satisfies both -- so one test
   cleanly separates the arms forwards and backwards.  Note a cons with a given
   head (DHead) is also a pair (DPair), so those two are NOT disjoint. *)
let disjoint (d1 : disc) (d2 : disc) : bool =
  match d1, d2 with
  | DAtom a, DAtom b -> a <> b
  | DHead a, DHead b -> a <> b
  | DNil, DNil | DPair, DPair -> false
  | DHead _, DPair | DPair, DHead _ -> false
  | _ -> true   (* atom vs nil vs cons are always disjoint *)

let rec pairwise_disjoint = function
  | [] | [_] -> true
  | x :: xs  -> List.for_all (disjoint x) xs && pairwise_disjoint xs

let seq3 a b c = CSeq (CSeq (a, b), c)

(* ---------------------------------------------------------------- *)
(* Sugar added 2026-08-05.  Each form below expands to existing R-WHILE
   syntax, so the interpreter, the inverter, `-p2d` and the
   self-interpreters need no new cases.

     skip                       ->  if 't fi 't          (a no-op, 1 step)
     assert E                   ->  if E fi 't           (fails when E is false:
                                    the else branch is taken and the exit
                                    assertion 't does not hold)
     X <-> Y                    ->  cons X Y <= cons Y X (1 step)
     local X = E in C
       delocal X = F end        ->  X ^= E; C; X ^= F
     for X = A to B do C end    ->  X ^= A ;
                                    from (=? X A) do C loop <X++> until (=? X B) ;
                                    X ^= B

     push X S                   ->  S <= cons X S        (X is left nil)
     pop  X S                   ->  cons X S <= S        (fails if S is not a cons)

   push and pop are exact inverses of each other, which falls out of the
   desugaring for free: inverting a replacement swaps its two patterns.  The two
   variable names must differ (S <= cons S S would read S twice).

   The counter step <X++> is the four-assignment increment on unary numerals
   (X := (nil . X)) that needs one fresh scratch variable -- the same idiom the
   verified interpreter uses (proofs/agda/RWhileSIMac.incC).

   The counter X is loop-LOCAL: it is nil before and after, so a for-loop keeps
   the store invariant that makes a program reversible (all_cleared).  The body
   runs at least once (A = B runs it exactly once), and B must be A extended by
   some number of nils -- otherwise the loop diverges, exactly as the underlying
   from/until does. *)

let vtrue = EVal (VAtom (Atom "'t"))

let fresh_counter = ref 0
let fresh_var () =
  incr fresh_counter;
  RIdent (Printf.sprintf "FOR-T-%d" !fresh_counter)

(* X := (nil . X), reversibly, via a fresh scratch T *)
let incr_unary (x : rIdent) : com =
  let t = fresh_var () in
  CSeq (CAss (t, ECons (EVal VNil, EVar (Var x))),
  CSeq (CAss (x, ETl (EVar (Var t))),
  CSeq (CAss (x, EVar (Var t)),
        CAss (t, EVar (Var x)))))

let rec desugar_com (c : com) : com =
  match c with
  | CCase (scrut, result, arms) -> desugar_case scrut result arms
  (* sugar *)
  | CSkip                  -> CCond (vtrue, BThenNone, BElseNone, vtrue)
  | CAssert e              -> CCond (e, BThenNone, BElseNone, vtrue)
  | CSwap (x, y)           -> CRep (PCons (PVar (Var x), PVar (Var y)),
                                    PCons (PVar (Var y), PVar (Var x)))
  | CLocalD (x, e, body, y, f) ->
     if x <> y then
       raise (Desugar_error "local/delocal: the two variable names must agree")
     else
       CSeq (CAss (x, e), CSeq (desugar_com body, CAss (x, f)))
  | CPush (x, s) ->
     if x = s then raise (Desugar_error "push: the two variables must differ")
     else CRep (PVar (Var s), PCons (PVar (Var x), PVar (Var s)))
  | CPop (x, s) ->
     if x = s then raise (Desugar_error "pop: the two variables must differ")
     else CRep (PCons (PVar (Var x), PVar (Var s)), PVar (Var s))
  | CFor (x, a, b, body) ->
     CSeq (CAss (x, a),
     CSeq (CLoop (EEq (EVar (Var x), a),
                  BDo (desugar_com body),
                  BLoop (incr_unary x),
                  EEq (EVar (Var x), b)),
           CAss (x, b)))
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
  (* Collect the concrete discriminants of one side (input/output).  A variable
     pattern carries no discriminant and is allowed only on the LAST arm: as an
     input it is the catch-all, as an output it is the untested fall-through. *)
  let discs side sel =
    List.concat (List.mapi
      (fun i arm ->
         match sel arm with
         | PVar _ when i = n - 1 -> []
         | PVar _ -> err ("only the LAST arm's " ^ side ^ " pattern may be a variable; \
                           every earlier arm needs a concrete pattern \
                           (cons / cons 'tag / nil / atom)")
         | p -> [disc_of_pat p])
      arms) in
  if not (pairwise_disjoint (discs "input" (fun (ACase (i,_,_)) -> i))) then
    err "the input patterns must have pairwise-disjoint discriminants \
         (only the last arm may be a variable catch-all)";
  if not (pairwise_disjoint (discs "output" (fun (ACase (_,_,o)) -> o))) then
    err "the output patterns must have pairwise-disjoint discriminants \
         so each exit assertion separates its arm";
  desugar_arms scrut result arms

(* Build the nested conditional.  The last arm is the fall-through (no test). *)
and desugar_arms scrut result = function
  | [ ACase (inp, body, out) ] ->
     seq3 (CRep (inp, PVar (Var scrut))) (desugar_com body) (CRep (PVar (Var result), out))
  | ACase (inp, body, out) :: rest ->
     let then_com =
       seq3 (CRep (inp, PVar (Var scrut))) (desugar_com body) (CRep (PVar (Var result), out)) in
     CCond (test_of_disc scrut (disc_of_pat inp),
            BThen then_com,
            BElse (desugar_arms scrut result rest),
            test_of_disc result (disc_of_pat out))
  | [] -> err "needs at least two arms"   (* unreachable: guarded above *)

let desugar_macro (Mac (name, params, body)) = Mac (name, params, desugar_com body)

let desugar_program (Prog (macros, x, c, y)) =
  Prog (List.map desugar_macro macros, x, desugar_com c, y)
