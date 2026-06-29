{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- H2 (self-representation) discharged for the STRUCTURAL specialiser model,
-- without the closure stand-in (case 2, the genuine prize beyond
-- RWhileFutamura2Inst).
--
-- RWhileFutamura2Inst makes H2 hold by a built-in `papp` constructor — a
-- closure: the specialiser is not a program in an object language, it is a
-- primitive of `run`.  Here we close H2's RECURSIVE CORE honestly: we exhibit
-- the real symbolic evaluator `aeval` (RWhileAVSpec) as a genuine PROGRAM —
-- data in an object language — run by a uniform, TOTAL interpreter.
--
-- The object language `E` is the AV-EXPRESSION language: exactly spec_av's AV
-- macros (AV-HD / AV-TL / AV-CONS / AV-EQ / AV-PAIRP) over the holes {the
-- static input, the two child results, the node payload}.  A *specialiser
-- program* is then a finite ALGEBRA `Alg` — one E-term per Code constructor —
-- mirroring spec_av's stepper SPEC-EXP-AV-STEP (which dispatches on the Code
-- tag and emits AV-macro calls).  The interpreter `cata` folds a Code with the
-- algebra; it is TOTAL because it recurses on the Code structure (`aeval` is
-- structurally terminating — the reason this is possible at all, where a
-- Turing-complete `run` could not be total under `--safe`).
--
-- Main results:
--   self-rep   : ∀ c a → cata specAlg c a ≡ aeval c a       -- aeval IS a program
--   specByProg-correct : the program-driven specialiser equals RWhileAVSpec.spec,
--                        hence inherits H1 (spec-correct).
--
-- So the modelled specialiser is BOTH correct (H1) AND self-represented by a
-- genuine data program under a uniform total interpreter (H2's core), with NO
-- closure constructor.  What remains for the FULL hierarchy instance on the
-- actual `spec_av` is only its non-structural part (the bounded worklist /
-- Turing-complete looping), which needs a fuel-indexed model — documented
-- future work (route A).  `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import RWhileAVSound using
  (Val; ⟨⟩; _·_; AV; S; D; C;
   avHd; avTl; avCons; avEq; avPairp)
open import RWhileAVSpec using (aeval; spec; spec-correct)
open import RWhileAVSound using (Code; cVar; cVal; cHd; cTl; cCons; cEq; cPairp; lift; ⟦_⟧c)
open import Relation.Binary.PropositionalEquality using (trans)

------------------------------------------------------------------------
-- The AV-expression object language E (= spec_av's AV macros), with holes:
--   eIn  = the threaded static input AV         (spec_av: the AV store entry)
--   eL   = the recursive result on the 1st child
--   eR   = the recursive result on the 2nd child
--   eVal = the node payload as a static AV `S v` (for cVal)

data E : Set where
  eIn    : E
  eL     : E
  eR     : E
  eVal   : E
  eHd    : E → E
  eTl    : E → E
  eCons  : E → E → E
  eEq    : E → E → E
  ePairp : E → E

-- Semantics of E: given the static input `a`, child results `l`,`r`, payload `v`.
evalE : E → AV → AV → AV → Val → AV
evalE eIn         a l r v = a
evalE eL          a l r v = l
evalE eR          a l r v = r
evalE eVal        a l r v = S v
evalE (eHd e)     a l r v = avHd   (evalE e a l r v)
evalE (eTl e)     a l r v = avTl   (evalE e a l r v)
evalE (eCons x y) a l r v = avCons (evalE x a l r v) (evalE y a l r v)
evalE (eEq x y)   a l r v = avEq   (evalE x a l r v) (evalE y a l r v)
evalE (ePairp e)  a l r v = avPairp (evalE e a l r v)

------------------------------------------------------------------------
-- A specialiser PROGRAM = an algebra: one E-term per Code constructor.

record Alg : Set where
  field
    aVar   : E
    aVal   : E
    aHd    : E
    aTl    : E
    aCons  : E
    aEq    : E
    aPairp : E
open Alg

-- The uniform, TOTAL interpreter: fold a Code with the algebra.  Unused child
-- slots get the dummy `S ⟨⟩`.  Structural recursion on the Code ⇒ total.

dummy : AV
dummy = S ⟨⟩

cata : Alg → Code → AV → AV
cata alg cVar        a = evalE (aVar alg)   a dummy            dummy            ⟨⟩
cata alg (cVal v)    a = evalE (aVal alg)   a dummy            dummy            v
cata alg (cHd c)     a = evalE (aHd alg)    a (cata alg c a)   dummy            ⟨⟩
cata alg (cTl c)     a = evalE (aTl alg)    a (cata alg c a)   dummy            ⟨⟩
cata alg (cCons x y) a = evalE (aCons alg)  a (cata alg x a)   (cata alg y a)   ⟨⟩
cata alg (cEq x y)   a = evalE (aEq alg)    a (cata alg x a)   (cata alg y a)   ⟨⟩
cata alg (cPairp c)  a = evalE (aPairp alg) a (cata alg c a)   dummy            ⟨⟩

------------------------------------------------------------------------
-- The specialiser, AS A PROGRAM: the algebra that mirrors `aeval`.

specAlg : Alg
specAlg = record
  { aVar   = eIn
  ; aVal   = eVal
  ; aHd    = eHd eL
  ; aTl    = eTl eL
  ; aCons  = eCons eL eR
  ; aEq    = eEq eL eR
  ; aPairp = ePairp eL
  }

------------------------------------------------------------------------
-- H2's recursive core: the genuine data program `specAlg`, run by the uniform
-- total interpreter `cata`, computes EXACTLY the real symbolic evaluator.

self-rep : ∀ c a → cata specAlg c a ≡ aeval c a
self-rep cVar        a = refl
self-rep (cVal v)    a = refl
self-rep (cHd c)     a = cong  avHd   (self-rep c a)
self-rep (cTl c)     a = cong  avTl   (self-rep c a)
self-rep (cCons x y) a = cong₂ avCons (self-rep x a) (self-rep y a)
self-rep (cEq x y)   a = cong₂ avEq   (self-rep x a) (self-rep y a)
self-rep (cPairp c)  a = cong  avPairp (self-rep c a)

------------------------------------------------------------------------
-- The program-driven specialiser equals RWhileAVSpec.spec, so it inherits H1
-- (spec-correct).  `spec p s = lift (aeval p (C (S s) (D cVar)))`.

specByProg : Code → Val → Code
specByProg p s = lift (cata specAlg p (C (S s) (D cVar)))

specByProg-correct : ∀ p s → specByProg p s ≡ spec p s
specByProg-correct p s = cong lift (self-rep p (C (S s) (D cVar)))

------------------------------------------------------------------------
-- H1 for the SELF-REPRESENTED specialiser: composing H2's structural core
-- (specByProg-correct: the data program `specAlg` run by `cata` equals the real
-- `spec`) with H1 (spec-correct) gives that the program-driven specialiser is
-- itself fp1-correct -- the residual it BUILDS AS A PROGRAM, run on d, equals the
-- source run on the paired input s · d.  This is the structural-level connection
-- of the real AV specialiser to the Futamura fp1, with the specialiser realised
-- as honest data (no closure primitive).

specByProg-H1 : ∀ p s d → ⟦ specByProg p s ⟧c d ≡ ⟦ p ⟧c (s · d)
specByProg-H1 p s d =
  trans (cong (λ z → ⟦ z ⟧c d) (specByProg-correct p s))
        (spec-correct p s d)

------------------------------------------------------------------------
-- Witnesses: the data-program specialiser on concrete Code, checked concretely.

module Witness where
  -- the data program `specAlg` run by `cata` on a concrete Code computes exactly
  -- the real symbolic evaluator (a closed instance of self-rep).
  rep-cons : cata specAlg (cCons cVar (cVal ⟨⟩)) (C (S ⟨⟩) (D cVar))
           ≡ aeval (cCons cVar (cVal ⟨⟩)) (C (S ⟨⟩) (D cVar))
  rep-cons = refl

  -- specialising the projection `cTl cVar` (return the dynamic half), AS A DATA
  -- PROGRAM, yields a residual equal to the identity on the runtime input d.
  proj-id : ∀ s d → ⟦ specByProg (cTl cVar) s ⟧c d ≡ d
  proj-id s d = specByProg-H1 (cTl cVar) s d
