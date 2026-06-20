{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The Futamura hierarchy for the REAL AV machinery in ONE universal value
-- type (case 2 / gap G1's remaining bridge H2).
--
-- RWhileFutamura2 proves fp1/fp2/fp3 modularly from H1 (spec-correct) and
-- H2 (spec-impl), but in an abstract universal type U.  RWhileAVSpec proved
-- H1 for the actual AV evaluator, yet over TWO types (Code for programs,
-- Val for data).  To talk about self-application at all one needs programs
-- and data in ONE type — that is what RWhileP2D's encoding provides.
--
-- Here we set U = Val and use program2data/data2program to make the real
-- residual evaluator act on a single value type:
--
--     runU  pv d  = ⟦ data2program pv ⟧c d              -- decode prog, run
--     specU pv sv = program2data (spec (data2program pv) sv)  -- specialise, re-encode
--
-- and we DISCHARGE H1 for this real, unified machinery:
--
--     specU-correct :  runU (specU pv sv) d ≡ runU pv (sv · d)
--
-- (proved from RWhileP2D's round-trip + RWhileAVSpec.spec-correct).  Hence
-- fp1 holds UNCONDITIONALLY for the real AV specialiser in the value type
-- (`fp1U`).
--
-- fp2/fp3 then follow from RWhileFutamura2's modular logic, instantiated at
-- the real runU/specU, GIVEN a self-representation `specP` with
--
--     spec-impl :  runU specP (pv · sv) ≡ specU pv sv          -- H2
--
-- which `WithSelfApp` takes as a hypothesis.  This is the single, now fully
-- CONCRETE remaining obligation.
--
-- Why H2 is left open (and is not a defect of this development):
--   (1) The residual `Code` (RWhileAVSound) is a first-order EXPRESSION
--       language (cVar/cVal/cHd/cTl/cCons/cEq/cPairp) with no recursion, so it
--       cannot express the specialiser `spec` (which recurses over program
--       structure via `aeval`).  No `specP : Val` decodes to such a Code.
--   (2) More fundamentally, in a TOTAL meta-language (Agda `--safe`) `runU`
--       cannot be a total universal interpreter for a Turing-complete object
--       language; the self-applicable specialiser of the full R-WHILE is
--       Turing-complete, so its H2 is provable only in a partial / fuel-indexed
--       model or via a closure encoding (cf. RWhileFutamura2Inst, where a
--       built-in `papp` constructor keeps `run` total and makes H2 hold by
--       refl).  The byte-equal fp2/fp3 of the real `spec_av` on ri_min are the
--       empirical witness; `WithSelfApp` certifies that the hierarchy LOGIC is
--       sound for the real runU/specU once such a specP is supplied.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileAVSelfApp where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import RWhileAVSound using (Val; ⟨⟩; _·_; Code; ⟦_⟧c)
open import RWhileAVSpec  using (spec; spec-correct)
open import RWhileP2D     using (program2data; data2program; d2p∘p2d)
import RWhileFutamura2

------------------------------------------------------------------------
-- The unified universal type U = Val (programs = data = residuals).

runU : Val → Val → Val
runU pv d = ⟦ data2program pv ⟧c d

specU : Val → Val → Val
specU pv sv = program2data (spec (data2program pv) sv)

------------------------------------------------------------------------
-- H1 (spec-correct) for the REAL, unified machinery.
--   runU (specU pv sv) d
--     = ⟦ data2program (program2data (spec (data2program pv) sv)) ⟧c d
--     ≡ ⟦ spec (data2program pv) sv ⟧c d            -- round-trip d2p∘p2d
--     ≡ ⟦ data2program pv ⟧c (sv · d)               -- AVSpec.spec-correct
--     = runU pv (sv · d)

specU-correct : ∀ pv sv d → runU (specU pv sv) d ≡ runU pv (sv · d)
specU-correct pv sv d =
  trans (cong (λ z → ⟦ z ⟧c d) (d2p∘p2d (spec (data2program pv) sv)))
        (spec-correct (data2program pv) sv d)

------------------------------------------------------------------------
-- fp1 holds UNCONDITIONALLY for the real AV specialiser in the value type.

targetU : Val → Val → Val
targetU int src = specU int src

fp1U : ∀ int src d → runU (targetU int src) d ≡ runU int (src · d)
fp1U int src d = specU-correct int src d

------------------------------------------------------------------------
-- fp2/fp3: the modular hierarchy logic, instantiated at the REAL runU/specU.
-- H1 is discharged (specU-correct); H2 (spec-impl) is the supplied hypothesis.

module WithSelfApp
  (int specP : Val)
  (spec-impl : ∀ pv sv → runU specP (pv · sv) ≡ specU pv sv)
  where
  open RWhileFutamura2.Hierarchy
         Val _·_ runU specU int specP
         specU-correct      -- H1, proved above
         spec-impl          -- H2, hypothesis (the one concrete open obligation)
    public
