{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE ALGEBRA OF THE FUTAMURA TOWER: composition laws and the collapse at
-- level 3 ("there is no fourth projection", Glück, PEPM 2009).
--
-- RWhileFutamura2.Hierarchy derives fp1/fp2/fp3 from H1 (`spec-correct`) and
-- H2 (`spec-impl`).  This module is a PURELY ADDITIVE extension of it: it
-- re-opens the same module with the same two hypotheses and asks what else
-- the two equations give.  Nothing in RWhileFutamura2 is changed.
--
-- WHAT IS PROVED
--
--   spec-compose  run (spec (spec p s) t) d ≡ run p ⟨ s , ⟨ t , d ⟩ ⟩
--                   -- specialising twice = specialising to a nested static
--                      input.  The one law here that is about `spec` rather
--                      than about the tower.
--   spec-stage    its n-ary form, over a list of static inputs (induction).
--   cogen-curry   run (run cogen p) s ≡ spec p s
--                   -- cogen IS the specialiser, curried.  fp2 and the
--                      two-stage composition are instances (p := int).
--   fp4           run cogen specP ≡ cogen
--                   -- THE DEGENERACY.  One line: it is `fp3 specP`, because
--                      cogen is *defined* as spec specP specP.  Stated here
--                      because the n-ary collapse below needs it, not
--                      because it is deep.  It is not deep.
--   tower-collapse  ∀ n → tower n ≡ cogen     (tower (suc n) = run (tower n) specP)
--   tower-curry     ∀ n p s → run (run (tower n) p) s ≡ spec p s
--   tower-run       ∀ n src d → run (run (run (tower n) int) src) d ≡ run int ⟨src,d⟩
--                   -- the WHOLE tower, at every height, computes what fp1's
--                      residual computes.  This is the honest formal content
--                      of "there is no fourth projection": levels ≥ 3 are all
--                      the same program, not merely programs with the same
--                      behaviour.
--
-- WHICH FIXED POINT?  `fp4` says cogen is a fixed point of
--      Φ X = run X specP        ("apply to the specialiser's text").
-- It does NOT say cogen is a fixed point of `run cogen`, i.e. that
-- `run cogen cogen ≡ cogen`; that reading is FALSE, and refuted in a model in
-- RWhileFutamuraAlgInst (`cogen-not-self-applicable`).  Since RESEARCH_ROADMAP
-- ④ says only "cogen の不動点性", the operator has to be named for the phrase
-- to be true.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileFutamuraAlg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

import RWhileFutamura2

module Algebra
  (U      : Set)                     -- programs = data = residuals
  (⟨_,_⟩  : U → U → U)               -- pairing of (static . dynamic)
  (run    : U → U → U)
  (spec   : U → U → U)
  (int    : U)
  (specP  : U)
  (spec-correct : ∀ p s d → run (spec p s) d ≡ run p ⟨ s , d ⟩)   -- H1
  (spec-impl    : ∀ p s   → run specP ⟨ p , s ⟩ ≡ spec p s)        -- H2
  where

  -- everything RWhileFutamura2 proves, unchanged
  open RWhileFutamura2.Hierarchy
         U ⟨_,_⟩ run spec int specP spec-correct spec-impl public

  ----------------------------------------------------------------------
  -- 1.  COMPOSITION OF SPECIALISATIONS (nothing to do with the tower).
  --
  -- Staging the static input in two goes is the same as handing it over
  -- nested.  Two uses of H1 and no use of H2: this holds for specialisers
  -- that are not self-applicable at all.

  spec-compose : ∀ p s t d → run (spec (spec p s) t) d ≡ run p ⟨ s , ⟨ t , d ⟩ ⟩
  spec-compose p s t d =
    trans (spec-correct (spec p s) t d) (spec-correct p s ⟨ t , d ⟩)

  -- the n-ary form.  `nest` builds ⟨s₁ , ⟨s₂ , … ⟨sₙ , d⟩ …⟩⟩.
  stage : U → List U → U
  stage p []       = p
  stage p (s ∷ ss) = stage (spec p s) ss

  nest : List U → U → U
  nest []       d = d
  nest (s ∷ ss) d = ⟨ s , nest ss d ⟩

  spec-stage : ∀ ss p d → run (stage p ss) d ≡ run p (nest ss d)
  spec-stage []       p d = refl
  spec-stage (s ∷ ss) p d =
    trans (spec-stage ss (spec p s) d) (spec-correct p s (nest ss d))

  ----------------------------------------------------------------------
  -- 2.  COGEN IS THE SPECIALISER, CURRIED.
  --
  -- One application of cogen picks the subject program; the second supplies
  -- the static input.  Everything else in this file is a corollary.

  cogen-curry : ∀ p s → run (run cogen p) s ≡ spec p s
  cogen-curry p s =
    trans (cong (λ c → run c s) (fp3 p))
          (trans (spec-correct specP p s) (spec-impl p s))

  -- two stages: cogen → compiler → target.  (p := int)
  cogen-target : ∀ src → run (run cogen int) src ≡ target src
  cogen-target src = cogen-curry int src

  -- and the residual so obtained is fp1's residual, end to end.
  cogen-run : ∀ src d → run (run (run cogen int) src) d ≡ run int ⟨ src , d ⟩
  cogen-run src d = trans (cong (λ t → run t d) (cogen-target src)) (fp1 src d)

  ----------------------------------------------------------------------
  -- 3.  THE DEGENERACY (the "fourth projection").
  --
  -- The candidate level-4 artefact is `run cogen specP` — generate a
  -- generator.  It is cogen itself.  ONE LINE: `fp3 specP` already says
  -- `run cogen specP ≡ spec specP specP`, and cogen is by definition that.
  -- The content is not in the proof, it is in the statement.

  fp4 : run cogen specP ≡ cogen
  fp4 = fp3 specP

  -- the operator of which cogen is a fixed point (see the header: naming it
  -- is the whole point).
  Φ : U → U
  Φ X = run X specP

  cogen-fixpoint : Φ cogen ≡ cogen
  cogen-fixpoint = fp4

  ----------------------------------------------------------------------
  -- 4.  THE TOWER AT ARBITRARY HEIGHT.
  --
  -- tower n = Φⁿ cogen: keep feeding the specialiser to the generator.

  tower : ℕ → U
  tower zero    = cogen
  tower (suc n) = Φ (tower n)

  tower-collapse : ∀ n → tower n ≡ cogen
  tower-collapse zero    = refl
  tower-collapse (suc n) = trans (cong Φ (tower-collapse n)) fp4

  -- hence every level of the tower is the specialiser curried …
  tower-curry : ∀ n p s → run (run (tower n) p) s ≡ spec p s
  tower-curry n p s =
    trans (cong (λ c → run (run c p) s) (tower-collapse n)) (cogen-curry p s)

  -- … and the level-n artefact, applied to int and then to a source, gives a
  -- program that computes the interpreter.  No height buys anything.
  tower-run : ∀ n src d →
    run (run (run (tower n) int) src) d ≡ run int ⟨ src , d ⟩
  tower-run n src d =
    trans (cong (λ t → run t d) (tower-curry n int src)) (fp1 src d)

  -- three explicit stages, for the record (n := 1):
  cogen-target₃ : ∀ src → run (run (run cogen specP) int) src ≡ target src
  cogen-target₃ = tower-curry 1 int
