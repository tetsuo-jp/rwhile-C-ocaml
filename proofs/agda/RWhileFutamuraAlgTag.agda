{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE SAME ALGEBRA FOR THE ARTEFACT'S OWN CONTRACT (tagged pairing).
--
-- RWhileFutamuraAlg works over RWhileFutamura2's untagged hierarchy.  The
-- real fp2/fp3 tests run `spec_av` on `(p . ('S . s))` and a residual on a
-- plain `(src . d)`, which is why RWhileFutamura3 re-derives the hierarchy
-- from the ONE contract
--
--     contract : run (run specP ⟨ p , tagS s ⟩) d ≡ run p ⟨ s , d ⟩
--
-- This module adds the composition laws and the collapse to THAT layer, so
-- the algebra applies to the artefact's equations verbatim — the level-n
-- statement `tower-run` is the ∀-closure of the OCaml check
-- `[[comp3]('S.ri_min)]('S.swap) == B` with arbitrarily many extra
-- self-applications in front.
--
-- Additive: RWhileFutamura3 is unchanged and re-opened.
--
--   cogen-curry  run (run (comp3 int) (tagS p)) (tagS s) ≡ spec p s
--   fp4          run (comp3 int) (tagS specP) ≡ comp3 int      (one line)
--   tower-run    ∀ n src d →
--                run (run (run (tower int n) (tagS int)) (tagS src)) d
--                  ≡ run int ⟨ src , d ⟩
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileFutamuraAlgTag where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

import RWhileFutamura3

module TagAlgebra
  (U      : Set)
  (⟨_,_⟩  : U → U → U)
  (tagS   : U → U)
  (run    : U → U → U)
  (specP  : U)
  (contract : ∀ p s d → run (run specP ⟨ p , tagS s ⟩) d ≡ run p ⟨ s , d ⟩)
  where

  open RWhileFutamura3.Contract U ⟨_,_⟩ tagS run specP contract public

  module _ (int : U) where

    -- cogen is the specialiser, curried — with the binding-time tag on both
    -- arguments, exactly as the tests feed it.
    cogen-curry : ∀ p s → run (run (comp3 int) (tagS p)) (tagS s) ≡ spec p s
    cogen-curry p s =
      trans (cong (λ c → run c (tagS s)) (fp3 int p)) (contract specP p (tagS s))

    -- THE DEGENERACY: feeding the specialiser to the cogen gives the cogen.
    -- One line — `fp3 int specP` already says it, since comp3 is spec specP specP.
    fp4 : run (comp3 int) (tagS specP) ≡ comp3 int
    fp4 = fp3 int specP

    tower : ℕ → U
    tower zero    = comp3 int
    tower (suc n) = run (tower n) (tagS specP)

    tower-collapse : ∀ n → tower n ≡ comp3 int
    tower-collapse zero    = refl
    tower-collapse (suc n) =
      trans (cong (λ c → run c (tagS specP)) (tower-collapse n)) fp4

    tower-curry : ∀ n p s → run (run (tower n) (tagS p)) (tagS s) ≡ spec p s
    tower-curry n p s =
      trans (cong (λ c → run (run c (tagS p)) (tagS s)) (tower-collapse n))
            (cogen-curry p s)

    -- the whole tower, at any height, still compiles sources correctly.
    tower-run : ∀ n src d →
      run (run (run (tower n) (tagS int)) (tagS src)) d ≡ run int ⟨ src , d ⟩
    tower-run n src d =
      trans (cong (λ t → run t d) (tower-curry n int src)) (fp1 int src d)

------------------------------------------------------------------------
-- Non-vacuity: the tagged closure model of RWhileFutamura3 discharges the
-- contract by refl, so the laws hold for concrete, distinct programs.
------------------------------------------------------------------------

module Closure where

  open RWhileFutamura3.Closure using (U; pair; tagS; papp; mkspec; idP; run)

  open TagAlgebra U pair tagS run mkspec (λ p s d → refl) public

  _ : comp3 idP ≡ papp mkspec mkspec
  _ = refl

  -- the fourth projection, by computation
  _ : run (comp3 idP) (tagS mkspec) ≡ comp3 idP
  _ = refl

  _ : run (comp3 idP) (tagS mkspec) ≡ comp3 idP
  _ = fp4 idP

  -- every height of the tower is the same program …
  _ : tower idP 4 ≡ comp3 idP
  _ = refl

  -- … and still compiles: three extra self-applications change nothing.
  _ : ∀ src d → run (run (run (tower idP 3) (tagS idP)) (tagS src)) d
                ≡ run idP (pair src d)
  _ = tower-run idP 3
