{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A QUANTITATIVE lower bound on the garbage of a reversible simulation
-- (#4 — sharpening the qualitative dichotomy of RWhileRevProjGen.Garbage and
-- the paper's §garbage / Landauer–Bennett discussion).
--
-- A reversible residual that simulates a source S keeps a pair
--   resid x = (result, garbage) = (S x , g x).
-- Reversibility = `resid` is injective.  RWhileRevProjGen.garbage-necessary
-- already shows that for a NON-injective S the cleanup that drops the garbage
-- cannot be injective (information must be discarded).  Here we quantify HOW
-- MUCH: on a FIBER of S (the inputs sharing one result value) the result
-- component is constant, so the GARBAGE alone must distinguish them.  Hence the
-- garbage is injective on every fiber, i.e. it carries at least as many distinct
-- values as the fiber has elements (≥ log |fiber| bits) — the minimal
-- information any reversible simulation of S must retain.
--
-- Stated without UIP/K (no equality of the fiber's proof component is needed),
-- so it holds under `--safe`.
------------------------------------------------------------------------

module RWhileGarbageBound where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

-- injectivity
Inj : {A B : Set} → (A → B) → Set
Inj f = ∀ {x y} → f x ≡ f y → x ≡ y

module Bound (In Out Gar : Set) (S : In → Out) (g : In → Gar) where

  -- the reversible residual keeps (result , garbage)
  resid : In → Out × Gar
  resid x = (S x , g x)

  ----------------------------------------------------------------------
  -- CORE LOWER BOUND: if the residual is reversible (injective) then two inputs
  -- with the SAME result and the SAME garbage are equal — the garbage must
  -- distinguish all inputs that share a result.
  garbage-distinguishes-fiber :
    Inj resid → ∀ {x y} → S x ≡ S y → g x ≡ g y → x ≡ y
  garbage-distinguishes-fiber inj sxy gxy = inj (cong₂ _,_ sxy gxy)

  ----------------------------------------------------------------------
  -- CARDINALITY FORM: the garbage restricted to the fiber over `v`
  -- (inputs with S x ≡ v) is injective — so |fiber v| ≤ |Gar|.  (No equality of
  -- the membership proofs is used, hence no UIP.)
  garbage-injective-on-fiber :
    Inj resid → ∀ {v} {x y} → S x ≡ v → S y ≡ v → g x ≡ g y → x ≡ y
  garbage-injective-on-fiber inj px py gxy =
    garbage-distinguishes-fiber inj (trans px (sym py)) gxy

------------------------------------------------------------------------
-- Non-vacuous witness: the maximally non-injective source — a CONSTANT
-- function S = const tt (one fiber = the whole input set).  Keeping the input
-- as garbage (g = id) is a reversible simulation (resid injective); the bound
-- then forces the garbage to be injective, i.e. the WHOLE input is retained.
-- This is the necessity counterpart of RWhileRevProjGen.input-preserving-inj
-- (which showed input-as-garbage SUFFICES): for the constant source it is also
-- NECESSARY to keep all of it.

module Witness where
  open Bound ℕ ⊤ ℕ (λ _ → tt) (λ x → x)

  resid-inj : Inj resid
  resid-inj eq = cong proj₂ eq          -- resid x = (tt , x); proj₂ recovers x

  -- the garbage map (= id here) must be injective: all of the input is kept.
  garbage-keeps-whole-input : Inj (λ (x : ℕ) → x)
  garbage-keeps-whole-input gxy =
    garbage-injective-on-fiber resid-inj refl refl gxy

------------------------------------------------------------------------
-- ACHIEVABILITY (the matching upper bound).  The lower bound says any reversible
-- simulation of S must keep garbage that distinguishes each fiber.  This is
-- ACHIEVABLE for EVERY S: keeping the whole input as garbage (g = id) makes the
-- residual injective — input-preservation is a universal reversible simulation
-- (the general form of RWhileRevProjGen.input-preserving-inj).  Together with
-- the lower bound this pins the picture: garbage IS necessary (lower bound) and
-- input-as-garbage always SUFFICES (upper bound); the two meet exactly at the
-- maximally non-injective (constant) source, where the whole input is forced
-- (`Witness`), so the input-preserving bound is tight there.

module Achievable (In Out : Set) (S : In → Out) where
  open Bound In Out In S (λ x → x)        -- garbage = the input itself

  -- input-preservation is a reversible simulation of ANY S.
  input-preserving-suffices : Inj resid
  input-preserving-suffices eq = cong proj₂ eq

------------------------------------------------------------------------
-- CLEAN simulation for a REVERSIBLE source (the dichotomy's reversible side,
-- quantified).  If S is injective then every fiber is a singleton, so the lower
-- bound demands no information: garbage = ⊤ (nothing) already gives a reversible
-- simulation.  This is Bennett's clean simulation — no garbage to uncompute.
-- Together with `Achievable` (universal upper bound) and the fiber lower bound,
-- it makes the essential/surplus garbage dichotomy quantitative: surplus = 0
-- iff S is injective.

module Clean (In Out : Set) (S : In → Out) (S-inj : Inj S) where
  open Bound In Out ⊤ S (λ _ → tt)        -- garbage = ⊤ (no information)

  -- with no garbage, the residual is still reversible (clean simulation).
  clean-resid-inj : Inj resid
  clean-resid-inj eq = S-inj (cong proj₁ eq)
