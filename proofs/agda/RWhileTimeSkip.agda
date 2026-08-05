{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- WHAT THE `skip`s COST.
--
-- R-WHILE's grammar has EMPTY branches (`BThenNone`, `BElseNone`,
-- `BDoNone`, `BLoopNone`), so a branch that is `skip` prints as nothing and
-- an implementation executing that text charges nothing for it.  This model
-- charges 1.  The measured gap between the two (§4.7 vs §4.75 of
-- LINEAR_TIME_SI.md) is therefore expected -- and this module pins down
-- exactly how much of it the model's `skip`s account for:
--
--     k ≡ cost₀ d + skips d
--
-- where `skips d` counts the `skip`s the derivation actually executed and
-- `cost₀ d` is the same run charged 0 for them.  Note this is a statement
-- INSIDE the model; the implementation's own counting is not formalised
-- (the OCaml is not verified), so the comparison with `./ri -steps` remains
-- a comparison of measurements.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileTimeSkip where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

open import RWhileTime

------------------------------------------------------------------------
-- The two accountings.

skips  : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k → ℕ
skipsR : ∀ {e D L f σ τ n} → Rest e D L f σ τ n → ℕ

skips e-skip            = 1
skips (e-ass _ _)       = 0
skips (e-seq d₁ d₂)     = skips d₁ + skips d₂
skips (e-then _ dc _)   = skips dc
skips (e-else _ dd _)   = skips dd
skips (e-loop _ dD r)   = skips dD + skipsR r

skipsR (r-exit _)              = 0
skipsR (r-iter _ dL _ dD r)    = skips dL + skips dD + skipsR r

cost₀  : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k → ℕ
cost₀R : ∀ {e D L f σ τ n} → Rest e D L f σ τ n → ℕ

cost₀ e-skip            = 0
cost₀ (e-ass _ _)       = 1
cost₀ (e-seq d₁ d₂)     = suc (cost₀ d₁ + cost₀ d₂)
cost₀ (e-then _ dc _)   = suc (cost₀ dc)
cost₀ (e-else _ dd _)   = suc (cost₀ dd)
cost₀ (e-loop _ dD r)   = suc (cost₀ dD + cost₀R r)

cost₀R (r-exit _)           = 0
cost₀R (r-iter _ dL _ dD r) = cost₀ dL + cost₀ dD + cost₀R r

------------------------------------------------------------------------
-- The split.

private
  e1 : ∀ a b c d → suc ((a + c) + (b + d)) ≡ suc (a + b) + (c + d)
  e1 = solve 4 (λ a b c d → con 1 :+ ((a :+ c) :+ (b :+ d)) :=
                            (con 1 :+ (a :+ b)) :+ (c :+ d)) refl
  e2 : ∀ a b c d e f → ((a + d) + (b + e)) + (c + f) ≡ ((a + b) + c) + ((d + e) + f)
  e2 = solve 6 (λ a b c d e f → ((a :+ d) :+ (b :+ e)) :+ (c :+ f) :=
                                ((a :+ b) :+ c) :+ ((d :+ e) :+ f)) refl

cost-split  : ∀ {c σ τ k} (d : c ⊢ σ ⇒ τ ∣ k) → k ≡ cost₀ d + skips d
cost-splitR : ∀ {e D L f σ τ n} (r : Rest e D L f σ τ n) → n ≡ cost₀R r + skipsR r

cost-split e-skip      = refl
cost-split (e-ass _ _) = refl

cost-split (e-seq {k = k} {l = l} d₁ d₂) =
  trans (cong suc (cong₂+ (cost-split d₁) (cost-split d₂)))
        (e1 (cost₀ d₁) (cost₀ d₂) (skips d₁) (skips d₂))
  where
    cong₂+ : ∀ {a b c d} → a ≡ b → c ≡ d → a + c ≡ b + d
    cong₂+ refl refl = refl

cost-split (e-then _ dc _) = cong suc (cost-split dc)
cost-split (e-else _ dd _) = cong suc (cost-split dd)

cost-split (e-loop _ dD r) =
  trans (cong suc (cong₂+ (cost-split dD) (cost-splitR r)))
        (e1 (cost₀ dD) (cost₀R r) (skips dD) (skipsR r))
  where
    cong₂+ : ∀ {a b c d} → a ≡ b → c ≡ d → a + c ≡ b + d
    cong₂+ refl refl = refl

cost-splitR (r-exit _) = refl
cost-splitR (r-iter _ dL _ dD r) =
  trans (cong₂+ (cong₂+ (cost-split dL) (cost-split dD)) (cost-splitR r))
        (e2 (cost₀ dL) (cost₀ dD) (cost₀R r) (skips dL) (skips dD) (skipsR r))
  where
    cong₂+ : ∀ {a b c d} → a ≡ b → c ≡ d → a + c ≡ b + d
    cong₂+ refl refl = refl
