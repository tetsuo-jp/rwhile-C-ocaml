{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Generalisations of the reversible projections (paper §generalization,
-- §irrev_source, §garbage), in Agda.
--
-- (a) GENERAL proj : the three reversible projections hold for an arbitrary
--     projection `proj` and an arbitrary source semantics `srcSem` (no
--     injectivity assumed) — `proj = snd` (RWhileRevProjPaper) is the special
--     case.  This already covers NON-REVERSIBLE source languages.
-- (b) NON-REVERSIBLE source : keeping the whole input as garbage gives an
--     injective (reversible) residual for ANY source — `input-preserving-inj`
--     — so the input-preserving reversible interpreter rint⁺ exists and the
--     reversible projection extends to non-reversible S.
-- (c) GARBAGE DICHOTOMY :
--       garbage-necessary : a reversible residual simulating a non-injective
--         source forces the cleanup `proj` to discard information (garbage).
--       input-preserving-inj : garbage (keeping the input) always suffices.
------------------------------------------------------------------------

module RWhileRevProjGen where

open import Data.Product using (_×_; _,_; proj₁)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- injectivity
Inj : {A B : Set} → (A → B) → Set
Inj f = ∀ {x y} → f x ≡ f y → x ≡ y

------------------------------------------------------------------------
-- Motivation (paper Thm proj1_fail): the ORDINARY first Futamura projection
-- with a reversible-implementation interpreter exists only for a TRIVIAL
-- source.  An interpreter that realises the source directly and is reversible
-- (injective) forces the source semantics to be injective.
--   srcMap ⟨p,d⟩ = ⟦p⟧_S d (the uncurried source semantics);
--   i = ⟦lint'⟧ (reversible interpreter), realising srcMap directly.
-- Contrapositive: a non-trivial (non-injective) source has NO such reversible
-- ordinary interpreter — hence the reversible *projection* (with rint) is
-- needed instead.
proj1-needs-trivial :
  ∀ {U : Set} {srcMap i : U → U}
  → Inj i → (∀ x → srcMap x ≡ i x) → Inj srcMap
proj1-needs-trivial inj-i eq sx≡sy =
  inj-i (trans (sym (eq _)) (trans sx≡sy (eq _)))

------------------------------------------------------------------------
-- (a) Generalised reversible projections: arbitrary `proj`, arbitrary srcSem.

module GeneralRevProjection
  (U      : Set)
  (run    : U → U → U)
  (⟨_,_⟩  : U → U → U)
  (proj   : U → U)              -- a projection (removes garbage); snd is one
  (srcSem : U → U → U)          -- arbitrary — NOT assumed injective
  (rint rspec : U)
  (rint-proj : ∀ p d → proj (run rint ⟨ p , d ⟩) ≡ srcSem p d)  -- general rint
  (def-spec  : ∀ p s d → run (run rspec ⟨ p , s ⟩) d ≡ run p ⟨ s , d ⟩)
  where

  tgt : U → U
  tgt src = run rspec ⟨ rint , src ⟩
  comp : U
  comp = run rspec ⟨ rspec , rint ⟩
  cogen : U
  cogen = run rspec ⟨ rspec , rspec ⟩

  rev-proj1 : ∀ src d → proj (run (tgt src) d) ≡ srcSem src d
  rev-proj1 src d = trans (cong proj (def-spec rint src d)) (rint-proj src d)

  rev-proj2 : ∀ src d → proj (run (run comp src) d) ≡ srcSem src d
  rev-proj2 src d =
    trans (cong (λ x → proj (run x d)) (def-spec rspec rint src)) (rev-proj1 src d)

  rev-proj3 : ∀ src d → proj (run (run (run cogen rint) src) d) ≡ srcSem src d
  rev-proj3 src d =
    trans (cong (λ x → proj (run (run x src) d)) (def-spec rspec rspec rint)) (rev-proj2 src d)

------------------------------------------------------------------------
-- (b),(c) Garbage dichotomy (for any carrier).

module Garbage (W : Set) where

  -- GARBAGE NECESSITY: if a reversible (injective) residual G simulates a
  -- non-injective source  S = proj ∘ G,  then the cleanup proj is NOT
  -- injective — i.e. it must discard information (= the garbage).
  garbage-necessary :
    ∀ {G proj S : W → W}
    → Inj G → (∀ x → S x ≡ proj (G x)) → ¬ Inj S → ¬ Inj proj
  garbage-necessary {G} {proj} {S} injG S≡pg ¬injS injproj =
    ¬injS λ {x} {y} sx≡sy →
      injG (injproj (trans (sym (S≡pg x)) (trans sx≡sy (S≡pg y))))

  -- GARBAGE SUFFICES (existence of a reversible simulation for ANY source):
  -- keeping the whole input as garbage, x ↦ (x , S x), is always injective.
  -- This is exactly the input-preserving reversible interpreter rint⁺, which
  -- therefore exists even when S is non-injective (non-reversible source).
  input-preserving-inj : ∀ {S : W → W} → Inj (λ x → (x , S x))
  input-preserving-inj eq = cong proj₁ eq

------------------------------------------------------------------------
-- Witness that garbage-necessary is non-vacuous: a constant (non-injective)
-- source S, an injective residual (suc), forces a non-injective cleanup.

module _ where
  open Garbage ℕ

  suc-inj : Inj suc
  suc-inj refl = refl

  ¬inj-const : ¬ Inj (λ (_ : ℕ) → zero)
  ¬inj-const inj with inj {zero} {suc zero} refl
  ... | ()

  -- S = const 0 (non-injective), residual G = suc (injective), cleanup
  -- proj = const 0 with S x = proj (G x); garbage-necessary ⇒ proj non-inj.
  garbage-witness : ¬ Inj (λ (_ : ℕ) → zero)
  garbage-witness = garbage-necessary {G = suc} {proj = λ _ → zero} {S = λ _ → zero}
                      suc-inj (λ _ → refl) ¬inj-const
