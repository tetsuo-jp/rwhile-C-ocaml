{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Towards `expMacProgram` correctness (R-WHILE-M → R-WHILE).
--
-- R-WHILE macros are NON-recursive and expand by INLINING: a call `M(a₁..aₙ)`
-- is replaced by M's body with the formal parameters RENAMED to the actual
-- variable arguments (src/MacroRwhile.ml + Subst.ml).  The heart of why this
-- preserves meaning is the SUBSTITUTION LEMMA: renaming the variables in a
-- term is the same as renaming the store.
--
--   subst-exp : ∀ ρ σ e → evalC σ (ren ρ e) ≡ evalC (σ ∘ ρ) e
--
-- For EXPRESSIONS this holds for ANY renaming ρ (expressions only READ the
-- store, so a clashing rename cannot capture/overwrite anything).  Hence
-- inlining a macro's expressions is unconditionally sound.  (For COMMANDS that
-- WRITE the store, the lemma needs ρ injective on the live variables — exactly
-- R-WHILE's hygiene condition: a macro local must not collide with a caller
-- variable.  The default expansion is non-hygienic and `-hygienic-macros`
-- enforces injectivity; this is the documented caveat, and the command-level
-- substitution lemma under injectivity is the remaining step.)
------------------------------------------------------------------------

module RWhileMacroSubst where

open import Data.Nat using (ℕ; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)

open import RWhileCoreExp using (CExp; xVar; xVal; xCons; xHd; xTl; xEq; xPair; evalC)
open import RWhileValStore using (Val; nil; cons; Store)

-- variable renaming on core expressions (formals → actuals at a macro call)
ren : (ℕ → ℕ) → CExp → CExp
ren ρ (xVar x)    = xVar (ρ x)
ren ρ (xVal v)    = xVal v
ren ρ (xCons a b) = xCons (ren ρ a) (ren ρ b)
ren ρ (xHd e)     = xHd (ren ρ e)
ren ρ (xTl e)     = xTl (ren ρ e)
ren ρ (xEq a b)   = xEq (ren ρ a) (ren ρ b)
ren ρ (xPair e)   = xPair (ren ρ e)

------------------------------------------------------------------------
-- SUBSTITUTION LEMMA (expressions): renaming the term = renaming the store.
-- Holds for ANY ρ (expressions are read-only).

subst-exp : ∀ (ρ : ℕ → ℕ) (σ : Store) e → evalC σ (ren ρ e) ≡ evalC (λ x → σ (ρ x)) e
subst-exp ρ σ (xVar x)    = refl
subst-exp ρ σ (xVal v)    = refl
subst-exp ρ σ (xCons a b) rewrite subst-exp ρ σ a | subst-exp ρ σ b = refl
subst-exp ρ σ (xHd e)     rewrite subst-exp ρ σ e = refl
subst-exp ρ σ (xTl e)     rewrite subst-exp ρ σ e = refl
subst-exp ρ σ (xEq a b)   rewrite subst-exp ρ σ a | subst-exp ρ σ b = refl
subst-exp ρ σ (xPair e)   rewrite subst-exp ρ σ e = refl

------------------------------------------------------------------------
-- WRITE SIDE: the hygiene condition, made precise.
--
-- A macro body also WRITES the store (pattern replacement assigns variables).
-- A single-variable store write is `upd x v σ` (matching RWhileCoreExp.setNil's
-- shape, but storing `v`).  For the renamed body to compute the same thing, the
-- write through a renamed variable must commute with renaming the store:
--
--   (λ y → upd (ρ x) v σ (ρ y)) ≡ upd x v (σ ∘ ρ)
--
-- This holds EXACTLY when ρ is INJECTIVE on the variables — which is precisely
-- R-WHILE's hygiene condition (a macro local must not be renamed onto a caller
-- variable, or the write would clobber it = variable capture).  The default
-- expansion is non-hygienic; `-hygienic-macros` makes ρ injective.

Inj : (ℕ → ℕ) → Set
Inj ρ = ∀ {a b} → ρ a ≡ ρ b → a ≡ b

upd : ℕ → Val → Store → Store
upd x v σ y with x ≟ y
... | yes _ = v
... | no  _ = σ y

-- pointwise commutation, under injectivity of ρ.
subst-upd-pt : ∀ (ρ : ℕ → ℕ) → Inj ρ → ∀ x v σ y →
  upd (ρ x) v σ (ρ y) ≡ upd x v (λ z → σ (ρ z)) y
subst-upd-pt ρ inj x v σ y with x ≟ y | ρ x ≟ ρ y
... | yes _  | yes _  = refl
... | yes p  | no  ¬q = ⊥-elim (¬q (cong ρ p))
... | no  ¬p | yes q  = ⊥-elim (¬p (inj q))
... | no  _  | no  _  = refl

-- full commutation (needs funext, taken as a hypothesis as elsewhere in this
-- development — e.g. RWhileDetConcrete).
module _ (funext : ∀ {A : Set} {B : Set} {f g : A → B}
                 → (∀ z → f z ≡ g z) → f ≡ g) where

  subst-upd : ∀ (ρ : ℕ → ℕ) → Inj ρ → ∀ x v σ →
    (λ y → upd (ρ x) v σ (ρ y)) ≡ upd x v (λ z → σ (ρ z))
  subst-upd ρ inj x v σ = funext (subst-upd-pt ρ inj x v σ)

------------------------------------------------------------------------
-- ...and INJECTIVITY IS NECESSARY: a collapsing rename (ρ = const 0, merging
-- variables 0 and 1 — the macro-capture scenario) breaks the commutation.
-- Writing `cons nil nil` to (renamed) variable 0 over the nil store: through
-- the renamed store it leaks to variable 1, but in the original it must not.

collapse : ℕ → ℕ
collapse _ = 0

capture : ¬ (upd (collapse 0) (cons nil nil) (λ _ → nil) (collapse 1)
             ≡ upd 0 (cons nil nil) (λ z → (λ _ → nil) (collapse z)) 1)
capture ()
