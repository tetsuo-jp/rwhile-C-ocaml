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

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileCoreExp using (CExp; xVar; xVal; xCons; xHd; xTl; xEq; xPair; evalC)
open import RWhileValStore using (Store)

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
