{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE STACK SUGAR `push` / `pop` (Rwhile.cf CPush/CPop, src/Desugar.ml).
--
--     push X S   ->   S <= cons X S        (X is left nil)
--     pop  X S   ->   cons X S <= S        (fails if S is not a cons)
--
-- These are the two sugars that CANNOT live in the timed layer: RWhileTime's
-- commands are skip / ^= / ; / if-fi / from-until, with no pattern replacement.
-- They belong here, where RWhileCRep models `<=` as a Read followed by a Write.
--
-- What is proved:
--
--   push-pop / pop-push  each is the other's inverse -- with NO inversion rule
--                        of its own.  R-WHILE inverts `q <= r` by swapping the
--                        two patterns, and that swap turns one into the other.
--   push-sem             S really becomes (X . S), and X really is left nil
--   pop-sem              popping SPLITS the stack: σ S ≡ cons (σ' X) (σ' S)
--   pop-needs-nil        pop only runs when X was nil -- the mirror of push
--                        leaving it nil, which is what makes them cancel
--
-- The two variables must differ; `S <= cons S S` would read S twice, which
-- src/Desugar.ml rejects and pattern linearity forbids here.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhilePushPop where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong₂)

open import RWhileValStore using (Val; nil; cons; Store; _≢ℕ_)
open import RWhileCRep
  using (Pat; pvar; pval; pcons; Read; Write;
         rd-var; rd-val; rd-cons; wr-var; wr-val; wr-cons;
         CRepRel; crepC; crep-reversible)
import RWhileRevFull
open RWhileRevFull.Core Store

------------------------------------------------------------------------
-- 1.  The two commands, exactly as Desugar.ml expands them.

pushC : ℕ → ℕ → Cmd
pushC x s = crepC (pvar s) (pcons (pvar x) (pvar s))

popC : ℕ → ℕ → Cmd
popC x s = crepC (pcons (pvar x) (pvar s)) (pvar s)

------------------------------------------------------------------------
-- 2.  They are each other's inverse, for free.
--
--     `crep-reversible` says the syntactic inversion of `q <= r` (swap the
--     patterns) realises the converse.  push and pop ARE that swap of each
--     other, so nothing further is needed -- which is exactly why Desugar.ml
--     gives them no inversion rule.

push-pop : ∀ {x s σ σ'} → pushC x s ⊢ σ ⇒ σ' → popC x s ⊢ σ' ⇒ σ
push-pop = crep-reversible

pop-push : ∀ {x s σ σ'} → popC x s ⊢ σ ⇒ σ' → pushC x s ⊢ σ' ⇒ σ
pop-push = crep-reversible

------------------------------------------------------------------------
-- 3.  What they actually do to the store.

-- push: S becomes (X . S), and X is left nil.
push-sem : ∀ {x s σ σ'} → x ≢ℕ s → s ≢ℕ x
         → pushC x s ⊢ σ ⇒ σ'
         → (σ' s ≡ cons (σ x) (σ s)) × (σ' x ≡ nil)
push-sem {x} {s} {σ} {σ'} xs sx
  (e-atom (_ , _ , rd-cons (rd-var ve₁ cl₁ fr₁) (rd-var ve₂ _ fr₂)
                 , wr-var _ ve₃ fr₃)) =
    trans (sym ve₃) (cong₂ cons ve₁ (trans ve₂ (sym (fr₁ s xs))))
  , trans (sym (fr₃ x sx)) (trans (sym (fr₂ x sx)) cl₁)

-- pop: the stack is SPLIT -- what S held is the cons of the two results.
pop-sem : ∀ {x s σ σ'} → x ≢ℕ s
        → popC x s ⊢ σ ⇒ σ'
        → σ s ≡ cons (σ' x) (σ' s)
pop-sem {x} {s} {σ} {σ'} xs
  (e-atom (_ , _ , rd-var ve _ _
                 , wr-cons (wr-var _ ve₂ _) (wr-var _ ve₁ fr₁))) =
    trans (sym ve) (cong₂ cons ve₁ (trans ve₂ (fr₁ s xs)))

-- pop only runs when X is nil beforehand: the mirror of push leaving it nil,
-- and what makes `push X S ; pop X S` cancel rather than merely typecheck.
pop-needs-nil : ∀ {x s σ σ'} → s ≢ℕ x
              → popC x s ⊢ σ ⇒ σ'
              → σ x ≡ nil
pop-needs-nil {x} {s} sx
  (e-atom (_ , _ , rd-var _ _ fr
                 , wr-cons (wr-var _ _ fr₂) (wr-var nl _ _))) =
    trans (fr x sx) (trans (fr₂ x sx) nl)
