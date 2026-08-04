{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Step (2), concrete: R-WHILE's reversible assignment `rupdate` is
-- deterministic, hence (by RWhileDet) the function-level inverse law holds
-- for concrete assignments: running `inv (assign x v)` on its output returns
-- to the start.
--
-- Determinism of the relational store update needs function extensionality
-- (two stores agreeing pointwise are equal).  We take `funext` as a module
-- hypothesis — this keeps the file --safe (it is an assumption, not a
-- postulate) and is discharged by Agda's --with-K-free funext or Cubical.
------------------------------------------------------------------------

module RWhileDetConcrete where

open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import RWhileValStore
import RWhileRevFull
import RWhileDet
open RWhileRevFull.Core Store
open RWhileDet.Det Store

module _ (funext : ∀ {A : Set} {B : Set} {f g : A → B}
                 → (∀ z → f z ≡ g z) → f ≡ g) where

  ----------------------------------------------------------------------
  -- `rupdate` is deterministic.

  -- the toggled slot value σ' x is determined by σ (both toggles agree there)
  -- 3 toggle cases on each side, so 9 clauses.  Case (3) (v ≡ nil, slot
  -- unchanged) was added on 2026-08-05 to match src/EvalRwhile.ml; see the
  -- note in RWhileValStore.agda.
  RAss-atx : ∀ {x v σ σ' σ''} → RAss x v σ σ' → RAss x v σ σ'' → σ' x ≡ σ'' x
  -- (1)/(1), (2)/(2), (3)/(3): both sides land on the same value
  RAss-atx (rass (inj₁ (_ , b1)) _) (rass (inj₁ (_ , b2)) _) = trans b1 (sym b2)
  RAss-atx (rass (inj₂ (inj₁ (_ , b1))) _) (rass (inj₂ (inj₁ (_ , b2))) _) =
    trans b1 (sym b2)
  RAss-atx (rass (inj₂ (inj₂ (_ , b1))) _) (rass (inj₂ (inj₂ (_ , b2))) _) =
    trans b1 (sym b2)
  -- (1)/(2) and (2)/(1): σx≡nil and σx≡v force v≡nil, so both slots are nil
  RAss-atx (rass (inj₁ (a1 , b1)) _) (rass (inj₂ (inj₁ (a2 , b2))) _) =
    trans b1 (trans (trans (sym a2) a1) (sym b2))   -- σ'x≡v , v≡nil , nil≡σ''x
  RAss-atx (rass (inj₂ (inj₁ (a1 , b1))) _) (rass (inj₁ (a2 , b2)) _) =
    trans b1 (trans (trans (sym a2) a1) (sym b2))   -- σ'x≡nil , nil≡v , v≡σ''x
  -- (1)/(3) and (3)/(1): v≡nil and σx≡nil, so the slot is nil either way
  RAss-atx (rass (inj₁ (a1 , b1)) _) (rass (inj₂ (inj₂ (a2 , b2))) _) =
    trans b1 (trans a2 (trans (sym a1) (sym b2)))
  RAss-atx (rass (inj₂ (inj₂ (a1 , b1))) _) (rass (inj₁ (a2 , b2)) _) =
    trans b1 (trans a2 (trans (sym a1) (sym b2)))
  -- (2)/(3) and (3)/(2): v≡nil and σx≡v, so the slot is nil either way
  RAss-atx (rass (inj₂ (inj₁ (a1 , b1))) _) (rass (inj₂ (inj₂ (a2 , b2))) _) =
    trans b1 (trans (sym a2) (trans (sym a1) (sym b2)))
  RAss-atx (rass (inj₂ (inj₂ (a1 , b1))) _) (rass (inj₂ (inj₁ (a2 , b2))) _) =
    trans b1 (trans a2 (trans a1 (sym b2)))

  RAss-det : ∀ {x v σ σ' σ''} → RAss x v σ σ' → RAss x v σ σ'' → σ' ≡ σ''
  RAss-det {x} r1@(rass _ fr1) r2@(rass _ fr2) = funext pw
    where
      pw : ∀ y → _
      pw y with x ≟ y
      ... | yes refl = RAss-atx r1 r2
      ... | no  x≠y  = trans (sym (fr1 y x≠y)) (fr2 y x≠y)

  ----------------------------------------------------------------------
  -- Hence the concrete assignment is deterministic, and its inverse cancels.

  -- Det⟨ assign x v ⟩  (the atom RAss x v is deterministic)
  assign-det : ∀ x v → Det⟨ assign x v ⟩
  assign-det x v = RAss-det

  -- Det⟨ inv (assign x v) ⟩.  inv (assign x v) = atom (conv (RAss x v)); since
  -- RAss is symmetric (RAss-sym), the converse is deterministic too.
  assign-inv-det : ∀ x v → Det⟨ inv (assign x v) ⟩
  assign-inv-det x v c1 c2 = RAss-det (RAss-sym c1) (RAss-sym c2)

  -- FUNCTION-LEVEL INVERSE: running inv(assign x v) on the output of
  -- assign x v returns to the start.
  assign-inv-cancels : ∀ {x v s t t'}
                     → assign x v ⊢ s ⇒ t → inv (assign x v) ⊢ t ⇒ t' → t' ≡ s
  assign-inv-cancels {x} {v} = inv-cancels (assign-inv-det x v)
