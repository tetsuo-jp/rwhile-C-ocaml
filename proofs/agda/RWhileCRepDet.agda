{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Integrate pattern replacement `CRep` into the determinism layer.
--
-- Pattern READ and WRITE are deterministic (Read-det / Write-det), hence the
-- pattern-replacement relation is deterministic (crep-det) and so is its
-- inverse (crep-inv-det).  With RWhileDet.inv-cancels this gives the
-- function-level inverse law for CRep: running `inv (CRep q r)` on its output
-- returns to the start (crep-inv-cancels).
--
-- Determinism of the relational store needs function extensionality, taken as
-- a module hypothesis (keeps the file --safe).
------------------------------------------------------------------------

module RWhileCRepDet where

open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import RWhileValStore using (Val; nil; cons; Store; _≢ℕ_)
open import RWhileCRep
import RWhileRevFull
import RWhileDet
open RWhileRevFull.Core Store
open RWhileDet.Det Store

module _ (funext : ∀ {A : Set} {B : Set} {f g : A → B}
                 → (∀ z → f z ≡ g z) → f ≡ g) where

  ----------------------------------------------------------------------
  -- Pattern READ is deterministic (same pattern, same source store ⇒ same
  -- value and same result store).

  Read-det : ∀ {p σ v σ' w σ''}
           → Read p σ v σ' → Read p σ w σ'' → (v ≡ w) × (σ' ≡ σ'')
  Read-det {σ' = σ'} {σ'' = σ''} (rd-var {x = x} ve1 cl1 fr1) (rd-var ve2 cl2 fr2) =
    trans ve1 (sym ve2) , funext pw
    where
      pw : ∀ y → σ' y ≡ σ'' y
      pw y with x ≟ y
      ... | yes refl = trans cl1 (sym cl2)
      ... | no  x≠y  = trans (sym (fr1 y x≠y)) (fr2 y x≠y)
  Read-det rd-val rd-val = refl , refl
  Read-det (rd-cons r1 r2) (rd-cons r1' r2') with Read-det r1 r1'
  ... | refl , refl with Read-det r2 r2'
  ...   | refl , refl = refl , refl

  ----------------------------------------------------------------------
  -- Pattern WRITE is deterministic (same pattern, source store and value ⇒
  -- same result store).

  Write-det : ∀ {p σ v σ' σ''} → Write p σ v σ' → Write p σ v σ'' → σ' ≡ σ''
  Write-det {σ' = σ'} {σ'' = σ''} (wr-var {x = x} cl1 ve1 fr1) (wr-var cl2 ve2 fr2) =
    funext pw
    where
      pw : ∀ y → σ' y ≡ σ'' y
      pw y with x ≟ y
      ... | yes refl = trans (sym ve1) ve2
      ... | no  x≠y  = trans (sym (fr1 y x≠y)) (fr2 y x≠y)
  Write-det wr-val wr-val = refl
  Write-det (wr-cons w2 w1) (wr-cons w2' w1') with Write-det w2 w2'
  ... | refl with Write-det w1 w1'
  ...   | refl = refl

  ----------------------------------------------------------------------
  -- Hence `CRep` and its inverse are deterministic, and the inverse cancels.

  crep-det : ∀ lhs rhs → Det⟨ crepC lhs rhs ⟩
  crep-det lhs rhs (v , σ1 , rd , wr) (v' , σ1' , rd' , wr') with Read-det rd rd'
  ... | refl , refl = Write-det wr wr'

  -- Det⟨ inv (crepC lhs rhs) ⟩ = injectivity of CRepRel, via CRep-rev.
  crep-inv-det : ∀ lhs rhs → Det⟨ inv (crepC lhs rhs) ⟩
  crep-inv-det lhs rhs c1 c2 = crep-det rhs lhs (CRep-rev c1) (CRep-rev c2)

  -- FUNCTION-LEVEL INVERSE for pattern replacement.
  crep-inv-cancels : ∀ {lhs rhs s t t'}
                   → crepC lhs rhs ⊢ s ⇒ t → inv (crepC lhs rhs) ⊢ t ⇒ t' → t' ≡ s
  crep-inv-cancels {lhs} {rhs} = inv-cancels (crep-inv-det lhs rhs)
