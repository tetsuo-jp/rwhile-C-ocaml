{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Grounding the executable interpreter in R-WHILE's REAL primitive:
-- an abstraction-free, executable `rupdF` (the reversible XOR-update as a
-- partial function `Store → Maybe Store`, the form `rupdate` takes in
-- src/EvalRwhile.ml), proved equivalent to the relational `RAss`.
--
--   rupdF-sound    : rupdF x v σ ≡ just σ' → RAss x v σ σ'
--   rupdF-complete : RAss x v σ σ' → rupdF x v σ ≡ just σ'   (uses funext)
--
-- Hence the EXECUTABLE assignment `frun (fatom (rupdF x v))` computes exactly
-- the relational assignment that RWhileValStore proves reversible, and
-- RWhileCRepDet/RWhileDetConcrete prove deterministic.  No abstraction
-- remains in this primitive — it is ordinary, runnable Agda code that
-- mirrors the OCaml `rupdate`.
------------------------------------------------------------------------

module RWhileExecConcrete where

open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import RWhileValStore using (Val; nil; cons; Store; _≢ℕ_; RAss; rass)
open import RWhileExec
import RWhileRevFull
open RWhileRevFull.Core Store

------------------------------------------------------------------------
-- Decidable equality on values, and single-variable store update.

_≟V_ : (a b : Val) → Dec (a ≡ b)
nil       ≟V nil       = yes refl
nil       ≟V cons _ _  = no λ ()
cons _ _  ≟V nil       = no λ ()
cons a b  ≟V cons c d  with a ≟V c | b ≟V d
... | yes refl | yes refl = yes refl
... | no  ¬p   | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }

set : ℕ → Val → Store → Store
set x v σ y with x ≟ y
... | yes _ = v
... | no  _ = σ y

set-eq : ∀ x v σ → set x v σ x ≡ v
set-eq x v σ with x ≟ x
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

set-neq : ∀ {x y} v σ → x ≢ℕ y → set x v σ y ≡ σ y
set-neq {x} {y} v σ x≢y with x ≟ y
... | yes p = ⊥-elim (x≢y p)
... | no  _ = refl

------------------------------------------------------------------------
-- The reversible XOR-update as an executable partial function (rupdate).

rupdF : ℕ → Val → Store → Maybe Store
rupdF x v σ with σ x ≟V nil
... | yes _ = just (set x v σ)
... | no  _ with σ x ≟V v
...   | yes _ = just (set x nil σ)
...   | no  _ = nothing

------------------------------------------------------------------------
-- SOUNDNESS: any successful update is a legal reversible step (no funext).

rupdF-sound : ∀ {x v σ σ'} → rupdF x v σ ≡ just σ' → RAss x v σ σ'
rupdF-sound {x} {v} {σ} h with σ x ≟V nil | h
... | yes p | h′ with just-injective h′
...   | refl = rass (inj₁ (p , set-eq x v σ)) (λ y x≢y → sym (set-neq v σ x≢y))
rupdF-sound {x} {v} {σ} h | no _ | h′ with σ x ≟V v | h′
...   | yes q | h″ with just-injective h″
...     | refl = rass (inj₂ (q , set-eq x nil σ)) (λ y x≢y → sym (set-neq nil σ x≢y))
rupdF-sound {x} {v} {σ} h | no _ | h′ | no _ | ()

------------------------------------------------------------------------
-- COMPLETENESS: every legal reversible step is computed by rupdF (uses funext).

module _ (funext : ∀ {A : Set} {B : Set} {f g : A → B}
                 → (∀ z → f z ≡ g z) → f ≡ g) where

  rupdF-complete : ∀ {x v σ σ'} → RAss x v σ σ' → rupdF x v σ ≡ just σ'
  rupdF-complete {x} {v} {σ} {σ'} (rass (inj₁ (p , q)) fr) with σ x ≟V nil
  ... | yes _   = cong just (funext pw)
      where
        -- in each branch `set x _ σ y` reduces via the SAME `x ≟ y` decision.
        pw : ∀ y → set x v σ y ≡ σ' y
        pw y with x ≟ y
        ... | yes refl = sym q                 -- set→v ; q : σ' x ≡ v
        ... | no  x≢y  = fr y x≢y               -- set→σ y ; fr : σ y ≡ σ' y
  ... | no ¬nil = ⊥-elim (¬nil p)
  rupdF-complete {x} {v} {σ} {σ'} (rass (inj₂ (p , q)) fr) with σ x ≟V nil
  ... | yes nileq = cong just (funext pw)       -- σx≡nil and σx≡v ⇒ v≡nil
      where
        v≡nil : v ≡ nil
        v≡nil = trans (sym p) nileq
        pw : ∀ y → set x v σ y ≡ σ' y
        pw y with x ≟ y
        ... | yes refl = trans v≡nil (sym q)    -- set→v ≡ nil ; q : σ' x ≡ nil
        ... | no  x≢y  = fr y x≢y
  ... | no _ with σ x ≟V v
  ...   | yes _   = cong just (funext pw)
        where
          pw : ∀ y → set x nil σ y ≡ σ' y
          pw y with x ≟ y
          ... | yes refl = sym q                -- set→nil ; q : σ' x ≡ nil
          ... | no  x≢y  = fr y x≢y
  ...   | no ¬v   = ⊥-elim (¬v p)

------------------------------------------------------------------------
-- The executable, abstraction-free assignment, and its correctness.

open Exec Store using (FCmd; fatom; frun)

fassign : ℕ → Val → FCmd
fassign x v = fatom (rupdF x v)

-- Running the executable assignment yields a legal reversible-assignment step
-- (so it is reversible and deterministic, by RWhileValStore / RWhileDetConcrete).
fassign-sound : ∀ {x v s t} → frun (fassign x v) s ≡ just t → RAss x v s t
fassign-sound h = rupdF-sound h
