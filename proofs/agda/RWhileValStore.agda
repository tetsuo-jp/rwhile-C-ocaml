{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Step (1): instantiate the abstract reversibility framework with
-- R-WHILE's concrete store and its reversible assignment `rupdate`.
--
-- The abstract development (RWhileRev / RWhileRevFull) parameterised over an
-- arbitrary store S and abstract atomic relations.  Here we give the
-- concrete atom: the reversible XOR-update `x ^= e` (src/EvalRwhile.ml's
-- `rupdate`), prove it is a partial involution (its inverse is itself), and
-- conclude that the concrete assignment is reversible — hence, with the
-- abstract `inv-sound`, that any R-WHILE program built from assignments,
-- sequencing, the reversible conditional and the reversible loop is
-- reversible.
------------------------------------------------------------------------

module RWhileValStore where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
open import Relation.Nullary using (¬_)

import RWhileRevFull

------------------------------------------------------------------------
-- Values: R-WHILE's binary trees (valT).

data Val : Set where
  nil  : Val
  cons : Val → Val → Val

-- Store: a variable environment (variables are ℕ indices, as in p2d).
Store : Set
Store = ℕ → Val

_≢ℕ_ : ℕ → ℕ → Set
x ≢ℕ y = ¬ (x ≡ y)

------------------------------------------------------------------------
-- The reversible XOR-assignment `x ^= e`, modelled as a relation on stores
-- with `v` the (x-independent, by R-WHILE's linearity rule) value of `e`.
--
-- rupdate (src/EvalRwhile.ml): assigning v when the slot is nil SETS it to v;
-- assigning v when the slot already holds v CLEARS it to nil; any other case
-- is stuck (the reversibility condition).  Every other variable is unchanged
-- (the "frame").  We describe σ' relationally (no functional store update),
-- so the involution proof needs no function extensionality.

record RAss (x : ℕ) (v : Val) (σ σ' : Store) : Set where
  constructor rass
  field
    toggle : (σ x ≡ nil × σ' x ≡ v) ⊎ (σ x ≡ v × σ' x ≡ nil)
    frame  : ∀ y → x ≢ℕ y → σ y ≡ σ' y

------------------------------------------------------------------------
-- KEY LEMMA: `rupdate` is a partial involution — its converse is itself.
-- (This is exactly why `inv (CAss x e) = CAss x e` in src/InvRwhile.ml.)

RAss-sym : ∀ {x v σ σ'} → RAss x v σ σ' → RAss x v σ' σ
RAss-sym (rass (inj₁ (p , q)) fr) = rass (inj₂ (q , p)) (λ y h → sym (fr y h))
RAss-sym (rass (inj₂ (p , q)) fr) = rass (inj₁ (q , p)) (λ y h → sym (fr y h))

------------------------------------------------------------------------
-- Instantiate the abstract framework at the concrete store, with the
-- atomic operation being `rupdate`.

open RWhileRevFull.Core Store

-- A concrete reversible assignment command.
assign : ℕ → Val → Cmd
assign x v = atom (RAss x v)

-- The concrete assignment is reversible: running it backward undoes it.
-- (Specialises the abstract `inv-sound`; the atom case bottoms out in the
-- involution lemma RAss-sym above.)
assign-reversible : ∀ {x v s t} → assign x v ⊢ s ⇒ t → assign x v ⊢ t ⇒ s
assign-reversible (e-atom r) = e-atom (RAss-sym r)

------------------------------------------------------------------------
-- Consequence: ANY R-WHILE program over concrete assignments, sequencing,
-- the reversible conditional and the reversible loop is reversible — this is
-- just the abstract theorem at the concrete store.  E.g. a two-assignment
-- program reverses by inverting (and flipping) its steps:

program-reversible : ∀ {c s t} → c ⊢ s ⇒ t → inv c ⊢ t ⇒ s
program-reversible = inv-sound
