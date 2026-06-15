{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Step (3): a reversible Intermediate Language (IL) and a VERIFIED
-- translation to R-WHILE.
--
-- This demonstrates the layered-correctness architecture: prove things in a
-- simpler/more-efficient IL, then transport them to R-WHILE through a
-- translation proved correct.
--
-- The IL differs from R-WHILE's core in its sequencing: an IL program is a
-- FLAT list of blocks (`Seq = List Block`), not a right-nested binary `⨾`.
-- Flat sequences are the natural efficient IR (associativity is free, no
-- re-bracketing).  The translation `trS` folds a list into `⨾`.
--
-- Proved (all --safe):
--   * SEMANTIC PRESERVATION   ⟦ p ⟧S s ⇒ t  ↔  trS p ⊢ s ⇒ t
--       (tr-soundS / tr-completeS) — the translation is correct.
--   * IL REVERSIBILITY        ⟦ p ⟧S s ⇒ t  →  ⟦ invS p ⟧S t ⇒ s
--       proved directly in the IL (il-revS); `invS` reverses the flat list
--       and inverts each block, exactly the efficient counterpart of
--       R-WHILE's `inv`.
--
-- (IL loops are an obvious extension, following RWhileRevFull's treatment.)
------------------------------------------------------------------------

module RWhileIL where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

import RWhileRevFull

module IL (S : Set) where
  open RWhileRevFull.Core S

  ----------------------------------------------------------------------
  -- IL syntax: flat (list) sequencing of reversible blocks.

  data Block : Set₁ where
    bAtom : (S → S → Set) → Block
    bCond : (S → Bool) → List Block → List Block → (S → Bool) → Block

  Seq : Set₁
  Seq = List Block

  ----------------------------------------------------------------------
  -- IL big-step semantics (own semantics, executed left-to-right).

  data ⟦_⟧B_⇒_ : Block → S → S → Set₁
  data ⟦_⟧S_⇒_ : Seq → S → S → Set₁

  data ⟦_⟧B_⇒_ where
    b-atom : ∀ {A s t} → A s t → ⟦ bAtom A ⟧B s ⇒ t
    b-then : ∀ {e c d f s t}
           → e s ≡ true  → ⟦ c ⟧S s ⇒ t → f t ≡ true  → ⟦ bCond e c d f ⟧B s ⇒ t
    b-else : ∀ {e c d f s t}
           → e s ≡ false → ⟦ d ⟧S s ⇒ t → f t ≡ false → ⟦ bCond e c d f ⟧B s ⇒ t

  data ⟦_⟧S_⇒_ where
    s-nil  : ∀ {s} → ⟦ [] ⟧S s ⇒ s
    s-cons : ∀ {b bs s t u} → ⟦ b ⟧B s ⇒ t → ⟦ bs ⟧S t ⇒ u → ⟦ b ∷ bs ⟧S s ⇒ u

  ----------------------------------------------------------------------
  -- Translation IL → R-WHILE.  The empty sequence becomes the identity
  -- atom `Id`; cons becomes `⨾`.

  Id : S → S → Set
  Id s t = s ≡ t

  trB : Block → Cmd
  trS : Seq → Cmd
  trB (bAtom A)       = atom A
  trB (bCond e c d f) = cond e (trS c) (trS d) f
  trS []       = atom Id
  trS (b ∷ bs) = trB b ⨾ trS bs

  ----------------------------------------------------------------------
  -- SEMANTIC PRESERVATION: the translation is correct (both directions).

  tr-soundB : ∀ {b s t} → ⟦ b ⟧B s ⇒ t → trB b ⊢ s ⇒ t
  tr-soundS : ∀ {p s t} → ⟦ p ⟧S s ⇒ t → trS p ⊢ s ⇒ t
  tr-soundB (b-atom a)        = e-atom a
  tr-soundB (b-then es cs ft) = e-then es (tr-soundS cs) ft
  tr-soundB (b-else es ds ft) = e-else es (tr-soundS ds) ft
  tr-soundS s-nil          = e-atom refl
  tr-soundS (s-cons bb bs) = e-seq (tr-soundB bb) (tr-soundS bs)

  tr-completeB : ∀ {b s t} → trB b ⊢ s ⇒ t → ⟦ b ⟧B s ⇒ t
  tr-completeS : ∀ {p s t} → trS p ⊢ s ⇒ t → ⟦ p ⟧S s ⇒ t
  tr-completeB {bAtom A}       (e-atom a)         = b-atom a
  tr-completeB {bCond e c d f} (e-then es cs ft)  = b-then es (tr-completeS cs) ft
  tr-completeB {bCond e c d f} (e-else es ds ft)  = b-else es (tr-completeS ds) ft
  tr-completeS {[]}     (e-atom refl)     = s-nil
  tr-completeS {b ∷ bs} (e-seq bb bs')    = s-cons (tr-completeB bb) (tr-completeS bs')

  ----------------------------------------------------------------------
  -- IL inversion: reverse the flat list, invert each block.

  invB : Block → Block
  invS : Seq → Seq
  invB (bAtom A)       = bAtom (λ s t → A t s)        -- converse atom
  invB (bCond e c d f) = bCond f (invS c) (invS d) e  -- swap entry/exit tests
  invS []       = []
  invS (b ∷ bs) = invS bs ++ (invB b ∷ [])           -- reverse, inverting blocks

  ----------------------------------------------------------------------
  -- Appending sequences composes their executions (needed to reverse a list).

  ++-exec : ∀ {xs ys s m u} → ⟦ xs ⟧S s ⇒ m → ⟦ ys ⟧S m ⇒ u → ⟦ xs ++ ys ⟧S s ⇒ u
  ++-exec s-nil          ys = ys
  ++-exec (s-cons bb xs) ys = s-cons bb (++-exec xs ys)

  ----------------------------------------------------------------------
  -- IL REVERSIBILITY (proved directly in the IL).

  il-revB : ∀ {b s t} → ⟦ b ⟧B s ⇒ t → ⟦ invB b ⟧B t ⇒ s
  il-revS : ∀ {p s t} → ⟦ p ⟧S s ⇒ t → ⟦ invS p ⟧S t ⇒ s
  il-revB (b-atom a)        = b-atom a                       -- converse: A t s
  il-revB (b-then es cs ft) = b-then ft (il-revS cs) es      -- tests swapped
  il-revB (b-else es ds ft) = b-else ft (il-revS ds) es
  il-revS s-nil             = s-nil
  il-revS (s-cons bb bs)    =
    -- invS (b ∷ bs) = invS bs ++ [invB b]; run reversed bs, then reversed b
    ++-exec (il-revS bs) (s-cons (il-revB bb) s-nil)
