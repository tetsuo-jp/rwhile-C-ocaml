{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 案1-B (Agda-first, step (a)): the loop the LoopBTA decision RESIDUALISES is a
-- REVERSIBLE R-WHILE loop.
--
-- RWhileLoopBTA proved WHEN to residualise (a dynamic entry/exit forces it).
-- Before changing spec_av's 'loop handler, we pin the reversibility of what it
-- emits: the residual loop `from (lift e) do D loop L until (lift f)`.  Its tests
-- become Val-state predicates (truthiness of running the residual code) and its
-- body the residual commands; this is exactly a `loop` of RWhileRevFull.Core,
-- whose inversion (entry/exit swapped) is already machine-checked sound and
-- involutive.  So residualising preserves reversibility -- no new proof burden on
-- the loop construct, the implementation only has to emit this shape.
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileLoopBTARev where

open import Data.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileAVSound using (Val; Code; ⟦_⟧c)
open import RWhileLoopBTA using (truthy)
import RWhileRevFull

-- reversibility apparatus instantiated at the runtime store S = Val
open RWhileRevFull.Core Val
  using (Cmd; loop; inv; _⊢_⇒_; inv-sound; inv-inv)

------------------------------------------------------------------------
-- A residual test code becomes a Val-state predicate: run it, take truthiness.

testOf : Code → (Val → Bool)
testOf c σ = truthy (⟦ c ⟧c σ)

-- The residual loop emitted when the decision must residualise: lifted entry /
-- exit test codes ce / cf and residual body commands D, L.
resLoop : Code → Cmd → Cmd → Code → Cmd
resLoop ce D L cf = loop (testOf ce) D L (testOf cf)

------------------------------------------------------------------------
-- It is a reversible R-WHILE loop (inheriting RWhileRevFull).

-- inversion swaps entry/exit and inverts the bodies (structurally, by refl).
resLoop-inv : ∀ ce D L cf → inv (resLoop ce D L cf) ≡ resLoop cf (inv D) (inv L) ce
resLoop-inv ce D L cf = refl

-- the inverse computes the converse run: forward s⇒t  ⟹  inverse t⇒s.
resLoop-reversible : ∀ ce D L cf {s t} →
  resLoop ce D L cf ⊢ s ⇒ t → inv (resLoop ce D L cf) ⊢ t ⇒ s
resLoop-reversible ce D L cf d = inv-sound d

-- double inversion is the identity (inverting the residual loop twice = itself).
resLoop-inv-inv : ∀ ce D L cf → inv (inv (resLoop ce D L cf)) ≡ resLoop ce D L cf
resLoop-inv-inv ce D L cf = inv-inv (resLoop ce D L cf)
