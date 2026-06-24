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

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileAVSound using (Val; ⟨⟩; _·_; Code; cVal; ⟦_⟧c)
open import RWhileLoopBTA using (truthy)
import RWhileRevFull

-- reversibility apparatus instantiated at the runtime store S = Val
open RWhileRevFull.Core Val
  using (Cmd; loop; inv; _⊢_⇒_; inv-sound; inv-inv; Rest; r-exit; r-iter)

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

------------------------------------------------------------------------
-- WHY residualisation must NOT constant-fold the entry test (the subtlety the
-- implementation must respect).
--
-- When a loop has a STATIC entry but a DYNAMIC exit (the AUX / '41 case:
-- `from (=? Cnt nil) ... until (=? Cnt J)` with J dynamic), the entry's AV is the
-- static `S vtrue`, and AV-LIFT folds it to the literal-true code `cVal vtrue`.
-- The entry test of the residual loop would then be `testOf (cVal vtrue)`, i.e.
-- CONSTANTLY TRUE.  But a reversible loop's `r-iter` (loop-back) step REQUIRES the
-- entry test to be FALSE on the loop-back store -- so a constant-true entry can
-- NEVER iterate.  Hence folding the entry to a constant cannot represent a loop
-- that runs its body more than once; residualisation must keep a REAL entry test
-- (dynamicise the control slots, e.g. Cnt, and RE-SPECIALISE the entry).

-- the constant-folded entry test (AV-LIFT of static `S vtrue`): always true.
constTrueTest : Val → Bool
constTrueTest = testOf (cVal (⟨⟩ · ⟨⟩))

constTrueTest-true : ∀ σ → constTrueTest σ ≡ true
constTrueTest-true σ = refl

-- A constant-true entry forbids iteration: every Rest is the immediate exit
-- (r-iter is impossible, its entry-false premise being true ≡ false).
constEntry-no-iter : ∀ {D L f w x} →
  Rest constTrueTest D L f w x → (f w ≡ true) × (w ≡ x)
constEntry-no-iter (r-exit fw)               = fw , refl
constEntry-no-iter (r-iter fw Lwu () Duv rest)
