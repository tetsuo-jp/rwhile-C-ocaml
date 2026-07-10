{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 9: REVERSIBILITY / information-loss check (answering the
-- question "情報消失がないか＝可逆性制約は満たされるか").
--
-- Stages 1-8 proved FORWARD soundness (γ / exec correctness).  But R-WHILE is a
-- REVERSIBLE language, and the paper's defining property is that a reversible
-- specialiser's meaning is INJECTIVE (no information loss).  This module checks both
-- reversibility obligations on the stage-8 command model:
--
--  (A) RESIDUAL reversibility -- the produced programs are reversible: running a
--      command and then running it BACKWARDS recovers the store (`rexec-exec`), with
--      the swap primitive a genuine involution (`swapV-invol`).
--
--  (B) SPECIALISER reversibility (injectivity = no information loss):
--       * the correct offline `specOff` is INFORMATION-PRESERVING -- it keeps every
--         branch, so it is the identity on control structure (`specOff-id`) and hence
--         INJECTIVE (`specOff-injective`).
--       * the online-agenda bug `specBug` DESTROYS information -- it maps two distinct
--         sources (differing only in a dropped then-branch) to the SAME residual
--         (`specBug-collapses`), so it is NOT injective (`specBug-not-injective`).
--
-- Conclusion: comp2's dropped then-branch is not merely a soundness bug but a
-- REVERSIBILITY VIOLATION (it destroys the branch program), exactly the failure the
-- reversible-specialiser injectivity requirement forbids; the offline fix (keep both
-- branches) restores injectivity.
------------------------------------------------------------------------
module RWhileOfflineBTA9 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; veq)
open import RWhileOfflineBTA8
  using ( Cmd; skip; swap; echoOp; seqC; ifOp; exec; swapV; ifV; specOff; specBug )

------------------------------------------------------------------------
-- (A) RESIDUAL reversibility.

-- swap is a genuine involution (the reversibility of R-WHILE's cons-swap).
swapV-invol : ∀ x → swapV (swapV x) ≡ x
swapV-invol ⟨⟩      = refl
swapV-invol (a · b) = refl

-- Run a command BACKWARDS (models R-WHILE inversion; the opcode is preserved so a
-- dispatch can re-decide the branch on the reverse run).  echoOp (s ↦ op·s) reverses
-- by dropping the echoed head.
rexec : Cmd → Val → Val → Val
rexec skip       op s = s
rexec swap       op s = swapV s
rexec echoOp     op (v · s) = s
rexec echoOp     op ⟨⟩      = ⟨⟩
rexec (seqC a b) op s = rexec a op (rexec b op s)
rexec (ifOp v c d) op s = ifV (veq op v) (rexec c op s) (rexec d op s)

-- REVERSIBILITY: forward then backward recovers the store -- no information is lost.
rexec-exec : ∀ c op s → rexec c op (exec c op s) ≡ s
rexec-exec skip       op s = refl
rexec-exec swap       op s = swapV-invol s
rexec-exec echoOp     op s = refl
rexec-exec (seqC a b) op s
  rewrite rexec-exec b op (exec a op s) = rexec-exec a op s
rexec-exec (ifOp v c d) op s with veq op v
... | ⟨⟩      = rexec-exec d op s
... | (_ · _) = rexec-exec c op s

------------------------------------------------------------------------
-- (B) SPECIALISER reversibility = injectivity (no information loss).

-- The correct offline specialiser keeps EVERY branch -- it is the identity on control
-- structure, so no program information is lost.
specOff-id : ∀ c → specOff c ≡ c
specOff-id skip        = refl
specOff-id swap        = refl
specOff-id echoOp      = refl
specOff-id (seqC a b)  rewrite specOff-id a | specOff-id b = refl
specOff-id (ifOp v c d) rewrite specOff-id c | specOff-id d = refl

-- ...hence INJECTIVE: distinct sources give distinct residuals (the reversible-
-- specialiser property: its meaning is injective).
specOff-injective : ∀ c1 c2 → specOff c1 ≡ specOff c2 → c1 ≡ c2
specOff-injective c1 c2 eq = trans (sym (specOff-id c1)) (trans eq (specOff-id c2))

-- The online-agenda BUG destroys information: two sources differing only in the dropped
-- then-branch (swap vs skip) map to the SAME residual.
specBug-collapses : specBug (ifOp vtrue swap skip) ≡ specBug (ifOp vtrue skip skip)
specBug-collapses = refl

-- ...so it is NOT injective = it VIOLATES the reversible-specialiser requirement.
specBug-not-injective : ¬ (∀ c1 c2 → specBug c1 ≡ specBug c2 → c1 ≡ c2)
specBug-not-injective inj = distinct (inj (ifOp vtrue swap skip) (ifOp vtrue skip skip) specBug-collapses)
  where
    distinct : ifOp vtrue swap skip ≡ ifOp vtrue skip skip → ⊥
    distinct ()
