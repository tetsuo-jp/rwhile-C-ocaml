{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 6: the PRODUCTION-FAITHFUL fix locus (measured 2026-07-10).
--
-- The implementation `examples/spec_av_bti.rwhile` already has a binding-time-aware
-- MKAV, selective dynamicize and loop-BTA, yet `[comp2]('S.swap) == B` is FALSE:
-- comp2 emits  `var2 <= cons 'swap var2`  i.e. it embeds the opcode via `('val.'swap)`
-- instead of dispatching.  fp1 and the fp1-scale dynamic-cond probe are both sound, so
-- the defect is SELF-APPLICATION-SPECIFIC.
--
-- This module models the fix PATTERN faithfully to the production macros and proves
-- it is fp1-safe.  Two production facts are modelled exactly:
--   * AV-LIFT (spec_av_bti.rwhile:149) lowers `('S.v)` to `('val.v)` — a CONSTANT
--     (RWhileAVSound.lift: `lift (S v) = cVal v`).  So a `('val.'swap)` in the
--     residual ⟺ the lifted slot leaf was static `S 'swap`.  AV-LIFT is faithful.
--   * MKAV's then-branch (spec_av_bti.rwhile:1111) builds the read-slot AV
--     `('C.(('S.Src).('D.('var.Ic))))` — modelled `prodThen`, taken as a REPRESENTATIVE
--     frozen node (whichever slot is wrongly static, the shape is this).
--
-- We prove:  a static car `('S.Src)` FREEZES the source (its lift is the constant
-- `cVal Src` = the observed `('val.'swap)`), and no static AV can track a runtime-
-- dependent source (`prodThen-car-unsound`).  The fix PATTERN drives such a node
-- through `mkAV` by binding time (`fixThen`): under BT='S (fp1) it is IDENTICAL to
-- production (`fix-agrees-on-fp1` — no fp1 regression), and under BT='D it residualises
-- to a `D` hole that TRACKS the runtime value (`fixThen-car-tracks`).
--
-- CAVEAT: this pins the fix SHAPE and its fp1-safety, not WHICH slot is wrongly static
-- in comp2 — identifying that (it may be MKAV's car, ASSEMBLE-FP1's output slot, or a
-- SPEC-CMD-AV intermediate) needs a live trace.  What is proved: the offending residual
-- is a lifted STATIC leaf, and replacing its construction with a BT-driven `mkAV` both
-- removes the over-static embed under self-application AND leaves fp1 byte-identical.
------------------------------------------------------------------------
module RWhileOfflineBTA6 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import RWhileAVSound
  using ( Val; Code; cVal; cVar; ⟦_⟧c
        ; AV; S; D; C; γ; lift; avHd )
open import RWhileOfflineBTA
  using ( BT; sta; dyn; mkAV; staticAV; sS; no-static-identity )

------------------------------------------------------------------------
-- The production MKAV then-branch (BT='S): read-slot AV for a variable whose static
-- half is `src` and whose dynamic half is the runtime input hole (cVar).

prodThen : Val → AV
prodThen src = C (S src) (D cVar)          -- ('C.(('S.src).('D.('var.Ic))))

-- AV-LIFT of the car is the constant `cVal src` — i.e. the observed `('val.'swap)`.
prodThen-car-lift : ∀ src → lift (avHd (prodThen src)) ≡ cVal src
prodThen-car-lift src = refl

-- ...and that residual denotes a CONSTANT, independent of the runtime input.
prodThen-car-const : ∀ src ρ → ⟦ lift (avHd (prodThen src)) ⟧c ρ ≡ src
prodThen-car-const src ρ = refl

-- So the frozen car cannot track a runtime-dependent source (e.g. the identity on ρ,
-- the paradigmatic "the opcode is really the dynamic input" case).  This is the exact
-- unsoundness behind `[comp2]('S.swap) == B : false`.
prodThen-car-unsound : ∀ src → ¬ (∀ ρ → γ (avHd (prodThen src)) ρ ≡ ρ)
prodThen-car-unsound src = no-static-identity (sS src)

------------------------------------------------------------------------
-- THE FIX: build the car through `mkAV` by binding time instead of a hardcoded 'S.
-- (In production: seed the static-half node with the source's binding time, so the
-- OUTER specialiser residualises it under self-application instead of baking 'S.)

fixThen : BT → Val → AV
fixThen bt src = C (mkAV bt src cVar) (D cVar)

-- fp1 SAFETY: under BT='S the fix is IDENTICAL to the current production then-branch,
-- so fp1 residuals are unchanged (mkAV sta src _ = S src).
fix-agrees-on-fp1 : ∀ src → fixThen sta src ≡ prodThen src
fix-agrees-on-fp1 src = refl

-- SELF-APPLICATION: under BT='D the car residualises to a `D` hole that TRACKS the
-- runtime source (γ = ρ) — exactly what the frozen version could not do.
fixThen-car-tracks : ∀ src ρ → γ (avHd (fixThen dyn src)) ρ ≡ ρ
fixThen-car-tracks src ρ = refl

-- The fixed car is never a static leaf (so AV-LIFT never emits `('val.src)` for it) —
-- the structural guarantee that removes the over-static embed.
fixThen-car-nonstatic : ∀ src → ¬ staticAV (avHd (fixThen dyn src))
fixThen-car-nonstatic src ()
