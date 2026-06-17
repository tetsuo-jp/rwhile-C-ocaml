{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- C-layer design spec for the B-layer fp2 fix: BINDING-TIME correctness.
--
-- Root cause of the failing 2nd reversible projection (compiler generation by
-- self-application), localised to spec_av.rwhile:1051
--     FpPart <= cons 'C (cons (cons 'S Src) (cons 'D (cons 'var FpIc)));
-- The specialiser tags its static input `Src` with `'S` UNCONDITIONALLY — it
-- statically commits the binding-time of its own input.
--   * fp1  : Src really is static -> correct.
--   * fp2  : under self-application the inner specialiser's `Src` is DYNAMIC,
--            but the code still tags it `'S` -> over-static degeneration
--            (the fp2 compiler ignores its runtime input; cf. the 1158-byte
--            broken compiler observed, plan_fp1_stage_c.md 6.3.6).
--
-- This module models a minimal specialiser step over annotated values and
-- proves, in the small core:
--   * fp1-ok            : when the input is static, the unconditional-`'S`
--                         builder agrees with the binding-time-aware one;
--   * fp2-buggy-mistags : when the input is dynamic (self-application), the
--                         unconditional-`'S` builder MIS-TAGS (≢ the correct AV);
--   * buggy-ignores-input / correct-uses-input / overstatic-wrong:
--                         the consequence — a statically-committed residual
--                         BAKES a constant and IGNORES its runtime input, whereas
--                         the binding-time-aware residual USES it.
--
-- So the precise fix B needs is to build the partial input with a binding-time-
-- AWARE tag (`mkAV bt`), not a constant `'S` — a BTA / two-level discipline,
-- exactly the self-applicability requirement (Futamura/Jones).
------------------------------------------------------------------------

module RWhileRevProj2BT where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

module Spec (V : Set) where

  -- annotated value: a known static value, or dynamic (runtime-only).
  data AV : Set where
    sta : V → AV
    dyn : AV

  -- residual of a unary operation.
  data Res : Set where
    konst : V → Res          -- baked constant: ignores the runtime input
    resid : (V → V) → Res    -- the operation kept: uses the runtime input

  run : Res → V → V
  run (konst c) _ = c
  run (resid f) d = f d

  -- one specialisation step for op `f` against the input's annotated value.
  specOp : (V → V) → AV → Res
  specOp f (sta v) = konst (f v)   -- static input: compute f v now (bake)
  specOp f dyn     = resid f       -- dynamic input: residualise f

  ----------------------------------------------------------------------
  -- The two partial-input builders.

  -- spec_av.rwhile:1051 — UNCONDITIONAL static tag (the bug).
  mkBuggy : V → AV
  mkBuggy v = sta v

  -- The FIX — tag by the input half's actual binding time.
  data BT : Set where st dy : BT
  mkAV : BT → V → AV
  mkAV st v = sta v
  mkAV dy v = dyn

  ----------------------------------------------------------------------
  -- fp1: the input is genuinely static (BT = st).  The buggy builder and the
  -- binding-time-aware builder AGREE, so fp1 is correct either way.
  fp1-ok : ∀ f v → specOp f (mkBuggy v) ≡ specOp f (mkAV st v)
  fp1-ok f v = refl

  -- fp2 (self-application): the input is DYNAMIC (BT = dy).  The unconditional
  -- `'S` builder MIS-TAGS it — its residual differs from the correct one.
  fp2-buggy-mistags : ∀ f v → ¬ (specOp f (mkBuggy v) ≡ specOp f (mkAV dy v))
  fp2-buggy-mistags f v ()

  ----------------------------------------------------------------------
  -- The CONSEQUENCE of mis-tagging a dynamic input as static.

  -- the buggy residual ignores its runtime input (it baked a constant):
  buggy-ignores-input : ∀ f v d₁ d₂ → run (specOp f (mkBuggy v)) d₁ ≡ run (specOp f (mkBuggy v)) d₂
  buggy-ignores-input f v d₁ d₂ = refl

  -- the binding-time-aware residual USES its runtime input:
  correct-uses-input : ∀ f v d → run (specOp f (mkAV dy v)) d ≡ f d
  correct-uses-input f v d = refl

  ----------------------------------------------------------------------
  -- when the input is really dynamic, static-committing gives the WRONG answer:
  -- it computes f v (a fixed guess) instead of f d.
  overstatic-wrong : ∀ (f : V → V) v d → ¬ (f v ≡ f d)
                   → ¬ (run (specOp f (mkBuggy v)) d ≡ run (specOp f (mkAV dy v)) d)
  overstatic-wrong f v d ¬eq = ¬eq
