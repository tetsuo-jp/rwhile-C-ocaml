{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- AV symbolic evaluation and the spec-correct (H1) obligation, proved for the
-- REAL annotated-value mechanism (#2 / N2 step 2, gap G1).
--
-- RWhileAVSound proved each AV operation sound w.r.t. concretisation.  Here we
-- assemble them into the symbolic evaluator `aeval` (the SPEC-EXP-AV stepper's
-- denotation) and the AV residualiser, and discharge the H1 hypothesis of the
-- modular Futamura hierarchy (RWhileFutamura2) for the actual AV machinery —
-- NOT the closure stand-in of RWhileFutamura2Inst nor the op-list table of
-- RWhileRevProj2Self.
--
-- Binding-time split (spec_av's MKAV discipline): a program `p` reads a paired
-- input ⟨s,d⟩ = s · d whose HEAD is the static argument and TAIL the dynamic
-- runtime input.  Specialising p to a static s symbolically evaluates p over the
-- partially static AV  C (S s) (D cVar)  — head static, tail dynamic — and lifts
-- the result to a residual.  Then:
--
--   spec-correct :  ⟦ spec p s ⟧c d  ≡  ⟦ p ⟧c (s · d)        -- H1 (= fp1)
--
-- holds by AV soundness (aeval-sound + lift-sound), with the dynamic tail
-- genuinely USED (no over-static degeneration — the property RWhileRevProj2BT
-- demands).  `--safe`, no postulates/holes.
--
-- Remaining for a full fp2/fp3 Hierarchy instance: H2 (spec-impl) — representing
-- this specialiser as a program in its own object language (self-application).
-- That is the same residual engineering the IEICE draft leaves open; H1 — the
-- correctness core — is now machine-checked for the real AV algebra.
------------------------------------------------------------------------

module RWhileAVSpec where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import RWhileAVSound

------------------------------------------------------------------------
-- Symbolic AV evaluation of a Code expression (the SPEC-EXP-AV denotation):
-- evaluate over an AV for the input variable, using the sound AV algebra.

aeval : Code → AV → AV
aeval cVar        a = a
aeval (cVal v)    _ = S v
aeval (cHd c)     a = avHd   (aeval c a)
aeval (cTl c)     a = avTl   (aeval c a)
aeval (cCons x y) a = avCons (aeval x a) (aeval y a)
aeval (cEq x y)   a = avEq   (aeval x a) (aeval y a)
aeval (cPairp c)  a = avPairp (aeval c a)

-- SOUNDNESS of the symbolic evaluator: concretising the symbolic result equals
-- running the program on the concretised input.  (Induction on c, each step a
-- single AV-operation soundness lemma from RWhileAVSound.)
aeval-sound : ∀ c a ρ → γ (aeval c a) ρ ≡ ⟦ c ⟧c (γ a ρ)
aeval-sound cVar        a ρ = refl
aeval-sound (cVal v)    a ρ = refl
aeval-sound (cHd c)     a ρ = trans (avHd-sound (aeval c a) ρ)  (cong hd (aeval-sound c a ρ))
aeval-sound (cTl c)     a ρ = trans (avTl-sound (aeval c a) ρ)  (cong tl (aeval-sound c a ρ))
aeval-sound (cCons x y) a ρ = trans (avCons-sound (aeval x a) (aeval y a) ρ)
                                    (cong₂ _·_ (aeval-sound x a ρ) (aeval-sound y a ρ))
aeval-sound (cEq x y)   a ρ = trans (avEq-sound (aeval x a) (aeval y a) ρ)
                                    (cong₂ veq (aeval-sound x a ρ) (aeval-sound y a ρ))
aeval-sound (cPairp c)  a ρ = trans (avPairp-sound (aeval c a) ρ) (cong pairp (aeval-sound c a ρ))

------------------------------------------------------------------------
-- The AV residualiser with binding-time split: head static, tail dynamic.

spec : Code → Val → Code
spec p s = lift (aeval p (C (S s) (D cVar)))

-- H1 (spec-correct, = fp1): the residual run on d equals p run on ⟨s,d⟩ = s · d.
-- γ (C (S s) (D cVar)) d  reduces to  s · d, so aeval-sound gives exactly this.
spec-correct : ∀ p s d → ⟦ spec p s ⟧c d ≡ ⟦ p ⟧c (s · d)
spec-correct p s d =
  trans (lift-sound (aeval p (C (S s) (D cVar))) d)
        (aeval-sound p (C (S s) (D cVar)) d)

------------------------------------------------------------------------
-- The dynamic tail is genuinely USED: the residual is a function of d (no
-- over-static degeneration).  E.g. specialising the projection `cTl cVar`
-- (return the dynamic half) yields a residual equal to the identity on d.

residual-uses-input : ∀ s d → ⟦ spec (cTl cVar) s ⟧c d ≡ d
residual-uses-input s d = spec-correct (cTl cVar) s d
