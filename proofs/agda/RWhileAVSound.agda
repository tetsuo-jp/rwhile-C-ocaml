{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Soundness of spec_av's ANNOTATED-VALUE (AV) algebra (gap G1, step N2).
--
-- spec_av specialises by symbolically evaluating the interpreter over
-- *annotated values*: ('S v) static, ('D code) dynamic, ('C a b) partially
-- static cons.  Its core AV operations are the macros AV-HD / AV-TL / AV-CONS /
-- AV-EQ / AV-PAIRP / AV-LIFT (examples/spec_av.rwhile).  For specialisation to
-- be CORRECT (H1 `spec-correct` of RWhileFutamura2), every AV operation must
-- agree with the corresponding concrete operation under CONCRETISATION: filling
-- the dynamic holes with a runtime value ρ must commute with the operation.
--
-- Here we model the AV algebra and a residual-code language, define
-- concretisation `γ : AV → Val → Val` (ρ = the runtime dynamic input) and the
-- residual semantics `⟦_⟧c`, and prove each AV operation SOUND:
--
--     γ (avHd a)      ρ ≡ hd    (γ a ρ)
--     γ (avTl a)      ρ ≡ tl    (γ a ρ)
--     γ (avCons a b)  ρ ≡ cons  (γ a ρ) (γ b ρ)
--     γ (avPairp a)   ρ ≡ pairp (γ a ρ)
--     γ (avEq a b)    ρ ≡ veq   (γ a ρ) (γ b ρ)
--     ⟦ lift a ⟧c     ρ ≡ γ a ρ                      (AV-LIFT preserves meaning)
--
-- These are the congruences that make the AV symbolic evaluator semantics-
-- preserving — the machine-checked core of "spec_av specialises correctly",
-- connecting the real AV machinery to the H1 hypothesis of the modular
-- Futamura hierarchy (RWhileFutamura2).  `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileAVSound where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

------------------------------------------------------------------------
-- Values (binary trees; nil = ⟨⟩, cons = _·_).  Atoms encode as trees.

data Val : Set where
  ⟨⟩  : Val
  _·_ : Val → Val → Val

vtrue : Val
vtrue = ⟨⟩ · ⟨⟩

vfalse : Val
vfalse = ⟨⟩

-- concrete operations (hd/tl total with nil default, matching how the residual
-- evaluates; pairp = cons-test; veq = structural equality returning a bool-val).
hd : Val → Val
hd (a · _) = a
hd ⟨⟩      = ⟨⟩

tl : Val → Val
tl (_ · b) = b
tl ⟨⟩      = ⟨⟩

pairp : Val → Val
pairp (_ · _) = vtrue
pairp ⟨⟩      = vfalse

vand : Val → Val → Val
vand (_ · _) y = y          -- first true  → second
vand ⟨⟩      _ = vfalse     -- first false → false

veq : Val → Val → Val
veq ⟨⟩      ⟨⟩      = vtrue
veq ⟨⟩      (_ · _) = vfalse
veq (_ · _) ⟨⟩      = vfalse
veq (a · b) (c · d) = vand (veq a c) (veq b d)

------------------------------------------------------------------------
-- Residual code: expressions over a single dynamic input `cVar` (= ρ).

data Code : Set where
  cVar   : Code
  cVal   : Val → Code
  cHd    : Code → Code
  cTl    : Code → Code
  cCons  : Code → Code → Code
  cEq    : Code → Code → Code
  cPairp : Code → Code

⟦_⟧c : Code → Val → Val
⟦ cVar      ⟧c ρ = ρ
⟦ cVal v    ⟧c ρ = v
⟦ cHd c     ⟧c ρ = hd (⟦ c ⟧c ρ)
⟦ cTl c     ⟧c ρ = tl (⟦ c ⟧c ρ)
⟦ cCons a b ⟧c ρ = (⟦ a ⟧c ρ) · (⟦ b ⟧c ρ)
⟦ cEq a b   ⟧c ρ = veq (⟦ a ⟧c ρ) (⟦ b ⟧c ρ)
⟦ cPairp c  ⟧c ρ = pairp (⟦ c ⟧c ρ)

------------------------------------------------------------------------
-- Annotated values and concretisation γ (fill dynamic holes with ρ).

data AV : Set where
  S : Val → AV            -- static
  D : Code → AV           -- dynamic (residual code)
  C : AV → AV → AV        -- partially static cons

γ : AV → Val → Val
γ (S v)   ρ = v
γ (D c)   ρ = ⟦ c ⟧c ρ
γ (C a b) ρ = (γ a ρ) · (γ b ρ)

------------------------------------------------------------------------
-- AV-LIFT (spec_av: AV-LIFT/AV-LIFT-STEP): lower an AV to residual code,
-- preserving meaning.

lift : AV → Code
lift (S v)   = cVal v
lift (D c)   = c
lift (C a b) = cCons (lift a) (lift b)

lift-sound : ∀ a ρ → ⟦ lift a ⟧c ρ ≡ γ a ρ
lift-sound (S v)   ρ = refl
lift-sound (D c)   ρ = refl
lift-sound (C a b) ρ = cong₂ _·_ (lift-sound a ρ) (lift-sound b ρ)

------------------------------------------------------------------------
-- AV-HD (spec_av macro AV-HD): static→take head; partial-cons→left; dynamic→residual hd.

avHd : AV → AV
avHd (S v)   = S (hd v)
avHd (C a _) = a
avHd (D c)   = D (cHd c)

avHd-sound : ∀ a ρ → γ (avHd a) ρ ≡ hd (γ a ρ)
avHd-sound (S v)   ρ = refl
avHd-sound (C a b) ρ = refl
avHd-sound (D c)   ρ = refl

------------------------------------------------------------------------
-- AV-TL (spec_av macro AV-TL).

avTl : AV → AV
avTl (S v)   = S (tl v)
avTl (C _ b) = b
avTl (D c)   = D (cTl c)

avTl-sound : ∀ a ρ → γ (avTl a) ρ ≡ tl (γ a ρ)
avTl-sound (S v)   ρ = refl
avTl-sound (C a b) ρ = refl
avTl-sound (D c)   ρ = refl

------------------------------------------------------------------------
-- AV-CONS (spec_av macro AV-CONS): both static→static cons; else partial-cons.

avCons : AV → AV → AV
avCons (S v1) (S v2) = S (v1 · v2)
avCons (S x)  (D y)  = C (S x) (D y)
avCons (S x)  (C y z) = C (S x) (C y z)
avCons (D x)  b      = C (D x) b
avCons (C x y) b     = C (C x y) b

avCons-sound : ∀ a b ρ → γ (avCons a b) ρ ≡ (γ a ρ) · (γ b ρ)
avCons-sound (S v1)  (S v2)  ρ = refl
avCons-sound (S x)   (D y)   ρ = refl
avCons-sound (S x)   (C y z) ρ = refl
avCons-sound (D x)   b       ρ = refl
avCons-sound (C x y) b       ρ = refl

------------------------------------------------------------------------
-- AV-PAIRP (spec_av macro AV-PAIRP): static→known bool; partial-cons→TRUE; dynamic→residual.

avPairp : AV → AV
avPairp (S v)   = S (pairp v)
avPairp (C _ _) = S vtrue
avPairp (D c)   = D (cPairp c)

avPairp-sound : ∀ a ρ → γ (avPairp a) ρ ≡ pairp (γ a ρ)
avPairp-sound (S v)   ρ = refl
avPairp-sound (C a b) ρ = refl
avPairp-sound (D c)   ρ = refl

------------------------------------------------------------------------
-- AV-EQ (spec_av macro AV-EQ): both static→known bool; else lift both, residual eq.

avEq : AV → AV → AV
avEq (S v1)  (S v2)  = S (veq v1 v2)
avEq (S x)   (D y)   = D (cEq (lift (S x)) (lift (D y)))
avEq (S x)   (C y z) = D (cEq (lift (S x)) (lift (C y z)))
avEq (D x)   b       = D (cEq (lift (D x)) (lift b))
avEq (C x y) b       = D (cEq (lift (C x y)) (lift b))

avEq-sound : ∀ a b ρ → γ (avEq a b) ρ ≡ veq (γ a ρ) (γ b ρ)
avEq-sound (S v1)  (S v2)  ρ = refl
avEq-sound (S x)   (D y)   ρ = cong₂ veq (lift-sound (S x) ρ)   (lift-sound (D y) ρ)
avEq-sound (S x)   (C y z) ρ = cong₂ veq (lift-sound (S x) ρ)   (lift-sound (C y z) ρ)
avEq-sound (D x)   b       ρ = cong₂ veq (lift-sound (D x) ρ)   (lift-sound b ρ)
avEq-sound (C x y) b       ρ = cong₂ veq (lift-sound (C x y) ρ) (lift-sound b ρ)
