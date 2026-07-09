{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 7: DISPATCH preservation (closes the stage-6 caveat).
--
-- Stage 6 proved the BT-driven fix removes the over-static `('val.'swap)` embed and is
-- fp1-safe, but not that the fixed compiler DISPATCHES correctly.  The production
-- symptom is precisely a lost dispatch: `[comp2]('S.swap)` embeds the opcode instead
-- of selecting ri_min's swap branch.  Here we add an opcode dispatch to the two-stage
-- model and prove the fix restores it.
--
-- The interpreter fragment gains equality (`eEq`) and conditional (`eIf`), so it can
-- branch on the stage-2 source (the opcode), exactly like ri_min's `=? Op 'swap`.
-- The AV specialiser gains `avEq2` / `avIf2` (mirroring the production AV-EQ and the
-- 'cond handler): a STATIC test resolves the branch at specialise time; a DYNAMIC test
-- RESIDUALISES the conditional (`kIf`).
--
-- We prove:
--   * `spec1-sound` still holds WITH dispatch — so the correct compiler (source kept
--     symbolic) is correct for EVERY opcode: it genuinely dispatches (`comp-swap` gives
--     the swap result, `comp-id` the id result — different outputs).
--   * `compbug-ignores-opcode` / `compbug-wrong` — freezing the opcode (the :1111-style
--     over-static) collapses the dispatch to ONE branch, so the "compiler" ignores its
--     opcode argument and is WRONG (the exact comp2 failure).
------------------------------------------------------------------------
module RWhileOfflineBTA7 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; vfalse; hd; tl; veq; vand)

------------------------------------------------------------------------
-- if-on-a-value (truth = non-nil), matching R-WHILE's `is_true`.

ifV : Val → Val → Val → Val
ifV ⟨⟩      t e = e
ifV (_ · _) t e = t

------------------------------------------------------------------------
-- Two-hole residual with equality + conditional.  kS = stage-2 source (opcode), kD = runtime.

data Code2 : Set where
  kVal  : Val → Code2
  kS    : Code2
  kD    : Code2
  kHd   : Code2 → Code2
  kTl   : Code2 → Code2
  kCons : Code2 → Code2 → Code2
  kEq   : Code2 → Code2 → Code2
  kIf   : Code2 → Code2 → Code2 → Code2

⟦_⟧2 : Code2 → Val → Val → Val      -- ⟦ c ⟧2 s2 d
⟦ kVal v    ⟧2 s d = v
⟦ kS        ⟧2 s d = s
⟦ kD        ⟧2 s d = d
⟦ kHd c     ⟧2 s d = hd (⟦ c ⟧2 s d)
⟦ kTl c     ⟧2 s d = tl (⟦ c ⟧2 s d)
⟦ kCons a b ⟧2 s d = ⟦ a ⟧2 s d · ⟦ b ⟧2 s d
⟦ kEq a b   ⟧2 s d = veq (⟦ a ⟧2 s d) (⟦ b ⟧2 s d)
⟦ kIf t a b ⟧2 s d = ifV (⟦ t ⟧2 s d) (⟦ a ⟧2 s d) (⟦ b ⟧2 s d)

------------------------------------------------------------------------
-- Stage-1 AV.

data AV2 : Set where
  S2 : Val → AV2
  D2 : Code2 → AV2
  C2 : AV2 → AV2 → AV2

γ2 : AV2 → Val → Val → Val
γ2 (S2 v)   s d = v
γ2 (D2 c)   s d = ⟦ c ⟧2 s d
γ2 (C2 a b) s d = γ2 a s d · γ2 b s d

lift2 : AV2 → Code2
lift2 (S2 v)   = kVal v
lift2 (D2 c)   = c
lift2 (C2 a b) = kCons (lift2 a) (lift2 b)

lift2-sound : ∀ a s d → ⟦ lift2 a ⟧2 s d ≡ γ2 a s d
lift2-sound (S2 v)   s d = refl
lift2-sound (D2 c)   s d = refl
lift2-sound (C2 a b) s d = cong₂ _·_ (lift2-sound a s d) (lift2-sound b s d)

avHd2 : AV2 → AV2
avHd2 (S2 v)   = S2 (hd v)
avHd2 (C2 a _) = a
avHd2 (D2 c)   = D2 (kHd c)

avHd2-sound : ∀ a s d → γ2 (avHd2 a) s d ≡ hd (γ2 a s d)
avHd2-sound (S2 v)   s d = refl
avHd2-sound (C2 a b) s d = refl
avHd2-sound (D2 c)   s d = refl

avTl2 : AV2 → AV2
avTl2 (S2 v)   = S2 (tl v)
avTl2 (C2 _ b) = b
avTl2 (D2 c)   = D2 (kTl c)

avTl2-sound : ∀ a s d → γ2 (avTl2 a) s d ≡ tl (γ2 a s d)
avTl2-sound (S2 v)   s d = refl
avTl2-sound (C2 a b) s d = refl
avTl2-sound (D2 c)   s d = refl

avCons2 : AV2 → AV2 → AV2
avCons2 (S2 v1)  (S2 v2)  = S2 (v1 · v2)
avCons2 (S2 x)   (D2 y)   = C2 (S2 x) (D2 y)
avCons2 (S2 x)   (C2 y z) = C2 (S2 x) (C2 y z)
avCons2 (D2 x)   b        = C2 (D2 x) b
avCons2 (C2 x y) b        = C2 (C2 x y) b

avCons2-sound : ∀ a b s d → γ2 (avCons2 a b) s d ≡ γ2 a s d · γ2 b s d
avCons2-sound (S2 v1)  (S2 v2)  s d = refl
avCons2-sound (S2 x)   (D2 y)   s d = refl
avCons2-sound (S2 x)   (C2 y z) s d = refl
avCons2-sound (D2 x)   b        s d = refl
avCons2-sound (C2 x y) b        s d = refl

-- AV-EQ (production AV-EQ:224): both-static → static bool; else residual `=?`.
avEq2 : AV2 → AV2 → AV2
avEq2 (S2 v1) (S2 v2) = S2 (veq v1 v2)
avEq2 a       b       = D2 (kEq (lift2 a) (lift2 b))

avEq2-sound : ∀ a b s d → γ2 (avEq2 a b) s d ≡ veq (γ2 a s d) (γ2 b s d)
avEq2-sound (S2 v1) (S2 v2) s d = refl
avEq2-sound (S2 v1) (D2 y)  s d = cong₂ veq (lift2-sound (S2 v1) s d) (lift2-sound (D2 y) s d)
avEq2-sound (S2 v1) (C2 y z) s d = cong₂ veq (lift2-sound (S2 v1) s d) (lift2-sound (C2 y z) s d)
avEq2-sound (D2 x)  b       s d = cong₂ veq (lift2-sound (D2 x) s d) (lift2-sound b s d)
avEq2-sound (C2 x y) b      s d = cong₂ veq (lift2-sound (C2 x y) s d) (lift2-sound b s d)

-- AV conditional (production 'cond handler): static test → pick branch at spec time;
-- dynamic test → residualise the whole conditional.
ifAV : Val → AV2 → AV2 → AV2
ifAV ⟨⟩      t e = e
ifAV (_ · _) t e = t

avIf2 : AV2 → AV2 → AV2 → AV2
avIf2 (S2 b) t e = ifAV b t e
avIf2 a      t e = D2 (kIf (lift2 a) (lift2 t) (lift2 e))

ifV-cong : ∀ {a a′ t t′ e e′} → a ≡ a′ → t ≡ t′ → e ≡ e′ → ifV a t e ≡ ifV a′ t′ e′
ifV-cong refl refl refl = refl

avIf2-sound : ∀ a t e s d → γ2 (avIf2 a t e) s d ≡ ifV (γ2 a s d) (γ2 t s d) (γ2 e s d)
avIf2-sound (S2 ⟨⟩)      t e s d = refl
avIf2-sound (S2 (x · y)) t e s d = refl
avIf2-sound (D2 c)       t e s d =
  ifV-cong (lift2-sound (D2 c) s d) (lift2-sound t s d) (lift2-sound e s d)
avIf2-sound (C2 a b)     t e s d =
  ifV-cong (lift2-sound (C2 a b) s d) (lift2-sound t s d) (lift2-sound e s d)

------------------------------------------------------------------------
-- Interpreter fragment with dispatch (three inputs s1,s2,d).

data Exp2 : Set where
  x1    : Exp2
  x2    : Exp2
  xd    : Exp2
  kK    : Val → Exp2
  hHd   : Exp2 → Exp2
  hTl   : Exp2 → Exp2
  hCons : Exp2 → Exp2 → Exp2
  eEq   : Exp2 → Exp2 → Exp2
  eIf   : Exp2 → Exp2 → Exp2 → Exp2

evalE2 : Exp2 → Val → Val → Val → Val
evalE2 x1         s1 s2 d = s1
evalE2 x2         s1 s2 d = s2
evalE2 xd         s1 s2 d = d
evalE2 (kK v)     s1 s2 d = v
evalE2 (hHd e)    s1 s2 d = hd (evalE2 e s1 s2 d)
evalE2 (hTl e)    s1 s2 d = tl (evalE2 e s1 s2 d)
evalE2 (hCons a b) s1 s2 d = evalE2 a s1 s2 d · evalE2 b s1 s2 d
evalE2 (eEq a b)  s1 s2 d = veq (evalE2 a s1 s2 d) (evalE2 b s1 s2 d)
evalE2 (eIf t a b) s1 s2 d = ifV (evalE2 t s1 s2 d) (evalE2 a s1 s2 d) (evalE2 b s1 s2 d)

------------------------------------------------------------------------
-- STAGE 1 (build comp): x1 → known; x2 → residualise (kS, symbolic); xd → kD.

spec1 : Exp2 → Val → AV2
spec1 x1         s1 = S2 s1
spec1 x2         s1 = D2 kS
spec1 xd         s1 = D2 kD
spec1 (kK v)     s1 = S2 v
spec1 (hHd e)    s1 = avHd2 (spec1 e s1)
spec1 (hTl e)    s1 = avTl2 (spec1 e s1)
spec1 (hCons a b) s1 = avCons2 (spec1 a s1) (spec1 b s1)
spec1 (eEq a b)  s1 = avEq2 (spec1 a s1) (spec1 b s1)
spec1 (eIf t a b) s1 = avIf2 (spec1 t s1) (spec1 a s1) (spec1 b s1)

spec1-sound : ∀ e s1 s2 d → γ2 (spec1 e s1) s2 d ≡ evalE2 e s1 s2 d
spec1-sound x1         s1 s2 d = refl
spec1-sound x2         s1 s2 d = refl
spec1-sound xd         s1 s2 d = refl
spec1-sound (kK v)     s1 s2 d = refl
spec1-sound (hHd e)    s1 s2 d =
  trans (avHd2-sound (spec1 e s1) s2 d) (cong hd (spec1-sound e s1 s2 d))
spec1-sound (hTl e)    s1 s2 d =
  trans (avTl2-sound (spec1 e s1) s2 d) (cong tl (spec1-sound e s1 s2 d))
spec1-sound (hCons a b) s1 s2 d =
  trans (avCons2-sound (spec1 a s1) (spec1 b s1) s2 d)
        (cong₂ _·_ (spec1-sound a s1 s2 d) (spec1-sound b s1 s2 d))
spec1-sound (eEq a b)  s1 s2 d =
  trans (avEq2-sound (spec1 a s1) (spec1 b s1) s2 d)
        (cong₂ veq (spec1-sound a s1 s2 d) (spec1-sound b s1 s2 d))
spec1-sound (eIf t a b) s1 s2 d =
  trans (avIf2-sound (spec1 t s1) (spec1 a s1) (spec1 b s1) s2 d)
        (ifV-cong (spec1-sound t s1 s2 d) (spec1-sound a s1 s2 d) (spec1-sound b s1 s2 d))

------------------------------------------------------------------------
-- COMPILE: fill the source hole kS with the concrete opcode s2.

substS : Code2 → Val → Code2
substS (kVal v)   s2 = kVal v
substS kS         s2 = kVal s2
substS kD         s2 = kD
substS (kHd c)    s2 = kHd (substS c s2)
substS (kTl c)    s2 = kTl (substS c s2)
substS (kCons a b) s2 = kCons (substS a s2) (substS b s2)
substS (kEq a b)  s2 = kEq (substS a s2) (substS b s2)
substS (kIf t a b) s2 = kIf (substS t s2) (substS a s2) (substS b s2)

substS-sound : ∀ c s2 s′ d → ⟦ substS c s2 ⟧2 s′ d ≡ ⟦ c ⟧2 s2 d
substS-sound (kVal v)   s2 s′ d = refl
substS-sound kS         s2 s′ d = refl
substS-sound kD         s2 s′ d = refl
substS-sound (kHd c)    s2 s′ d = cong hd (substS-sound c s2 s′ d)
substS-sound (kTl c)    s2 s′ d = cong tl (substS-sound c s2 s′ d)
substS-sound (kCons a b) s2 s′ d = cong₂ _·_ (substS-sound a s2 s′ d) (substS-sound b s2 s′ d)
substS-sound (kEq a b)  s2 s′ d = cong₂ veq (substS-sound a s2 s′ d) (substS-sound b s2 s′ d)
substS-sound (kIf t a b) s2 s′ d =
  ifV-cong (substS-sound t s2 s′ d) (substS-sound a s2 s′ d) (substS-sound b s2 s′ d)

compile : AV2 → Val → AV2
compile (S2 v)   s2 = S2 v
compile (D2 c)   s2 = D2 (substS c s2)
compile (C2 a b) s2 = C2 (compile a s2) (compile b s2)

compile-sound : ∀ a s2 s′ d → γ2 (compile a s2) s′ d ≡ γ2 a s2 d
compile-sound (S2 v)   s2 s′ d = refl
compile-sound (D2 c)   s2 s′ d = substS-sound c s2 s′ d
compile-sound (C2 a b) s2 s′ d = cong₂ _·_ (compile-sound a s2 s′ d) (compile-sound b s2 s′ d)

fp2-eq : ∀ e s1 s2 s′ d → γ2 (compile (spec1 e s1) s2) s′ d ≡ evalE2 e s1 s2 d
fp2-eq e s1 s2 s′ d =
  trans (compile-sound (spec1 e s1) s2 s′ d) (spec1-sound e s1 s2 d)

------------------------------------------------------------------------
-- A ri_min-like DISPATCH on the opcode x2: `if x2 = 'swap then (d.d) else d`.
-- Opcodes as concrete values: 'swap = vtrue, 'id = ⟨⟩ (so veq computes definitionally).

dispatchExpr : Exp2
dispatchExpr = eIf (eEq x2 (kK vtrue)) (hCons xd xd) xd

-- The CORRECT compiler (source kept symbolic) dispatches: different opcodes → different
-- results, each correct.  (Instances of fp2-eq; the concrete evals reduce definitionally.)
comp-swap : ∀ s1 s′ d → γ2 (compile (spec1 dispatchExpr s1) vtrue) s′ d ≡ (d · d)
comp-swap s1 s′ d = fp2-eq dispatchExpr s1 vtrue s′ d

comp-id : ∀ s1 s′ d → γ2 (compile (spec1 dispatchExpr s1) ⟨⟩) s′ d ≡ d
comp-id s1 s′ d = fp2-eq dispatchExpr s1 ⟨⟩ s′ d

------------------------------------------------------------------------
-- The OVER-STATIC bug: freeze the opcode x2 at stage 1 (:1111-style).  avEq2 then
-- resolves the test statically, avIf2 picks ONE branch — the dispatch is GONE and the
-- "compiler" ignores its opcode argument.

spec1bug : Exp2 → Val → AV2
spec1bug x1         s1 = S2 s1
spec1bug x2         s1 = S2 ⟨⟩        -- BUG: freeze the opcode to a static value
spec1bug xd         s1 = D2 kD
spec1bug (kK v)     s1 = S2 v
spec1bug (hHd e)    s1 = avHd2 (spec1bug e s1)
spec1bug (hTl e)    s1 = avTl2 (spec1bug e s1)
spec1bug (hCons a b) s1 = avCons2 (spec1bug a s1) (spec1bug b s1)
spec1bug (eEq a b)  s1 = avEq2 (spec1bug a s1) (spec1bug b s1)
spec1bug (eIf t a b) s1 = avIf2 (spec1bug t s1) (spec1bug a s1) (spec1bug b s1)

⟨⟩≢vtrue : ⟨⟩ ≡ vtrue → ⊥
⟨⟩≢vtrue ()

-- The frozen compiler yields the SAME result for the swap opcode as for anything —
-- it collapsed to the else-branch `d`, ignoring the opcode.
compbug-ignores-opcode : ∀ s1 s2 s′ d → γ2 (compile (spec1bug dispatchExpr s1) s2) s′ d ≡ d
compbug-ignores-opcode s1 s2 s′ d = compile-sound (spec1bug dispatchExpr s1) s2 s′ d

-- ...so it is WRONG at the swap opcode (correct = (d·d), frozen = d).
-- ...so it is WRONG at the swap opcode: the frozen compiler gives ⟨⟩ (the else-branch),
-- while the correct result is (⟨⟩·⟨⟩)=vtrue.  At d=⟨⟩ the γ2 term reduces to ⟨⟩, so hyp
-- forces ⟨⟩ ≡ vtrue.
compbug-wrong :
  ¬ (∀ s1 s′ d → γ2 (compile (spec1bug dispatchExpr s1) vtrue) s′ d ≡ evalE2 dispatchExpr s1 vtrue d)
compbug-wrong hyp = ⟨⟩≢vtrue (hyp ⟨⟩ ⟨⟩ ⟨⟩)
