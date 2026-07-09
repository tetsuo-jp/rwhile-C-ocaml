{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 4: the actual TWO-STAGE comp2 (the fp2 compiler).
--
-- Continues RWhileOfflineBTA/2/3.  fp2 = [spec]((spec . int)) yields a COMPILER
-- `comp`: [comp](s2) = target, [target](d) = ⟦int⟧(s1,s2,d).  There are THREE
-- binding times: the stage-1 static part s1 (the interpreter, known when we build
-- comp), the stage-2 source s2 (known when we COMPILE, symbolic while building comp),
-- and the runtime input d.  The over-static bug freezes s2 at stage 1.
--
-- We model this directly with a TWO-HOLE residual (`Code2`: holes kS = stage-2 source,
-- kD = runtime) and a stage-1 AV (`AV2`).  We prove:
--
--   * `spec1-sound`  — comp (the stage-1 residual) is a correct compiler as a whole:
--                      γ2 (spec1 e s1) s2 d ≡ ⟦e⟧(s1,s2,d).
--   * `compile-sound`+`fp2-eq` — COMPILE (instantiate the s2 hole) then RUN over d
--                      equals direct evaluation: the Futamura fp2 equation.  The
--                      target no longer depends on s2 (the hole is gone).
--   * `spec1-keeps-source-symbolic` — the correct comp keeps s2 SYMBOLIC (a kS hole),
--                      i.e. it is a genuine non-trivial compiler, not a frozen constant.
--   * `spec1bug-wrong-on-source` — freezing s2 at stage 1 is UNSOUND (the over-static
--                      bug): the "compiler" ignores its source argument.
--   * `gain` — stage-1-static (s1/const-only) parts fully collapse at stage 1.
------------------------------------------------------------------------
module RWhileOfflineBTA4 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; hd; tl)

------------------------------------------------------------------------
-- Two-hole residual code:  kS = stage-2 source hole, kD = runtime hole.

data Code2 : Set where
  kVal  : Val → Code2
  kS    : Code2
  kD    : Code2
  kHd   : Code2 → Code2
  kTl   : Code2 → Code2
  kCons : Code2 → Code2 → Code2

⟦_⟧2 : Code2 → Val → Val → Val      -- ⟦ c ⟧2 s2 d
⟦ kVal v   ⟧2 s d = v
⟦ kS       ⟧2 s d = s
⟦ kD       ⟧2 s d = d
⟦ kHd c    ⟧2 s d = hd (⟦ c ⟧2 s d)
⟦ kTl c    ⟧2 s d = tl (⟦ c ⟧2 s d)
⟦ kCons a b ⟧2 s d = ⟦ a ⟧2 s d · ⟦ b ⟧2 s d

------------------------------------------------------------------------
-- Stage-1 annotated value:  S2 known at stage 1; D2 residual over (s2,d); C2 partial.

data AV2 : Set where
  S2 : Val → AV2
  D2 : Code2 → AV2
  C2 : AV2 → AV2 → AV2

γ2 : AV2 → Val → Val → Val          -- γ2 a s2 d
γ2 (S2 v)   s d = v
γ2 (D2 c)   s d = ⟦ c ⟧2 s d
γ2 (C2 a b) s d = γ2 a s d · γ2 b s d

-- AV2 operations (mirror RWhileAVSound's avHd/avTl/avCons, two-hole version).
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

------------------------------------------------------------------------
-- Interpreter-like expression over THREE inputs: s1 (stage-1), s2 (stage-2), d (runtime).

data Exp2 : Set where
  x1    : Exp2                 -- stage-1 source (e.g. the interpreter part)
  x2    : Exp2                 -- stage-2 source (the program being compiled)
  xd    : Exp2                 -- runtime input
  kK    : Val → Exp2
  hHd   : Exp2 → Exp2
  hTl   : Exp2 → Exp2
  hCons : Exp2 → Exp2 → Exp2

evalE2 : Exp2 → Val → Val → Val → Val   -- evalE2 e s1 s2 d
evalE2 x1         s1 s2 d = s1
evalE2 x2         s1 s2 d = s2
evalE2 xd         s1 s2 d = d
evalE2 (kK v)     s1 s2 d = v
evalE2 (hHd e)    s1 s2 d = hd (evalE2 e s1 s2 d)
evalE2 (hTl e)    s1 s2 d = tl (evalE2 e s1 s2 d)
evalE2 (hCons a b) s1 s2 d = evalE2 a s1 s2 d · evalE2 b s1 s2 d

------------------------------------------------------------------------
-- STAGE 1 (build the compiler `comp`): specialise w.r.t. s1 only.  x1 → known value;
-- x2 → RESIDUALISE as the stage-2 source hole kS (symbolic here, NOT frozen); xd → kD.

spec1 : Exp2 → Val → AV2
spec1 x1         s1 = S2 s1
spec1 x2         s1 = D2 kS          -- keep the stage-2 source symbolic
spec1 xd         s1 = D2 kD
spec1 (kK v)     s1 = S2 v
spec1 (hHd e)    s1 = avHd2 (spec1 e s1)
spec1 (hTl e)    s1 = avTl2 (spec1 e s1)
spec1 (hCons a b) s1 = avCons2 (spec1 a s1) (spec1 b s1)

-- comp is a correct compiler as a whole: concretising at (s2,d) = evaluating.
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

------------------------------------------------------------------------
-- COMPILE ([comp](s2)): instantiate the stage-2 source hole kS with the concrete
-- source value s2, leaving a residual over the runtime hole kD only (= target).

substS : Code2 → Val → Code2
substS (kVal v)   s2 = kVal v
substS kS         s2 = kVal s2      -- the source hole is filled at compile time
substS kD         s2 = kD
substS (kHd c)    s2 = kHd (substS c s2)
substS (kTl c)    s2 = kTl (substS c s2)
substS (kCons a b) s2 = kCons (substS a s2) (substS b s2)

substS-sound : ∀ c s2 s′ d → ⟦ substS c s2 ⟧2 s′ d ≡ ⟦ c ⟧2 s2 d
substS-sound (kVal v)   s2 s′ d = refl
substS-sound kS         s2 s′ d = refl
substS-sound kD         s2 s′ d = refl
substS-sound (kHd c)    s2 s′ d = cong hd (substS-sound c s2 s′ d)
substS-sound (kTl c)    s2 s′ d = cong tl (substS-sound c s2 s′ d)
substS-sound (kCons a b) s2 s′ d = cong₂ _·_ (substS-sound a s2 s′ d) (substS-sound b s2 s′ d)

compile : AV2 → Val → AV2
compile (S2 v)   s2 = S2 v
compile (D2 c)   s2 = D2 (substS c s2)
compile (C2 a b) s2 = C2 (compile a s2) (compile b s2)

-- The target no longer depends on the stage-2 source (s′ is arbitrary and unused).
compile-sound : ∀ a s2 s′ d → γ2 (compile a s2) s′ d ≡ γ2 a s2 d
compile-sound (S2 v)   s2 s′ d = refl
compile-sound (D2 c)   s2 s′ d = substS-sound c s2 s′ d
compile-sound (C2 a b) s2 s′ d = cong₂ _·_ (compile-sound a s2 s′ d) (compile-sound b s2 s′ d)

------------------------------------------------------------------------
-- THE FUTAMURA fp2 EQUATION: compile (comp at s2) then run over d = direct evaluation.

fp2-eq : ∀ e s1 s2 s′ d → γ2 (compile (spec1 e s1) s2) s′ d ≡ evalE2 e s1 s2 d
fp2-eq e s1 s2 s′ d =
  trans (compile-sound (spec1 e s1) s2 s′ d) (spec1-sound e s1 s2 d)

------------------------------------------------------------------------
-- Non-triviality: the correct comp keeps the stage-2 source symbolic — reading x2
-- residualises to the kS hole, so comp genuinely consumes its source argument.

spec1-keeps-source-symbolic : ∀ s1 → spec1 x2 s1 ≡ D2 kS
spec1-keeps-source-symbolic s1 = refl

------------------------------------------------------------------------
-- The OVER-STATIC bug: freeze the stage-2 source at stage 1 (as spec_av.rwhile:1051's
-- unconditional 'S does).  Only x2 differs; the resulting "compiler" ignores its source.

spec1bug : Exp2 → Val → AV2
spec1bug x1         s1 = S2 s1
spec1bug x2         s1 = S2 ⟨⟩       -- BUG: commit the stage-2 source to a static value
spec1bug xd         s1 = D2 kD
spec1bug (kK v)     s1 = S2 v
spec1bug (hHd e)    s1 = avHd2 (spec1bug e s1)
spec1bug (hTl e)    s1 = avTl2 (spec1bug e s1)
spec1bug (hCons a b) s1 = avCons2 (spec1bug a s1) (spec1bug b s1)

⟨⟩≢vtrue : ⟨⟩ ≡ vtrue → ⊥
⟨⟩≢vtrue ()

-- The frozen compiler is unsound: it does not compile its stage-2 source argument.
spec1bug-wrong-on-source :
  ∀ s1 → ¬ (∀ s2 d → γ2 (spec1bug x2 s1) s2 d ≡ evalE2 x2 s1 s2 d)
spec1bug-wrong-on-source s1 hyp = ⟨⟩≢vtrue (hyp vtrue ⟨⟩)

------------------------------------------------------------------------
-- GAIN: an expression using only the stage-1 source / constants collapses to a single
-- stage-1 value (all its work is done while building comp).

data stage1Static : Exp2 → Set where
  s1x1   : stage1Static x1
  s1K    : ∀ v → stage1Static (kK v)
  s1Hd   : ∀ {e} → stage1Static e → stage1Static (hHd e)
  s1Tl   : ∀ {e} → stage1Static e → stage1Static (hTl e)
  s1Cons : ∀ {a b} → stage1Static a → stage1Static b → stage1Static (hCons a b)

data isS2 : AV2 → Set where
  mkS2 : ∀ v → isS2 (S2 v)

avHd2-isS2 : ∀ {a} → isS2 a → isS2 (avHd2 a)
avHd2-isS2 (mkS2 v) = mkS2 (hd v)

avTl2-isS2 : ∀ {a} → isS2 a → isS2 (avTl2 a)
avTl2-isS2 (mkS2 v) = mkS2 (tl v)

avCons2-isS2 : ∀ {a b} → isS2 a → isS2 b → isS2 (avCons2 a b)
avCons2-isS2 (mkS2 v1) (mkS2 v2) = mkS2 (v1 · v2)

gain : ∀ {e} s1 → stage1Static e → isS2 (spec1 e s1)
gain s1 s1x1          = mkS2 s1
gain s1 (s1K v)       = mkS2 v
gain s1 (s1Hd st)     = avHd2-isS2 (gain s1 st)
gain s1 (s1Tl st)     = avTl2-isS2 (gain s1 st)
gain s1 (s1Cons sa sb) = avCons2-isS2 (gain s1 sa) (gain s1 sb)
