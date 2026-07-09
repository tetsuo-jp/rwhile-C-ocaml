{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 5: the THREE-stage cogen (the fp3 compiler generator).
--
-- Continues RWhileOfflineBTA/2/3/4.  fp3 = [spec]((spec . spec)) = cogen, a compiler
-- GENERATOR: [cogen](int) = comp, [comp](s2) = target, [target](d) = ⟦int⟧(s2,d).
-- Now the interpreter s1 is ALSO symbolic while cogen is built — so there are three
-- residualisable inputs: s1 (interpreter, known at GENERATE time), s2 (source, known
-- at COMPILE time) and d (runtime).  The over-static bug freezes s1 at cogen-build.
--
-- We model this with a THREE-hole residual (`Code3`: j1 = interpreter, j2 = source,
-- jd = runtime) and a stage-0 AV (`AV3`).  We prove:
--
--   * `gen-sound`  — cogen is correct as a whole: γ3 (gen e) s1 s2 d ≡ ⟦e⟧(s1,s2,d).
--   * `generate`/`compile` (hole instantiation) with soundness, culminating in
--     `fp3-eq`  — GENERATE (fill j1=int) then COMPILE (fill j2=s2) then run over d
--                 equals direct evaluation: the Futamura fp3 equation.
--   * `gen-keeps-int-symbolic` — the correct cogen keeps the interpreter symbolic
--                 (a j1 hole): it is a genuine generator, not a frozen constant.
--   * `genbug-wrong-on-int` — freezing the interpreter at cogen-build is UNSOUND.
--   * `gain` — constant/structural parts collapse at stage 0.
--
-- Reuses the interpreter semantics `evalE2`/`Exp2` of stage 4 (the same three-input
-- interpreter), so stages 4 and 5 share one notion of "what the program means".
------------------------------------------------------------------------
module RWhileOfflineBTA5 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; hd; tl)
open import RWhileOfflineBTA4
  using ( Exp2; x1; x2; xd; kK; hHd; hTl; hCons; evalE2 )

------------------------------------------------------------------------
-- Three-hole residual: j1 = interpreter (s1), j2 = source (s2), jd = runtime (d).

data Code3 : Set where
  jVal  : Val → Code3
  j1    : Code3
  j2    : Code3
  jd    : Code3
  jHd   : Code3 → Code3
  jTl   : Code3 → Code3
  jCons : Code3 → Code3 → Code3

⟦_⟧3 : Code3 → Val → Val → Val → Val      -- ⟦ c ⟧3 s1 s2 d
⟦ jVal v   ⟧3 s1 s2 d = v
⟦ j1       ⟧3 s1 s2 d = s1
⟦ j2       ⟧3 s1 s2 d = s2
⟦ jd       ⟧3 s1 s2 d = d
⟦ jHd c    ⟧3 s1 s2 d = hd (⟦ c ⟧3 s1 s2 d)
⟦ jTl c    ⟧3 s1 s2 d = tl (⟦ c ⟧3 s1 s2 d)
⟦ jCons a b ⟧3 s1 s2 d = ⟦ a ⟧3 s1 s2 d · ⟦ b ⟧3 s1 s2 d

------------------------------------------------------------------------
-- Stage-0 annotated value and its concretisation.

data AV3 : Set where
  S3 : Val → AV3
  D3 : Code3 → AV3
  C3 : AV3 → AV3 → AV3

γ3 : AV3 → Val → Val → Val → Val          -- γ3 a s1 s2 d
γ3 (S3 v)   s1 s2 d = v
γ3 (D3 c)   s1 s2 d = ⟦ c ⟧3 s1 s2 d
γ3 (C3 a b) s1 s2 d = γ3 a s1 s2 d · γ3 b s1 s2 d

avHd3 : AV3 → AV3
avHd3 (S3 v)   = S3 (hd v)
avHd3 (C3 a _) = a
avHd3 (D3 c)   = D3 (jHd c)

avHd3-sound : ∀ a s1 s2 d → γ3 (avHd3 a) s1 s2 d ≡ hd (γ3 a s1 s2 d)
avHd3-sound (S3 v)   s1 s2 d = refl
avHd3-sound (C3 a b) s1 s2 d = refl
avHd3-sound (D3 c)   s1 s2 d = refl

avTl3 : AV3 → AV3
avTl3 (S3 v)   = S3 (tl v)
avTl3 (C3 _ b) = b
avTl3 (D3 c)   = D3 (jTl c)

avTl3-sound : ∀ a s1 s2 d → γ3 (avTl3 a) s1 s2 d ≡ tl (γ3 a s1 s2 d)
avTl3-sound (S3 v)   s1 s2 d = refl
avTl3-sound (C3 a b) s1 s2 d = refl
avTl3-sound (D3 c)   s1 s2 d = refl

avCons3 : AV3 → AV3 → AV3
avCons3 (S3 v1)  (S3 v2)  = S3 (v1 · v2)
avCons3 (S3 x)   (D3 y)   = C3 (S3 x) (D3 y)
avCons3 (S3 x)   (C3 y z) = C3 (S3 x) (C3 y z)
avCons3 (D3 x)   b        = C3 (D3 x) b
avCons3 (C3 x y) b        = C3 (C3 x y) b

avCons3-sound : ∀ a b s1 s2 d → γ3 (avCons3 a b) s1 s2 d ≡ γ3 a s1 s2 d · γ3 b s1 s2 d
avCons3-sound (S3 v1)  (S3 v2)  s1 s2 d = refl
avCons3-sound (S3 x)   (D3 y)   s1 s2 d = refl
avCons3-sound (S3 x)   (C3 y z) s1 s2 d = refl
avCons3-sound (D3 x)   b        s1 s2 d = refl
avCons3-sound (C3 x y) b        s1 s2 d = refl

------------------------------------------------------------------------
-- COGEN: specialise keeping ALL of s1,s2,d symbolic (nothing is known yet — cogen is
-- program-independent).  Constants and structure fold; every input is residualised.

gen : Exp2 → AV3
gen x1         = D3 j1
gen x2         = D3 j2
gen xd         = D3 jd
gen (kK v)     = S3 v
gen (hHd e)    = avHd3 (gen e)
gen (hTl e)    = avTl3 (gen e)
gen (hCons a b) = avCons3 (gen a) (gen b)

gen-sound : ∀ e s1 s2 d → γ3 (gen e) s1 s2 d ≡ evalE2 e s1 s2 d
gen-sound x1         s1 s2 d = refl
gen-sound x2         s1 s2 d = refl
gen-sound xd         s1 s2 d = refl
gen-sound (kK v)     s1 s2 d = refl
gen-sound (hHd e)    s1 s2 d =
  trans (avHd3-sound (gen e) s1 s2 d) (cong hd (gen-sound e s1 s2 d))
gen-sound (hTl e)    s1 s2 d =
  trans (avTl3-sound (gen e) s1 s2 d) (cong tl (gen-sound e s1 s2 d))
gen-sound (hCons a b) s1 s2 d =
  trans (avCons3-sound (gen a) (gen b) s1 s2 d)
        (cong₂ _·_ (gen-sound a s1 s2 d) (gen-sound b s1 s2 d))

------------------------------------------------------------------------
-- GENERATE ([cogen](int)): fill the interpreter hole j1 with s1 → comp (over j2, jd).

subst1 : Code3 → Val → Code3
subst1 (jVal v)   s1 = jVal v
subst1 j1         s1 = jVal s1
subst1 j2         s1 = j2
subst1 jd         s1 = jd
subst1 (jHd c)    s1 = jHd (subst1 c s1)
subst1 (jTl c)    s1 = jTl (subst1 c s1)
subst1 (jCons a b) s1 = jCons (subst1 a s1) (subst1 b s1)

subst1-sound : ∀ c s1 s1′ s2 d → ⟦ subst1 c s1 ⟧3 s1′ s2 d ≡ ⟦ c ⟧3 s1 s2 d
subst1-sound (jVal v)   s1 s1′ s2 d = refl
subst1-sound j1         s1 s1′ s2 d = refl
subst1-sound j2         s1 s1′ s2 d = refl
subst1-sound jd         s1 s1′ s2 d = refl
subst1-sound (jHd c)    s1 s1′ s2 d = cong hd (subst1-sound c s1 s1′ s2 d)
subst1-sound (jTl c)    s1 s1′ s2 d = cong tl (subst1-sound c s1 s1′ s2 d)
subst1-sound (jCons a b) s1 s1′ s2 d =
  cong₂ _·_ (subst1-sound a s1 s1′ s2 d) (subst1-sound b s1 s1′ s2 d)

generate : AV3 → Val → AV3
generate (S3 v)   s1 = S3 v
generate (D3 c)   s1 = D3 (subst1 c s1)
generate (C3 a b) s1 = C3 (generate a s1) (generate b s1)

generate-sound : ∀ a s1 s1′ s2 d → γ3 (generate a s1) s1′ s2 d ≡ γ3 a s1 s2 d
generate-sound (S3 v)   s1 s1′ s2 d = refl
generate-sound (D3 c)   s1 s1′ s2 d = subst1-sound c s1 s1′ s2 d
generate-sound (C3 a b) s1 s1′ s2 d =
  cong₂ _·_ (generate-sound a s1 s1′ s2 d) (generate-sound b s1 s1′ s2 d)

------------------------------------------------------------------------
-- COMPILE ([comp](s2)): fill the source hole j2 with s2 → target (over jd only).

subst2 : Code3 → Val → Code3
subst2 (jVal v)   s2 = jVal v
subst2 j1         s2 = j1
subst2 j2         s2 = jVal s2
subst2 jd         s2 = jd
subst2 (jHd c)    s2 = jHd (subst2 c s2)
subst2 (jTl c)    s2 = jTl (subst2 c s2)
subst2 (jCons a b) s2 = jCons (subst2 a s2) (subst2 b s2)

subst2-sound : ∀ c s2 s1 s2′ d → ⟦ subst2 c s2 ⟧3 s1 s2′ d ≡ ⟦ c ⟧3 s1 s2 d
subst2-sound (jVal v)   s2 s1 s2′ d = refl
subst2-sound j1         s2 s1 s2′ d = refl
subst2-sound j2         s2 s1 s2′ d = refl
subst2-sound jd         s2 s1 s2′ d = refl
subst2-sound (jHd c)    s2 s1 s2′ d = cong hd (subst2-sound c s2 s1 s2′ d)
subst2-sound (jTl c)    s2 s1 s2′ d = cong tl (subst2-sound c s2 s1 s2′ d)
subst2-sound (jCons a b) s2 s1 s2′ d =
  cong₂ _·_ (subst2-sound a s2 s1 s2′ d) (subst2-sound b s2 s1 s2′ d)

compile : AV3 → Val → AV3
compile (S3 v)   s2 = S3 v
compile (D3 c)   s2 = D3 (subst2 c s2)
compile (C3 a b) s2 = C3 (compile a s2) (compile b s2)

compile-sound : ∀ a s2 s1 s2′ d → γ3 (compile a s2) s1 s2′ d ≡ γ3 a s1 s2 d
compile-sound (S3 v)   s2 s1 s2′ d = refl
compile-sound (D3 c)   s2 s1 s2′ d = subst2-sound c s2 s1 s2′ d
compile-sound (C3 a b) s2 s1 s2′ d =
  cong₂ _·_ (compile-sound a s2 s1 s2′ d) (compile-sound b s2 s1 s2′ d)

------------------------------------------------------------------------
-- THE FUTAMURA fp3 EQUATION: GENERATE (fill int) then COMPILE (fill source) then run
-- over d equals direct evaluation.  s1′,s2′ are arbitrary (both holes are gone).

fp3-eq : ∀ e s1 s2 s1′ s2′ d →
         γ3 (compile (generate (gen e) s1) s2) s1′ s2′ d ≡ evalE2 e s1 s2 d
fp3-eq e s1 s2 s1′ s2′ d =
  trans (compile-sound (generate (gen e) s1) s2 s1′ s2′ d)
        (trans (generate-sound (gen e) s1 s1′ s2 d) (gen-sound e s1 s2 d))

------------------------------------------------------------------------
-- Non-triviality: the correct cogen keeps the interpreter symbolic (a j1 hole).

gen-keeps-int-symbolic : gen x1 ≡ D3 j1
gen-keeps-int-symbolic = refl

------------------------------------------------------------------------
-- The OVER-STATIC bug at the cogen level: freeze the interpreter at cogen-build time.

genbug : Exp2 → AV3
genbug x1         = S3 ⟨⟩       -- BUG: commit the interpreter to a static value
genbug x2         = D3 j2
genbug xd         = D3 jd
genbug (kK v)     = S3 v
genbug (hHd e)    = avHd3 (genbug e)
genbug (hTl e)    = avTl3 (genbug e)
genbug (hCons a b) = avCons3 (genbug a) (genbug b)

⟨⟩≢vtrue : ⟨⟩ ≡ vtrue → ⊥
⟨⟩≢vtrue ()

genbug-wrong-on-int :
  ¬ (∀ s1 s2 d → γ3 (genbug x1) s1 s2 d ≡ evalE2 x1 s1 s2 d)
genbug-wrong-on-int hyp = ⟨⟩≢vtrue (hyp vtrue ⟨⟩ ⟨⟩)

------------------------------------------------------------------------
-- GAIN: constant / structural parts collapse to a single value already at stage 0.

data stage0Static : Exp2 → Set where
  s0K    : ∀ v → stage0Static (kK v)
  s0Hd   : ∀ {e} → stage0Static e → stage0Static (hHd e)
  s0Tl   : ∀ {e} → stage0Static e → stage0Static (hTl e)
  s0Cons : ∀ {a b} → stage0Static a → stage0Static b → stage0Static (hCons a b)

data isS3 : AV3 → Set where
  mkS3 : ∀ v → isS3 (S3 v)

avHd3-isS3 : ∀ {a} → isS3 a → isS3 (avHd3 a)
avHd3-isS3 (mkS3 v) = mkS3 (hd v)

avTl3-isS3 : ∀ {a} → isS3 a → isS3 (avTl3 a)
avTl3-isS3 (mkS3 v) = mkS3 (tl v)

avCons3-isS3 : ∀ {a b} → isS3 a → isS3 b → isS3 (avCons3 a b)
avCons3-isS3 (mkS3 v1) (mkS3 v2) = mkS3 (v1 · v2)

gain : ∀ {e} → stage0Static e → isS3 (gen e)
gain (s0K v)       = mkS3 v
gain (s0Hd st)     = avHd3-isS3 (gain st)
gain (s0Tl st)     = avTl3-isS3 (gain st)
gain (s0Cons sa sb) = avCons3-isS3 (gain sa) (gain sb)
