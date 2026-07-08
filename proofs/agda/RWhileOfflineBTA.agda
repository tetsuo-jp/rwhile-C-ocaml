{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline binding-time analysis (BTA): a design blueprint (in Agda) for the
-- open "real fp2" problem — the OVER-STATIC binding-time bug of spec_av.
--
-- Background (see RESEARCH_ROADMAP.md §1-①-(2), second-futamura-projection-status).
-- The self-application fp2 = [spec_av]((spec_av . ri_min)) produces an *incorrect*
-- compiler once the loops are trivialised.  Root cause: examples/spec_av.rwhile:1051
--
--     FpPart <= cons 'C (cons (cons 'S Src) …)
--
-- tags the source `Src` UNCONDITIONALLY as 'S (static).  In fp1 that is right (Src
-- really is static), but under self-application the inner "static input" is the
-- outer's DYNAMIC data, so committing it to a static value is unsound.  This is the
-- classic clash between ONLINE, value-carrying AVs (an 'S-AV literally carries a Val,
-- and AV-HD/AV-EQ/AV-LIFT assume that) and OFFLINE, two-level binding times (an 'S
-- position is "known at spec time" but may be SYMBOLIC).
--
-- This module makes the diagnosis precise and gives the fix as a theorem:
--
--   * static-stability:  a fully-static AV denotes a ρ-INDEPENDENT value.
--   * over-commit-unsound / no-static-identity:  therefore NO static AV can
--     faithfully abstract a runtime-dependent slot (e.g. the identity on ρ).
--     ⇒ freezing a dynamic slot to `S` is unsound — this IS the over-static bug.
--   * The congruence-driven offline constructor `mkAV`:  `mkAV dyn` NEVER returns a
--     static AV (`mkAV-dyn-nonstatic`).  So a spec that builds slots through `mkAV`
--     (BT-driven) is structurally incapable of the bug — the intended fix for :1051.
--   * The honest offline specialiser `spec2` (built from avHd/avTl/avCons) is SOUND
--     for every expression (`spec2-sound`), and is fully static EXACTLY when the
--     source does not read the dynamic input (`spec2-static`) — congruence holds by
--     construction, so `spec2` exhibits no over-commit.
--
-- Reuses the AV algebra + soundness lemmas of RWhileAVSound.
------------------------------------------------------------------------
module RWhileOfflineBTA where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

open import RWhileAVSound
  using ( Val; ⟨⟩; _·_; vtrue; hd; tl
        ; Code; cVar; cVal; cHd; cTl; cCons; ⟦_⟧c
        ; AV; S; D; C; γ
        ; avHd; avTl; avCons; avHd-sound; avTl-sound; avCons-sound )

------------------------------------------------------------------------
-- "Fully static" AVs: built from S / C only (no dynamic D hole anywhere).

data staticAV : AV → Set where
  sS : ∀ v          → staticAV (S v)
  sC : ∀ {a b} → staticAV a → staticAV b → staticAV (C a b)

-- The crux: a fully-static AV denotes a value that does NOT depend on the runtime
-- dynamic input ρ.  (spec_av's 'S-AVs are exactly these — value-carrying.)
static-stable : ∀ {a} → staticAV a → ∀ ρ ρ′ → γ a ρ ≡ γ a ρ′
static-stable (sS v)     ρ ρ′ = refl
static-stable (sC pa pb) ρ ρ′ = cong₂ _·_ (static-stable pa ρ ρ′) (static-stable pb ρ ρ′)

------------------------------------------------------------------------
-- Over-commit is unsound.  If a fully-static AV faithfully abstracts a function
-- f : Val → Val (γ a ρ ≡ f ρ for all ρ), then f must be constant.  Contrapositive:
-- a genuinely runtime-dependent slot CANNOT be represented by any static AV — so
-- freezing it to `S` (the :1051 bug) is unsound.

over-commit-unsound :
  ∀ {a} → staticAV a → (f : Val → Val) → (∀ ρ → γ a ρ ≡ f ρ) →
  ∀ ρ ρ′ → f ρ ≡ f ρ′
over-commit-unsound {a} sa f hyp ρ ρ′ =
  trans (sym (hyp ρ)) (trans (static-stable sa ρ ρ′) (hyp ρ′))

-- Concrete witness: no static AV abstracts the IDENTITY on ρ (the paradigmatic
-- dynamic slot — "the runtime input itself").  ⟨⟩ ≢ vtrue is decided by constructors.
⟨⟩≢vtrue : ⟨⟩ ≡ vtrue → ⊥
⟨⟩≢vtrue ()

no-static-identity : ∀ {a} → staticAV a → ¬ (∀ ρ → γ a ρ ≡ ρ)
no-static-identity sa hyp =
  ⟨⟩≢vtrue (over-commit-unsound sa (λ ρ → ρ) hyp ⟨⟩ vtrue)

------------------------------------------------------------------------
-- The fix: a congruence-driven, BT-annotated constructor (offline MKAV).
-- `sta` ⇒ carry the known value as an S-AV; `dyn` ⇒ residualise as a D-AV.
-- This is what spec_av.rwhile:1051 should do INSTEAD of the unconditional 'S tag.

data BT : Set where
  sta dyn : BT

mkAV : BT → Val → Code → AV
mkAV sta v _ = S v      -- known value → static AV
mkAV dyn _ c = D c      -- symbolic position → residual code (NOT frozen to S)

-- Soundness both ways: static commits to the value, dynamic tracks the code.
mkAV-sound-sta : ∀ v c ρ → γ (mkAV sta v c) ρ ≡ v
mkAV-sound-sta v c ρ = refl

mkAV-sound-dyn : ∀ v c ρ → γ (mkAV dyn v c) ρ ≡ ⟦ c ⟧c ρ
mkAV-sound-dyn v c ρ = refl

-- No over-commit, structurally: the dynamic binding time NEVER yields a static AV.
-- (staticAV has no constructor for `D c`.)  This is the property whose absence at
-- :1051 causes the over-static fp2 bug.
mkAV-dyn-nonstatic : ∀ v c → ¬ staticAV (mkAV dyn v c)
mkAV-dyn-nonstatic v c ()

------------------------------------------------------------------------
-- The honest offline specialiser on a small two-level expression fragment.
-- Environment = a static source `s` (as in `spec p (s · d)`) and the dynamic input.
-- eS reads the static source, eD reads the dynamic input, eK a constant.

data Exp : Set where
  eS    : Exp                 -- static source s   (binding time: static)
  eD    : Exp                 -- dynamic input d   (binding time: dynamic)
  eK    : Val → Exp           -- constant
  eHd   : Exp → Exp
  eTl   : Exp → Exp
  eCons : Exp → Exp → Exp

-- Concrete meaning:  evalE e s d.
evalE : Exp → Val → Val → Val
evalE eS         s d = s
evalE eD         s d = d
evalE (eK v)     s d = v
evalE (eHd e)    s d = hd (evalE e s d)
evalE (eTl e)    s d = tl (evalE e s d)
evalE (eCons a b) s d = evalE a s d · evalE b s d

-- Offline specialisation w.r.t. the known static source `s`; residual over the one
-- dynamic hole ρ = d.  eD is residualised to `D cVar` (a hole), never frozen.
spec2 : Exp → Val → AV
spec2 eS         s = S s
spec2 eD         s = D cVar
spec2 (eK v)     s = S v
spec2 (eHd e)    s = avHd (spec2 e s)
spec2 (eTl e)    s = avTl (spec2 e s)
spec2 (eCons a b) s = avCons (spec2 a s) (spec2 b s)

-- H1 for this fragment: the residual, concretised at ρ = d, equals eval.
spec2-sound : ∀ e s d → γ (spec2 e s) d ≡ evalE e s d
spec2-sound eS         s d = refl
spec2-sound eD         s d = refl
spec2-sound (eK v)     s d = refl
spec2-sound (eHd e)    s d =
  trans (avHd-sound (spec2 e s) d) (cong hd (spec2-sound e s d))
spec2-sound (eTl e)    s d =
  trans (avTl-sound (spec2 e s) d) (cong tl (spec2-sound e s d))
spec2-sound (eCons a b) s d =
  trans (avCons-sound (spec2 a s) (spec2 b s) d)
        (cong₂ _·_ (spec2-sound a s d) (spec2-sound b s d))

------------------------------------------------------------------------
-- Congruence, by construction.  An expression that does NOT read the dynamic input
-- ("noD") specialises to a fully-static AV; one that DOES read it specialises to a
-- non-static AV (`spec2 eD s = D cVar`).  So spec2 commits to `S` EXACTLY on the
-- genuinely static parts — it can never over-commit a dynamic slot.

data noD : Exp → Set where
  ndS    : noD eS
  ndK    : ∀ v → noD (eK v)
  ndHd   : ∀ {e} → noD e → noD (eHd e)
  ndTl   : ∀ {e} → noD e → noD (eTl e)
  ndCons : ∀ {a b} → noD a → noD b → noD (eCons a b)

-- avHd/avTl/avCons preserve full staticness.
avHd-static : ∀ {a} → staticAV a → staticAV (avHd a)
avHd-static (sS v)     = sS (hd v)
avHd-static (sC pa pb) = pa

avTl-static : ∀ {a} → staticAV a → staticAV (avTl a)
avTl-static (sS v)     = sS (tl v)
avTl-static (sC pa pb) = pb

avCons-static : ∀ {a b} → staticAV a → staticAV b → staticAV (avCons a b)
avCons-static (sS v1)  (sS v2)   = sS (v1 · v2)
avCons-static (sS v1)  (sC qy qz) = sC (sS v1) (sC qy qz)
avCons-static (sC px py) qb       = sC (sC px py) qb

-- No-D source ⇒ fully-static residual (the congruent direction).
spec2-static : ∀ {e} s → noD e → staticAV (spec2 e s)
spec2-static s ndS           = sS _
spec2-static s (ndK v)       = sS v
spec2-static s (ndHd nd)     = avHd-static (spec2-static s nd)
spec2-static s (ndTl nd)     = avTl-static (spec2-static s nd)
spec2-static s (ndCons na nb) = avCons-static (spec2-static s na) (spec2-static s nb)

-- Reading the dynamic input yields a NON-static residual — witnessed on eD itself:
-- spec2 eD s = D cVar, and by no-static-identity no static AV could stand in for it.
spec2-eD-nonstatic : ∀ s → ¬ staticAV (spec2 eD s)
spec2-eD-nonstatic s ()
