{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 2: the SELF-APPLICATION step (the real fp2).
--
-- Continues RWhileOfflineBTA.  In fp1 = [spec]((p . ('S . s))) the inner static
-- source `s` is a concrete value.  In fp2 = [spec]((spec . ri_min)) the OUTER
-- specialiser feeds the INNER spec a source that is itself the OUTER's DYNAMIC
-- input — i.e. the inner "static source" is SYMBOLIC, not a concrete value.
--
-- We model that by generalising the static source from a `Val` to an `AV`
-- (which may carry a dynamic hole).  The correct, congruence-preserving specialiser
-- `spec2g` handles the source position eS by PASSING THE AV THROUGH unchanged
-- (preserving its binding time), and is sound for ANY source AV — concrete or
-- symbolic (`spec2g-sound`).  The fp1 specialiser is exactly its static instance
-- (`spec2≡spec2g`).
--
-- The over-static bug of spec_av.rwhile:1051 is modelled by `spec2bug`, which FREEZES
-- the source AV to a static value at a fixed runtime (`S (γ sₐ ⟨⟩)`).  We prove:
--
--   * `spec2bug-ok-on-static`   — on a STATIC source the bug is INVISIBLE
--                                 (this is why fp1 is green / DYNAMICIZE-ALL masked it);
--   * `spec2bug-wrong-on-symbolic` — on a SYMBOLIC source it is UNSOUND
--                                 (this is exactly the fp2 over-commit failure).
--
-- Conclusion: the correct fp2 needs the source position specialised by binding-time
-- PASS-THROUGH (`spec2g`), never by value-freezing.  This is the blueprint for the
-- :1051 fix (drive the source AV through mkAV / keep it symbolic under self-app).
------------------------------------------------------------------------
module RWhileOfflineBTA2 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)
open import Relation.Nullary using (¬_)

open import RWhileAVSound
  using ( Val; ⟨⟩; _·_; vtrue; hd; tl
        ; Code; cVar; ⟦_⟧c
        ; AV; S; D; C; γ
        ; avHd; avTl; avCons; avHd-sound; avTl-sound; avCons-sound )

open import RWhileOfflineBTA
  using ( Exp; eS; eD; eK; eHd; eTl; eCons; evalE; spec2
        ; staticAV; sS; sC; static-stable; ⟨⟩≢vtrue )

------------------------------------------------------------------------
-- The correct offline specialiser with a GENERALISED static source (an AV, which
-- may be symbolic).  Source position eS just passes the source AV through — its
-- binding time (S / D / C) is preserved.

spec2g : Exp → AV → AV
spec2g eS          sₐ = sₐ
spec2g eD          sₐ = D cVar
spec2g (eK v)      sₐ = S v
spec2g (eHd e)     sₐ = avHd (spec2g e sₐ)
spec2g (eTl e)     sₐ = avTl (spec2g e sₐ)
spec2g (eCons a b) sₐ = avCons (spec2g a sₐ) (spec2g b sₐ)

-- Generalised H1: concretising the residual at ρ equals evaluating with the
-- concretised static source `γ sₐ ρ`.  Holds for CONCRETE and SYMBOLIC sources alike.
spec2g-sound : ∀ e sₐ ρ → γ (spec2g e sₐ) ρ ≡ evalE e (γ sₐ ρ) ρ
spec2g-sound eS          sₐ ρ = refl
spec2g-sound eD          sₐ ρ = refl
spec2g-sound (eK v)      sₐ ρ = refl
spec2g-sound (eHd e)     sₐ ρ =
  trans (avHd-sound (spec2g e sₐ) ρ) (cong hd (spec2g-sound e sₐ ρ))
spec2g-sound (eTl e)     sₐ ρ =
  trans (avTl-sound (spec2g e sₐ) ρ) (cong tl (spec2g-sound e sₐ ρ))
spec2g-sound (eCons a b) sₐ ρ =
  trans (avCons-sound (spec2g a sₐ) (spec2g b sₐ) ρ)
        (cong₂ _·_ (spec2g-sound a sₐ ρ) (spec2g-sound b sₐ ρ))

-- fp1 is the static instance: feeding a concrete source `S s` recovers spec2.
spec2≡spec2g : ∀ e s → spec2 e s ≡ spec2g e (S s)
spec2≡spec2g eS          s = refl
spec2≡spec2g eD          s = refl
spec2≡spec2g (eK v)      s = refl
spec2≡spec2g (eHd e)     s = cong avHd (spec2≡spec2g e s)
spec2≡spec2g (eTl e)     s = cong avTl (spec2≡spec2g e s)
spec2≡spec2g (eCons a b) s = cong₂ avCons (spec2≡spec2g a s) (spec2≡spec2g b s)

------------------------------------------------------------------------
-- The over-static bug: freeze the source AV to a static value at a FIXED runtime.
-- (This models spec_av.rwhile:1051's unconditional 'S tag: it takes the source's
-- current concrete content and commits it as static.)  Only the eS case differs.

spec2bug : Exp → AV → AV
spec2bug eS          sₐ = S (γ sₐ ⟨⟩)     -- BUG: commit source at ρ = ⟨⟩, dropping ρ-dependence
spec2bug eD          sₐ = D cVar
spec2bug (eK v)      sₐ = S v
spec2bug (eHd e)     sₐ = avHd (spec2bug e sₐ)
spec2bug (eTl e)     sₐ = avTl (spec2bug e sₐ)
spec2bug (eCons a b) sₐ = avCons (spec2bug a sₐ) (spec2bug b sₐ)

-- On a STATIC source the bug is invisible: the frozen value equals the real one at
-- every ρ (static-stability), so the buggy specialiser is still sound.  ⇒ fp1 green.
spec2bug-ok-on-static :
  ∀ e {sₐ} → staticAV sₐ → ∀ ρ → γ (spec2bug e sₐ) ρ ≡ evalE e (γ sₐ ρ) ρ
spec2bug-ok-on-static eS          ssₐ ρ = static-stable ssₐ ⟨⟩ ρ
spec2bug-ok-on-static eD          ssₐ ρ = refl
spec2bug-ok-on-static (eK v)      ssₐ ρ = refl
spec2bug-ok-on-static (eHd e)     ssₐ ρ =
  trans (avHd-sound (spec2bug e _) ρ) (cong hd (spec2bug-ok-on-static e ssₐ ρ))
spec2bug-ok-on-static (eTl e)     ssₐ ρ =
  trans (avTl-sound (spec2bug e _) ρ) (cong tl (spec2bug-ok-on-static e ssₐ ρ))
spec2bug-ok-on-static (eCons a b) ssₐ ρ =
  trans (avCons-sound (spec2bug a _) (spec2bug b _) ρ)
        (cong₂ _·_ (spec2bug-ok-on-static a ssₐ ρ) (spec2bug-ok-on-static b ssₐ ρ))

-- On a SYMBOLIC source the bug is unsound.  Witness: source = `D cVar` (the outer's
-- dynamic input flowing into the inner's "static" slot), expression = eS.  The buggy
-- residual denotes the constant ⟨⟩, but the correct value is ρ itself → mismatch.
spec2bug-wrong-on-symbolic :
  ¬ (∀ ρ → γ (spec2bug eS (D cVar)) ρ ≡ evalE eS (γ (D cVar) ρ) ρ)
spec2bug-wrong-on-symbolic hyp = ⟨⟩≢vtrue (hyp vtrue)

-- ...whereas the correct pass-through specialiser IS sound on that same symbolic
-- source (the instance of spec2g-sound the bug fails).
spec2g-ok-on-symbolic :
  ∀ ρ → γ (spec2g eS (D cVar)) ρ ≡ evalE eS (γ (D cVar) ρ) ρ
spec2g-ok-on-symbolic ρ = spec2g-sound eS (D cVar) ρ
