{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 案1-B (Agda-first): the LOOP binding-time decision for a reversible
-- specialiser, and why it must inspect the EXIT test, not only the entry.
--
-- comp2 (the self-applied spec_av) stayed trivial because DYNAMICIZE-ALL froze
-- the static inner program; the selective-dynamicize fix lets the inner
-- interpreter UNROLL.  But unrolling then exposed a SECOND issue (the runtime
-- error `'error <= '41` in spec_av's 'lcheck): spec_av's 'loop handler decides to
-- statically unroll a loop by looking only at the ENTRY test's binding time, then
-- the 'lcheck continuation gets stuck when the EXIT test turns out DYNAMIC.
--
-- This module models that decision over annotated values (RWhileAVSound's AV /
-- γ) and proves, axiom-free:
--   * staticTruth : classify a test's AV as a statically-known truth value
--     (S → known, C → definitely a cons = true, D → unknown), γ-SOUND.
--   * a DYNAMIC test genuinely varies with the runtime input -> not resolvable.
--   * the CORRECT unrollability predicate needs BOTH entry and exit static;
--     the entry-only predicate spec_av used is wrong on a static-entry /
--     dynamic-exit loop (exactly the '41 scenario).
--   * a dynamic exit ALWAYS forces residualisation.
-- This is the verified blueprint for the implementation fix: in the 'loop
-- handler, specialise the exit test too and residualise unless BOTH are static.
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileLoopBTA where

open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import RWhileAVSound using (Val; ⟨⟩; _·_; AV; S; D; C; γ; Code; cVar; ⟦_⟧c)

------------------------------------------------------------------------
-- Truthiness (R-WHILE: nil = false, any cons = true).

truthy : Val → Bool
truthy ⟨⟩      = false
truthy (_ · _) = true

------------------------------------------------------------------------
-- Static resolution of a test's annotated value.
--   S v   : statically known -> truthy v.
--   C _ _ : a partial-static cons is DEFINITELY a cons -> true.
--   D _   : dynamic (depends on the runtime input) -> cannot decide.

staticTruth : AV → Maybe Bool
staticTruth (S v)   = just (truthy v)
staticTruth (C _ _) = just true
staticTruth (D _)   = nothing

-- Soundness: if the test resolves statically to b, it IS b at every runtime ρ.
staticTruth-sound : ∀ a b ρ → staticTruth a ≡ just b → truthy (γ a ρ) ≡ b
staticTruth-sound (S v)   .(truthy v) ρ refl = refl
staticTruth-sound (C x y) .true       ρ refl = refl
staticTruth-sound (D c)   b           ρ ()

-- A dynamic test reading the runtime input genuinely VARIES: nil-input gives
-- false, cons-input gives true, so no single static truth value can stand in.
dynamic-varies :
  Σ[ ρ₁ ∈ Val ] Σ[ ρ₂ ∈ Val ] (¬ (truthy (γ (D cVar) ρ₁) ≡ truthy (γ (D cVar) ρ₂)))
dynamic-varies = ⟨⟩ , (⟨⟩ · ⟨⟩) , λ ()

------------------------------------------------------------------------
-- The loop unrollability decision.

-- CORRECT: unroll only when BOTH entry and exit tests are statically known
-- (the loop's control is independent of the runtime input).
unrollable : AV → AV → Bool
unrollable e f = is-just (staticTruth e) ∧ is-just (staticTruth f)

-- BUGGY (what spec_av's 'loop handler effectively used): inspect only the entry.
unrollable-entry-only : AV → AV → Bool
unrollable-entry-only e f = is-just (staticTruth e)

-- THE BUG, formally: a loop with a STATIC entry but a DYNAMIC exit is classified
-- "unrollable" by the entry-only check, yet the correct predicate rejects it.
-- (Static entry S vtrue, dynamic exit D cVar -- the spec_av '41 scenario.)
bug-static-entry-dynamic-exit :
    (unrollable-entry-only (S (⟨⟩ · ⟨⟩)) (D cVar) ≡ true)
  × (unrollable           (S (⟨⟩ · ⟨⟩)) (D cVar) ≡ false)
bug-static-entry-dynamic-exit = refl , refl

-- A dynamic EXIT always forces residualisation, whatever the entry is.
exit-dynamic-forces-residual : ∀ e c → unrollable e (D c) ≡ false
exit-dynamic-forces-residual e c with staticTruth e
... | just _  = refl
... | nothing = refl

-- When the decision says "unroll", BOTH tests really are statically known, so
-- both can be resolved at specialisation time (the unroll is justified).
unrollable-justified : ∀ e f → unrollable e f ≡ true →
  (Σ[ be ∈ Bool ] staticTruth e ≡ just be) × (Σ[ bf ∈ Bool ] staticTruth f ≡ just bf)
unrollable-justified e f h with staticTruth e | staticTruth f
... | just be | just bf = (be , refl) , (bf , refl)
-- the other combinations make `unrollable e f` reduce to false, contradicting h:
unrollable-justified e f () | just be | nothing
unrollable-justified e f () | nothing | just bf
unrollable-justified e f () | nothing | nothing

------------------------------------------------------------------------
-- Concrete loop semantics + the meaning-preservation the decision protects.
-- A reversible-style loop iterates `body` while the exit test is false (fuel for
-- totality).  The point: when the decision unrolls, it is sound to peel one
-- iteration; this is exactly spec_av's 'lcheck step -- valid ONLY when the exit
-- is statically known (false here).

open import Data.Nat using (ℕ; suc)

loopRun : ℕ → (Val → Val) → (Val → Val) → Val → Maybe Val
loopRun ℕ.zero  _    _    _ = nothing
loopRun (suc n) body exit σ with truthy (exit σ)
... | true  = just σ
... | false = loopRun n body exit (body σ)

-- Unroll one iteration: sound exactly when the exit test is (statically) false.
-- This mirrors the 'lcheck continuation -- and is why a dynamic exit (whose
-- truth we cannot know at spec time) must NOT take this path.
unroll-step-sound : ∀ n body exit σ →
  truthy (exit σ) ≡ false →
  loopRun (suc n) body exit σ ≡ loopRun n body exit (body σ)
unroll-step-sound n body exit σ h with truthy (exit σ)
... | false = refl
unroll-step-sound n body exit σ () | true

-- And if the exit is (statically) true, the loop stops here -- the other 'lcheck
-- branch.  Together these are the only two STATIC outcomes; a dynamic exit fits
-- neither, so the loop must be residualised (exit-dynamic-forces-residual).
exit-true-stops : ∀ n body exit σ →
  truthy (exit σ) ≡ true →
  loopRun (suc n) body exit σ ≡ just σ
exit-true-stops n body exit σ h with truthy (exit σ)
... | true = refl
exit-true-stops n body exit σ () | false
