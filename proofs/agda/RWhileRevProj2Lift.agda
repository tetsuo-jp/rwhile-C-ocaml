{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- C-layer hint for the B-layer 2nd reversible projection (compiler
-- generation by SELF-APPLICATION of the specialiser).
--
-- RWhileFutamura2Inst discharges the self-application hypothesis (H2) with a
-- `papp` CLOSURE trick, which trivialises the one operation that actually
-- breaks the real R-WHILE specialiser (spec_av): turning a static / partial-
-- static annotated value into residual code — `lift` — inside the reversible
-- "lift-then-clear" idiom that CLOSES the residual.  So that instance gives no
-- hint for B.  This module models that idiom HONESTLY in the small core and
-- pins the exact invariant the 2nd projection needs.
--
-- The idiom (spec_av.rwhile ASSEMBLE-FP1, L259-262):
--     LOOKUP(Vl,J',AsAV);     -- a ^= s        : a := s     (a started cleared)
--     AV-LIFT(AsAV,AsCode);   -- c := lift a   (a MUST be preserved)
--     LOOKUP(Vl,J',AsAV);     -- a ^= s        : clear a back to nil
-- The 2nd `a ^= s` is a reversible XOR-assign that CLEARS a only if a still
-- equals s.  We model spec_av's reversible-assign check exactly (L840-849):
-- assigning `new` into slot --- empty slot ⇒ set; slot already = new ⇒ clear;
-- otherwise ⇒ ERROR `'10` (rupdate-different).
--
-- THEOREM: the idiom round-trips (a returns to nil, no '10) IFF `lift`
-- preserves a's value.  The fp2 '10 reproduces with the *actual* drift
-- observed in the trace — AV-LIFT leaving a = (LfTag . LfPay), the lift
-- machinery's own internal variables (plan_fp1_stage_c.md 6.3.2).
--
-- HINT FOR B (delivered by this proof): making AV-LIFT preserve its operand's
-- abstract slot is NECESSARY and SUFFICIENT for the self-applicative ASSEMBLE
-- step — hence for the 2nd reversible projection on the real spec_av.
------------------------------------------------------------------------

module RWhileRevProj2Lift where

open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- Values (program fragments are values too, since program = data).

data V : Set where
  at   : ℕ → V
  cons : V → V → V

_≟V_ : (x y : V) → Dec (x ≡ y)
at m     ≟V at n     with m ≟ n
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
at _     ≟V cons _ _ = no λ ()
cons _ _ ≟V at _     = no λ ()
cons a b ≟V cons c d with a ≟V c | b ≟V d
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }

------------------------------------------------------------------------
-- A scratch slot: `nothing` = cleared (static-nil), `just v` = holds AV value v.
Slot : Set
Slot = Maybe V

-- Reversible XOR-assign of `new` into a slot, modelling spec_av L840-849.
-- `nothing` result = the `'10` error (rupdate-different).
xor : Slot → V → Maybe Slot
xor nothing  new = just (just new)                 -- L842-843: empty ⇒ set
xor (just v) new with v ≟V new
... | yes _ = just nothing                          -- L846-847: matches ⇒ clear
... | no  _ = nothing                               -- L849: mismatch ⇒ '10

------------------------------------------------------------------------
-- The lift-then-clear idiom.  `lift`'s effect on the scratch `a` is the
-- function `le : V → V` (preserving ⇔ le = id).  After
--   a := s          (xor nothing s = just (just s))
--   a := le a       (the AV-LIFT step's net effect on the scratch)
-- the idiom does the clearing `a ^= s`:
liftThenClear : (V → V) → V → Maybe Slot
liftThenClear le s = xor (just (le s)) s

------------------------------------------------------------------------
-- (1) SUFFICIENT: if lift preserves the operand, the idiom round-trips.
idiom-ok : ∀ s → liftThenClear (λ x → x) s ≡ just nothing
idiom-ok s with s ≟V s
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

-- (2) NECESSARY: any drift (le s ≢ s) makes the clear raise '10 (nothing).
idiom-drift : ∀ le s → ¬ (le s ≡ s) → liftThenClear le s ≡ nothing
idiom-drift le s ¬eq with (le s) ≟V s
... | yes eq = ⊥-elim (¬eq eq)
... | no  _  = refl

------------------------------------------------------------------------
-- (3) The ACTUAL fp2 bug: AV-LIFT leaves the scratch holding (LfTag . LfPay)
-- = the lift machinery's own internal variables (indices 16, 17 in the trace),
-- independent of s.  For every output value s that is not literally that
-- fragment, the closing `a ^= s` raises '10 — exactly the observed failure.

LfTag LfPay : V
LfTag = at 16
LfPay = at 17

buggy-lift : V → V
buggy-lift _ = cons LfTag LfPay

bug-reproduces-'10 : ∀ s → ¬ (s ≡ cons LfTag LfPay) → liftThenClear buggy-lift s ≡ nothing
bug-reproduces-'10 s ¬eq = idiom-drift buggy-lift s (λ eq → ¬eq (sym eq))

------------------------------------------------------------------------
-- (4) The FIX, as a theorem: an AV-LIFT that preserves its operand makes the
-- ASSEMBLE step round-trip for EVERY output value — the precise repair B needs.
fix-roundtrips : ∀ s → liftThenClear (λ x → x) s ≡ just nothing
fix-roundtrips = idiom-ok

------------------------------------------------------------------------
-- (5) A FALSE fix, refuted.  One might try to dodge the '10 by clearing the
-- scratch with its OWN current value (`AsAV ^= AsAV`) instead of re-reading the
-- store slot:  selfClear le s = xor (just (le s)) (le s).  This was tried on the
-- real spec_av: fp2 then TERMINATES (no '10) but emits a BROKEN compiler
-- (`error in update: var=Vl` when run).  The reason, made precise here: the
-- self-clear succeeds for ANY `le` — it is INSENSITIVE to the drift — so it
-- removes the symptom without restoring the value `lift` corrupted upstream.
selfClear : (V → V) → V → Maybe Slot
selfClear le s = xor (just (le s)) (le s)

selfClear-masks : ∀ le s → selfClear le s ≡ just nothing
selfClear-masks le s with (le s) ≟V (le s)
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

-- Contrast: the genuine clear (re-read slot `s`) DETECTS drift (idiom-drift
-- raises '10), whereas selfClear never can.  So the only correct repair is to
-- restore lift-preservation (idiom-ok / fix-roundtrips), not to silence the
-- check — exactly what the spec_av experiment confirmed.
