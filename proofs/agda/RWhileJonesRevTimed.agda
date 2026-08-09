{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE BRIDGE: an instance of the reversible Jones criterion ON THE TIMED
-- CORE, and the ONE theorem that R-WHILE's p⁺ satisfies its obligation.
--
-- Until now the development had two layers that did not meet:
--
--   abstract   RWhileJonesRev.Criterion — data, programs, semantics, cost,
--              encoding and pairing all parameters; `PP q p` is an equation
--              between TOTAL functions;
--   concrete   RWhileTime / RWhileProgPres — a cost-annotated RELATION and
--              a construction of p⁺ inside it.
--
-- "R-WHILE's p⁺ meets `PP`" was therefore stated twice, once per layer, and
-- never proved as a single theorem: the criterion demanded a total `⟦_⟧`
-- that the timed core cannot supply.
--
-- RWhileJonesRevRel removes the demand (the criterion is restated over a
-- deterministic partial semantics, with the total setting as a special
-- case).  This module cashes that in: it instantiates the relational
-- criterion at the timed core and proves
--
--     ⁺-PP :  PP p⁺ p                                    (module Ext)
--
-- for the p⁺ that RWhileProgPres actually BUILDS, with `PP` being genuine
-- Kleene equality — p⁺ converges exactly where p does (⁺-run forwards,
-- RWhileProgPresBack.pp-back backwards).  Everything the abstract layer
-- proves about `PP` therefore now applies to R-WHILE programs:
-- `pp-unique`, `pp-injective`, `classical⇒rev`, `rev-mono`.
--
-- WHAT THE PROGRAMS ARE.  `Program` is RWhileProgWork's `read X; body;
-- write Y`, and a run is a derivation of the timed core from the store that
-- has `d` in the input slot and nil everywhere else, ending in a store that
-- is nil everywhere but the output slot (R-WHILE's `all_cleared`).  The cost
-- is the step count, i.e. `./ri -steps`.  The encoding ⌜·⌝ is a module
-- parameter `code`, exactly as `Simp.program_preserving` treats it (it calls
-- `Program2DataRwhile.program2data` once, at construction time, and then the
-- result is a constant of the program text).
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileJonesRevTimed where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import RWhileTime
open import RWhileTimeDet using (⇒-det)
open import RWhileProgWork using (Program; prog)
open import RWhileProgPresBack using (module PPBack)
open import RWhileJonesRevRel using (module CriterionR)

------------------------------------------------------------------------
-- The pairing of R-WHILE data is injective on the right, so the
-- `⊗-injectiveʳ` hypothesis is discharged rather than assumed.

∙-injʳ : ∀ {a x z : V} → (a ∙ x) ≡ (a ∙ z) → x ≡ z
∙-injʳ refl = refl

------------------------------------------------------------------------
-- The instance.

module Timed (code : Program → V) where

  ----------------------------------------------------------------------
  -- 1.  What it means for a whole program to converge, at a cost.
  --
  -- Identical to RWhileProgWork's `_▷_⇒_∥_` except that the meter kept is
  -- the STEP count.  The last premise is `all_cleared`.

  infix 3 _⊨_⇓_∣_
  data _⊨_⇓_∣_ : Program → V → V → ℕ → Set where
    run : ∀ {x y c d τ k v}
        → c ⊢ set [] x d ⇒ τ ∣ k
        → get τ y ≡ v
        → (∀ z → ¬ (y ≡ z) → get τ z ≡ nil)
        → prog x y c ⊨ d ⇓ v ∣ k

  -- R-WHILE is deterministic, which is what lets the relation stand in for
  -- the function the abstract criterion wanted.
  ⇓-det : ∀ {p d v₁ v₂ k₁ k₂}
        → p ⊨ d ⇓ v₁ ∣ k₁ → p ⊨ d ⇓ v₂ ∣ k₂ → (v₁ ≡ v₂) × (k₁ ≡ k₂)
  ⇓-det (run d₁ h₁ _) (run d₂ h₂ _) with ⇒-det d₁ d₂
  ... | refl , refl = trans (sym h₁) h₂ , refl

  -- THE INSTANTIATION.  Everything RWhileJonesRevRel proves is now
  -- available for R-WHILE programs under the timed semantics.
  open CriterionR V Program _⊨_⇓_∣_ ⇓-det code _∙_ public

  ----------------------------------------------------------------------
  -- 2.  p⁺, and the theorem that it meets the obligation.
  --
  -- The module parameters are the source program (input slot x, output slot
  -- y, body c) and the two fresh slots of `Simp.program_preserving`
  -- (`P-SELF` = self, `OUT-PP` = o).

  module Ext (x y self o : ℕ) (c : Cmd)
             (self≢y : ¬ (self ≡ y))
             (self≢o : ¬ (self ≡ o))
             (o≢y    : ¬ (o ≡ y))
             where

    p : Program
    p = prog x y c

    open PPBack y self o (code p) self≢y self≢o o≢y

    p⁺ : Program
    p⁺ = prog x o (ppBody c)

    ------------------------------------------------------------------
    -- Forwards: wherever p converges, p⁺ converges to ⟨⌜p⌝ , answer⟩,
    -- at cost + 8.  (RWhileProgPres.pp-cost, lifted to whole programs;
    -- the new content is that p⁺'s `all_cleared` survives.)

    ⁺-run : ∀ {d v k} → p ⊨ d ⇓ v ∣ k → p⁺ ⊨ d ⇓ (code p ∙ v) ∣ (k + 8)
    ⁺-run (run {τ = τ} {v = v} dc hy hcl) =
      run (pp-cost v dc (hcl self y≢self) (hcl o y≢out) hy) (final-out τ v) cl
      where
        cl : ∀ z → ¬ (o ≡ z) → get (final τ v) z ≡ nil
        cl z ne with y ≟ z | self ≟ z
        ... | yes refl | _        = final-y τ v
        ... | no ny    | yes refl = final-self τ v
        ... | no ny    | no ns    = trans (final-frame τ v z ny ns ne) (hcl z ny)

    ------------------------------------------------------------------
    -- Backwards: p⁺ converges ONLY where p does, and then at exactly
    -- cost(p) + 8.  (RWhileProgPresBack.pp-back, lifted the same way.)

    back : ∀ {d u m} → p⁺ ⊨ d ⇓ u ∣ m
         → Σ[ v ∈ V ] Σ[ k ∈ ℕ ] ((p ⊨ d ⇓ v ∣ k) × (m ≡ k + 8))
    back (run dpp _ hcl) with pp-back dpp hcl
    ... | τ , k , db , hs , ho , ρ≡ , m≡ = get τ y , k , run db refl cl , m≡
      where
        cl : ∀ z → ¬ (y ≡ z) → get τ z ≡ nil
        cl z ny with self ≟ z | o ≟ z
        ... | yes refl | _        = hs
        ... | no ns    | yes refl = ho
        ... | no ns    | no no′   =
              trans (sym (final-frame τ (get τ y) z ny ns no′))
                    (trans (cong (λ σ → get σ z) (sym ρ≡)) (hcl z no′))

    ------------------------------------------------------------------
    -- THE THEOREM.  p⁺ satisfies the criterion's obligation — ONE
    -- statement, about the p⁺ the timed core builds, in the criterion the
    -- abstract layer defines.  (Gap 2 of AGDA_CORRESPONDENCE closed.)

    ⁺-PP : PP p⁺ p
    ⁺-PP = fwd , bwd
      where
        fwd : PP⇒ p⁺ p
        fwd dp = _ , ⁺-run dp
        bwd : PP⇐ p⁺ p
        bwd dpp with back dpp
        ... | v , k , dp , _ = v , k , dp

    ------------------------------------------------------------------
    -- Consequences, now available on the concrete layer.

    -- the basis is at least as expensive as p: the side condition of
    -- `classical⇒rev`, DISCHARGED (it is the +8 of pp-cost).
    ⁺-mono : p ≼ p⁺
    ⁺-mono dpp with back dpp
    ... | v , k , dp , m≡ = v , k , dp , subst (k ≤_) (sym m≡) (m≤m+n k 8)

    -- reversible Jones optimality for THIS p, on the step meter
    RevJonesTimed : Program → Set
    RevJonesTimed r = RevJonesOptimal r p p⁺

    classical⇒rev-timed : ∀ {r} → JonesOptimal r p → RevJonesTimed r
    classical⇒rev-timed = classical⇒rev ⁺-PP ⁺-mono

    -- what the criterion SAYS, unfolded at the step meter: the residual is
    -- allowed 8 steps more than p, and not one more.  (Contrast the work
    -- meter, where the slack is |⌜p⌝| + |answer| — RWhileProgPresWork.)
    rev-unfold : ∀ {r} → RevJonesTimed r
               → ∀ {d v k} → p ⊨ d ⇓ v ∣ k
               → Σ[ w ∈ V ] Σ[ j ∈ ℕ ] ((r ⊨ d ⇓ w ∣ j) × (j ≤ k + 8))
    rev-unfold (_ , le) dp = le (⁺-run dp)

    rev-fold : ∀ {r}
             → (∀ {d v k} → p ⊨ d ⇓ v ∣ k
                → Σ[ w ∈ V ] Σ[ j ∈ ℕ ] ((r ⊨ d ⇓ w ∣ j) × (j ≤ k + 8)))
             → RevJonesTimed r
    rev-fold {r} h = ⁺-PP , le
      where
        le : r ≼ p⁺
        le dpp with back dpp
        ... | v , k , dp , m≡ with h dp
        ...   | w , j , dr , j≤ = w , j , dr , subst (j ≤_) (sym m≡) j≤

    -- p⁺ is injective whenever p is (the reversibility side), with the
    -- ⊗-injectivity hypothesis discharged for R-WHILE data.
    ⁺-injective : Inj p → Inj p⁺
    ⁺-injective = pp-injective ∙-injʳ ⁺-PP

    -- the answer of p⁺ is THE answer: any program meeting the obligation
    -- agrees with it wherever p converges.
    ⁺-answer : ∀ {q d v k u j} → PP⇒ q p
             → p ⊨ d ⇓ v ∣ k → q ⊨ d ⇓ u ∣ j → u ≡ code p ∙ v
    ⁺-answer = pp-answer

------------------------------------------------------------------------
-- A CONCRETE INSTANCE, so that none of the above is vacuous: the worked
-- example of RWhileProgPres, now as a criterion-level statement.
--
--   p  = read V0;  V0 ^= 'seven;  write V0
--   p⁺ = read V0;  V0 ^= 'seven;  emit;  write V2      (V1 = P-SELF, V2 = OUT-PP)
--
-- with ⌜p⌝ modelled by the atom 42.  Both directions of the obligation are
-- exercised: `⁺-ex` runs p⁺ forwards, `back-ex` recovers p's run from it.

module Example where

  codeEx : Program → V
  codeEx _ = atm 42

  open Timed codeEx
  open Ext 0 0 1 2 (0 ^= opd (cst (atm 7))) (λ ()) (λ ()) (λ ())

  bodyEx : Cmd
  bodyEx = 0 ^= opd (cst (atm 7))

  runEx : p ⊨ nil ⇓ atm 7 ∣ 1
  runEx = run {τ = atm 7 ∷ []}
              (exec-sound 1 bodyEx (nil ∷ []) (atm 7 ∷ []) 1 refl) refl cl
    where
      cl : ∀ z → ¬ (0 ≡ z) → get (atm 7 ∷ []) z ≡ nil
      cl zero    ne with ne refl
      ... | ()
      cl (suc z) _ = refl

  -- forwards: p⁺ pairs ⌜p⌝ onto the answer, for 8 steps more
  ⁺-ex : p⁺ ⊨ nil ⇓ (atm 42 ∙ atm 7) ∣ 9
  ⁺-ex = ⁺-run runEx

  -- backwards: from p⁺'s run, p's run and the exact cost relation
  back-ex : Σ[ v ∈ V ] Σ[ k ∈ ℕ ] ((p ⊨ nil ⇓ v ∣ k) × (9 ≡ k + 8))
  back-ex = back ⁺-ex

  -- the criterion is not vacuous here: p⁺ is an admissible basis for p
  basis-ex : PP p⁺ p
  basis-ex = ⁺-PP
