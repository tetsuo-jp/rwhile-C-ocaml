{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- REVERSIBLE JONES OPTIMALITY: the criterion, its basis p⁺, and why the
-- basis is forced (not chosen).
--
-- Jones optimality asks that the residual of specialising a self-interpreter
-- to a source program be no worse than the source program itself:
--
--     ⟦spec⟧(int, p)  ≤  p                                  (classical)
--
-- A REVERSIBLE Futamura projection cannot use that criterion as it stands.
-- The projection needs a PROGRAM-PRESERVING interpreter
--
--     ⟦rint⟧ ⟨⌜p⌝, d⟩ = ⟨⌜p⌝ , ⟦p⟧ d⟩
--
-- (keeping the program is what makes the interpreter injective), and therefore
-- the fp1 residual ⟦spec⟧(rint, ⌜p⌝) INHERITS that obligation: it must emit
-- ⌜p⌝ alongside the answer.  `p` itself does not do that job.  Comparing the
-- residual with `p` charges it for work `p` never does, so the classical
-- criterion would be measuring the definition of the projection rather than
-- the quality of the specialiser.
--
-- The fix is to compare against the smallest program carrying the SAME
-- obligation,
--
--     ⟦p⁺⟧ d = ⟨⌜p⌝ , ⟦p⟧ d⟩ ,
--
-- and to define REVERSIBLE JONES OPTIMALITY as  residual ≤ p⁺.
--
-- This module is the abstract layer: data, programs, semantics, cost, the
-- encoding ⌜·⌝ and the pairing are all parameters.  What is proved here is
-- exactly what does NOT depend on R-WHILE:
--
--   * `residual-pp`  — the fp1 residual of a program-preserving interpreter
--                      satisfies the obligation (so the basis must too);
--   * `pp-unique`    — the obligation determines the function completely, so
--                      the residual and p⁺ are two programs for ONE
--                      specification: the comparison is like-for-like;
--   * `pp-injective` — a program-preserving program is injective whenever the
--                      source program is (the reversibility side of it);
--   * `classical⇒rev`— the classical criterion implies the reversible one
--                      whenever the basis is at least as expensive as p.
--
-- What is NOT proved here (and is refuted in RWhileJonesRevCE): that p⁺ is the
-- CHEAPEST program meeting the obligation.  See that module for why.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileJonesRev where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- The abstract setting.
--
--   D      data
--   P      programs
--   ⟦_⟧    semantics (the defined fragment: a total function, as in
--          RWhileRevProjPaper, where Kleene equality is modelled by ≡)
--   cost   the cost model (R-WHILE's `-steps` or `-work`; any ℕ-valued
--          measure will do — nothing below inspects it)
--   p2d    the program encoding ⌜·⌝
--   _⊗_    pairing

module Criterion
  (D P  : Set)
  (⟦_⟧  : P → D → D)
  (cost : P → D → ℕ)
  (p2d  : P → D)
  (_⊗_  : D → D → D)
  where

  ----------------------------------------------------------------------
  -- 1.  The obligation.
  --
  -- `PP q p` : q does p's job AND carries p's text to the output.  This is
  -- src/Simp.ml's `program_preserving` specification.

  PP : P → P → Set
  PP q p = ∀ d → ⟦ q ⟧ d ≡ p2d p ⊗ ⟦ p ⟧ d

  -- The obligation pins the FUNCTION down completely: any two programs
  -- meeting it are extensionally equal.  Hence the only freedom left among
  -- program-preserving programs is COST — which is exactly what a Jones-style
  -- criterion is supposed to compare.
  pp-unique : ∀ {q₁ q₂ p} → PP q₁ p → PP q₂ p → ∀ d → ⟦ q₁ ⟧ d ≡ ⟦ q₂ ⟧ d
  pp-unique h₁ h₂ d = trans (h₁ d) (sym (h₂ d))

  ----------------------------------------------------------------------
  -- 2.  Injectivity (the reversibility side of the obligation).

  ⊗-injectiveʳ : Set
  ⊗-injectiveʳ = ∀ {a x z} → a ⊗ x ≡ a ⊗ z → x ≡ z

  Injective : (D → D) → Set
  Injective f = ∀ {d₁ d₂} → f d₁ ≡ f d₂ → d₁ ≡ d₂

  -- A program-preserving version of an injective program is injective.
  pp-injective : ∀ {q p} → ⊗-injectiveʳ → PP q p
               → Injective ⟦ p ⟧ → Injective ⟦ q ⟧
  pp-injective {q} {p} ⊗inj ppq inj {d₁} {d₂} eq =
    inj (⊗inj (trans (sym (ppq d₁)) (trans eq (ppq d₂))))

  ----------------------------------------------------------------------
  -- 3.  The two criteria.

  -- classical: the residual is no more expensive than the source program.
  JonesOptimal : P → P → Set
  JonesOptimal r p = ∀ d → cost r d ≤ cost p d

  -- reversible: the residual is no more expensive than a basis `q` that
  -- CARRIES THE SAME OBLIGATION.  The `PP q p` component is not decoration:
  -- without it the criterion could be made trivially true by picking an
  -- arbitrarily wasteful basis.
  RevJonesOptimal : P → P → P → Set
  RevJonesOptimal r p q = PP q p × (∀ d → cost r d ≤ cost q d)

  -- The classical criterion is the stronger one whenever the basis is at
  -- least as expensive as p — which it always is when the basis is built by
  -- extending p (proved for R-WHILE in RWhileProgPresMin.ext-strictly-dearer).
  classical⇒rev : ∀ {r p q} → PP q p → (∀ d → cost p d ≤ cost q d)
                → JonesOptimal r p → RevJonesOptimal r p q
  classical⇒rev ppq mono jo = ppq , λ d → ≤-trans (jo d) (mono d)

  -- Changing the basis is monotone in the obvious way.
  rev-mono : ∀ {r p q q′} → PP q′ p → (∀ d → cost q d ≤ cost q′ d)
           → RevJonesOptimal r p q → RevJonesOptimal r p q′
  rev-mono ppq′ mono (_ , le) = ppq′ , λ d → ≤-trans (le d) (mono d)

  ----------------------------------------------------------------------
  -- 4.  WHY THE BASIS MUST CARRY THE OBLIGATION.
  --
  -- Under the two defining equations of a reversible Futamura projection
  -- (RWhileRevProjPaper's `def-rint` / `def-spec`) the fp1 residual is
  -- program-preserving.  So `residual ≤ p` compares programs with DIFFERENT
  -- specifications, while `residual ≤ q` for any program-preserving q
  -- compares two implementations of ONE specification.

  module Fp1
    (rint     : P)                                   -- program-preserving interpreter
    (spec     : P → D → P)                           -- the specialiser
    (def-rint : ∀ p d → ⟦ rint ⟧ (p2d p ⊗ d) ≡ p2d p ⊗ ⟦ p ⟧ d)
    (def-spec : ∀ q s d → ⟦ spec q s ⟧ d ≡ ⟦ q ⟧ (s ⊗ d))
    where

    residual : P → P
    residual p = spec rint (p2d p)

    -- THE KEY FACT: the residual inherits the interpreter's obligation.
    residual-pp : ∀ p → PP (residual p) p
    residual-pp p d = trans (def-spec rint (p2d p) d) (def-rint p d)

    -- Consequently the residual and ANY program-preserving basis compute the
    -- same function; the reversible criterion compares like with like.
    residual-same-spec : ∀ p q → PP q p → ∀ d → ⟦ residual p ⟧ d ≡ ⟦ q ⟧ d
    residual-same-spec p q ppq d = trans (residual-pp p d) (sym (ppq d))

    -- ... and it is injective whenever the source program is, so the residual
    -- of a reversible projection is itself a reversible program.
    residual-injective : ∀ p → ⊗-injectiveʳ → Injective ⟦ p ⟧
                       → Injective ⟦ residual p ⟧
    residual-injective p ⊗inj inj = pp-injective ⊗inj (residual-pp p) inj

    -- The basis p⁺ is singled out among all bases by ONE property: it meets
    -- the residual's obligation.  This is the precise sense in which
    -- "compare against p⁺" is not an arbitrary choice.  (It does NOT say p⁺
    -- is the cheapest such program; see RWhileJonesRevCE.)
    basis-adequate : ∀ p q → PP q p
                   → (∀ d → ⟦ residual p ⟧ d ≡ ⟦ q ⟧ d)
    basis-adequate = residual-same-spec
