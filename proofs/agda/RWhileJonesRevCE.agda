{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- WHAT p⁺ IS NOT: it is not the cheapest program meeting the obligation.
--
-- The natural wish, after defining reversible Jones optimality as
-- `residual ≤ p⁺`, is a lower-bound theorem saying that p⁺ is MINIMAL —
-- "every program that carries p's text to the output costs at least what p⁺
-- costs", which would make the basis canonical rather than merely adequate.
--
-- That statement is FALSE, and this module refutes it by exhibiting a model
-- of RWhileJonesRev.Criterion in which a program-preserving program is
-- strictly cheaper than p⁺.  The reason is structural, not an artefact of the
-- model: the obligation `PP q p` is EXTENSIONAL (it fixes the function
-- computed — see `pp-unique`) while cost is not determined by the function.
-- If `p` wastes work — and the subject program of a self-interpreter may
-- waste as much as one likes — then a program that computes ⟨⌜p⌝, ⟦p⟧ d⟩ by
-- some cleverer route beats `p⁺ = p followed by an emit`, which pays p's
-- waste.
--
-- Formally: any minimality claim for p⁺ would entail a lower bound on the
-- cost of computing the FUNCTION ⟨⌜p⌝, ⟦p⟧ ·⟩, i.e. a complexity-theoretic
-- lower bound for an arbitrary computable function.  No such bound follows
-- from the definition of the projection, so none is provable here.
--
-- What survives is:
--   * p⁺ is minimal *as an extension of p*: it adds a constant and nothing
--     else (RWhileProgPres.pp-cost-exact, RWhileProgPresMin);
--   * p⁺ is adequate: it meets exactly the residual's obligation
--     (RWhileJonesRev.Fp1.basis-adequate).
--
-- This module also refutes the converse of `classical⇒rev`: the reversible
-- criterion does not imply the classical one.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileJonesRevCE where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import RWhileJonesRev

------------------------------------------------------------------------
-- A four-program model.  `slow` is a wasteful identity; `ppSlow` is its p⁺
-- (run slow, then emit the pair); `fastPP` computes the very same function
-- without paying slow's waste; `resid` is a residual sitting between the two.

data Pr : Set where
  slow ppSlow fastPP resid : Pr

data Dat : Set where
  base  : ℕ  → Dat
  code  : Pr → Dat            -- the program encoding ⌜·⌝ (injective: a ctor)
  _⊗_   : Dat → Dat → Dat     -- pairing

sem : Pr → Dat → Dat
sem slow   d = d                    -- a (wasteful) identity
sem ppSlow d = code slow ⊗ d        -- = ⟨⌜slow⌝ , ⟦slow⟧ d⟩
sem fastPP d = code slow ⊗ d        -- the same function ...
sem resid  d = code slow ⊗ d        -- ... and again

-- The cost model.  `ppSlow` = slow (100) + an emit of 8, exactly the shape
-- RWhileProgPres builds; `fastPP` reaches the same value in 2.
cst : Pr → Dat → ℕ
cst slow   _ = 100
cst ppSlow _ = 108
cst fastPP _ = 2
cst resid  _ = 104

open Criterion Dat Pr sem cst code _⊗_

------------------------------------------------------------------------
-- All three of ppSlow, fastPP, resid meet slow's obligation.

ppSlow-pp : PP ppSlow slow
ppSlow-pp d = refl

fastPP-pp : PP fastPP slow
fastPP-pp d = refl

resid-pp : PP resid slow
resid-pp d = refl

-- Sanity: the obligation really does fix the function (`pp-unique` applied).
ppSlow≗fastPP : ∀ d → sem ppSlow d ≡ sem fastPP d
ppSlow≗fastPP = pp-unique {ppSlow} {fastPP} {slow} ppSlow-pp fastPP-pp

------------------------------------------------------------------------
-- 1.  p⁺ IS NOT COST-MINIMAL among the programs meeting the obligation.

p⁺-not-minimal : ¬ (∀ q → PP q slow → ∀ d → cst ppSlow d ≤ cst q d)
p⁺-not-minimal h =
  toWitnessFalse {a? = 108 ≤? 2} tt (h fastPP fastPP-pp (base 0))

------------------------------------------------------------------------
-- 2.  The reversible criterion does NOT imply the classical one.
--     `resid` (104) is within p⁺ (108) but beyond p (100).

resid-rev-optimal : RevJonesOptimal resid slow ppSlow
resid-rev-optimal = resid-pp , λ d → toWitness {a? = 104 ≤? 108} tt

resid-not-classical : ¬ (JonesOptimal resid slow)
resid-not-classical h = toWitnessFalse {a? = 104 ≤? 100} tt (h (base 0))

------------------------------------------------------------------------
-- 3.  Neither criterion is vacuous: `fastPP` (2) meets the classical
--     criterion against `slow` (100), hence also the reversible one.

fastPP-classical : JonesOptimal fastPP slow
fastPP-classical d = toWitness {a? = 2 ≤? 100} tt

fastPP-rev : RevJonesOptimal fastPP slow ppSlow
fastPP-rev = classical⇒rev {fastPP} {slow} {ppSlow} ppSlow-pp
                           (λ d → toWitness {a? = 100 ≤? 108} tt) fastPP-classical
