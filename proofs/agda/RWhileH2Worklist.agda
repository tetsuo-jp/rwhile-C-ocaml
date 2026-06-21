{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Tier-2 #5 (engineering): the real spec_av WORKLIST, concretised in the
-- fuel/partiality model.  spec_av's SPEC-EXP-AV / PAT-READ-ITER is an explicit
-- STACK MACHINE that folds an expression tree bottom-up with begin/end markers
-- (a worklist `Cd`, a result stack `RSt`, AV-CONS combining children) -- a
-- GENUINELY NON-STRUCTURAL loop (`from … until` over a worklist whose stack
-- grows/shrinks), not the structural recursion of RWhileH2HierRec's `cata`.
--
-- Here we model exactly that machine and run it with FUEL (total in `--safe`,
-- like RWhileH2Fuel.runF): a task stack of `doE e` (evaluate e) and `comb`
-- (combine the top two results = the begin/end marker), a result stack, iterated
-- one task per step.  We prove it computes the meta-level fold `metaFold` via a
-- machine RELATION (`_⟱_`), and fuel-index it (sound/complete/monotone), so the
-- looping worklist specialiser holds at the fuel level whenever fuel suffices.
-- Parametrised by the leaf/combine algebra (combR = AV-CONS bottom-up assembly).
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2Worklist where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- a tiny expression tree (the program/data structure spec_av folds).
data E : Set where
  leaf : ℕ → E
  node : E → E → E

module Core (R : Set) (leafR : ℕ → R) (combR : R → R → R) where

  -- the meta-level fold (the specification): assemble bottom-up.
  metaFold : E → R
  metaFold (leaf v)   = leafR v
  metaFold (node a b) = combR (metaFold a) (metaFold b)

  -- worklist tasks: evaluate an expr, or COMBINE the top two results (the
  -- begin/end marker that makes the traversal iterative rather than recursive).
  data Task : Set where
    doE  : E → Task
    comb : Task

  ----------------------------------------------------------------------
  -- the abstract machine as a (partial) RELATION on (task-stack, result-stack).
  infix 4 _⟱_
  data _⟱_ : (List Task × List R) → List R → Set where
    ⟱nil  : ∀ rs                          → ([] , rs) ⟱ rs
    ⟱leaf : ∀ {v ts rs r} → (ts , leafR v ∷ rs) ⟱ r
          → (doE (leaf v) ∷ ts , rs) ⟱ r
    ⟱node : ∀ {a b ts rs r} → (doE a ∷ doE b ∷ comb ∷ ts , rs) ⟱ r
          → (doE (node a b) ∷ ts , rs) ⟱ r
    ⟱comb : ∀ {x y ts rs r} → (ts , combR x y ∷ rs) ⟱ r
          → (comb ∷ ts , y ∷ x ∷ rs) ⟱ r

  -- CORRECTNESS of the worklist: pushing `doE e` onto any stacks reaches the
  -- continuation with `metaFold e` on the result stack (abstract-machine lemma).
  machine-spec : ∀ e ts rs {r} → (ts , metaFold e ∷ rs) ⟱ r → (doE e ∷ ts , rs) ⟱ r
  machine-spec (leaf v) ts rs h = ⟱leaf h
  machine-spec (node a b) ts rs h =
    ⟱node (machine-spec a (doE b ∷ comb ∷ ts) rs
            (machine-spec b (comb ∷ ts) (metaFold a ∷ rs)
              (⟱comb {x = metaFold a} {y = metaFold b} h)))

  -- the whole worklist run computes the fold.
  machine-correct : ∀ e → (doE e ∷ [] , []) ⟱ (metaFold e ∷ [])
  machine-correct e = machine-spec e [] [] (⟱nil (metaFold e ∷ []))

  ----------------------------------------------------------------------
  -- FUEL-INDEXED machine: total (`nothing` = out of fuel / malformed), one task
  -- per step -- the `from … until` worklist loop bounded by fuel (cf. runF).
  machineF : ℕ → List Task → List R → Maybe (List R)
  machineF zero    _                      _            = nothing
  machineF (suc n) []                     rs           = just rs
  machineF (suc n) (doE (leaf v)   ∷ ts)  rs           = machineF n ts (leafR v ∷ rs)
  machineF (suc n) (doE (node a b) ∷ ts)  rs           = machineF n (doE a ∷ doE b ∷ comb ∷ ts) rs
  machineF (suc n) (comb ∷ ts)            (y ∷ x ∷ rs) = machineF n ts (combR x y ∷ rs)
  machineF (suc n) (comb ∷ ts)            []           = nothing
  machineF (suc n) (comb ∷ ts)            (_ ∷ [])     = nothing

  -- SOUNDNESS: a `just` machine result is a valid relation run.
  machineF-sound : ∀ n ts rs {r} → machineF n ts rs ≡ just r → (ts , rs) ⟱ r
  machineF-sound zero ts rs ()
  machineF-sound (suc n) [] rs refl = ⟱nil rs
  machineF-sound (suc n) (doE (leaf v) ∷ ts) rs eq =
    ⟱leaf (machineF-sound n ts (leafR v ∷ rs) eq)
  machineF-sound (suc n) (doE (node a b) ∷ ts) rs eq =
    ⟱node (machineF-sound n (doE a ∷ doE b ∷ comb ∷ ts) rs eq)
  machineF-sound (suc n) (comb ∷ ts) (y ∷ x ∷ rs) eq =
    ⟱comb (machineF-sound n ts (combR x y ∷ rs) eq)
  machineF-sound (suc n) (comb ∷ ts) [] ()
  machineF-sound (suc n) (comb ∷ ts) (_ ∷ []) ()

  -- MONOTONICITY: more fuel preserves results.
  machineF-mono-≤ : ∀ {n m} → n ≤ m → ∀ ts rs {r}
                  → machineF n ts rs ≡ just r → machineF m ts rs ≡ just r
  machineF-mono-≤ z≤n ts rs ()
  machineF-mono-≤ {suc n} {suc m} (s≤s le) [] rs eq = eq
  machineF-mono-≤ {suc n} {suc m} (s≤s le) (doE (leaf v) ∷ ts) rs eq =
    machineF-mono-≤ le ts (leafR v ∷ rs) eq
  machineF-mono-≤ {suc n} {suc m} (s≤s le) (doE (node a b) ∷ ts) rs eq =
    machineF-mono-≤ le (doE a ∷ doE b ∷ comb ∷ ts) rs eq
  machineF-mono-≤ {suc n} {suc m} (s≤s le) (comb ∷ ts) (y ∷ x ∷ rs) eq =
    machineF-mono-≤ le ts (combR x y ∷ rs) eq
  machineF-mono-≤ {suc n} {suc m} (s≤s le) (comb ∷ ts) [] ()
  machineF-mono-≤ {suc n} {suc m} (s≤s le) (comb ∷ ts) (_ ∷ []) ()

  -- COMPLETENESS: every relation run terminates within some fuel (one task per
  -- step ⇒ no ⊔ needed; the loop is linear in the number of tasks).
  machineF-complete : ∀ {ts rs r} → (ts , rs) ⟱ r → Σ ℕ (λ n → machineF n ts rs ≡ just r)
  machineF-complete (⟱nil rs)  = suc zero , refl
  machineF-complete (⟱leaf d)  with machineF-complete d
  ... | n , e = suc n , e
  machineF-complete (⟱node d)  with machineF-complete d
  ... | n , e = suc n , e
  machineF-complete (⟱comb d)  with machineF-complete d
  ... | n , e = suc n , e

  -- the worklist, fuel-indexed, computes the fold within some finite fuel.
  machine-correct-fuel : ∀ e → Σ ℕ (λ n → machineF n (doE e ∷ []) [] ≡ just (metaFold e ∷ []))
  machine-correct-fuel e = machineF-complete (machine-correct e)

------------------------------------------------------------------------
-- Non-vacuous witness: R = E, combR = node, leafR = leaf -- the worklist
-- RECONSTRUCTS the tree bottom-up (metaFold = identity), modelling PAT-READ-ITER
-- rebuilding a (residual) structure via AV-CONS.

module Witness where
  open Core E leaf node public

  e0 : E
  e0 = node (leaf 1) (node (leaf 2) (leaf 3))

  -- the fuelled worklist rebuilds e0 exactly (metaFold e0 ≡ e0 definitionally).
  ex : Σ ℕ (λ n → machineF n (doE e0 ∷ []) [] ≡ just (e0 ∷ []))
  ex = machine-correct-fuel e0
