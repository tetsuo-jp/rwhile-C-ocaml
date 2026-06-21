{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2), step: model STATIC DISPATCH RESOLUTION — the very
-- mechanism the real spec_av uses (`if =? Tag 'ass …`, `if =? (hd PP) 'var …`):
-- an interpreter branches at RUNTIME on an operation tag; specialising it to a
-- STATIC op RESOLVES the branch and DELETES the dispatch node from the residual.
--
-- This is the optimising heart of #1 made concrete and self-contained (no change
-- to the RWhileH2HierRec foundation): the residual is provably DISPATCH-FREE
-- (the interpreter's runtime test is gone), still computes the interpreter's
-- result, and uses its runtime data input.  Complements RWhileH2HierRecSelf
-- (which eliminated the interpreter's FOLD over an op-list); here we eliminate
-- the interpreter's CASE over an op tag.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2HierDispatch where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- a two-element op alphabet (enough to make dispatch non-trivial).
data Op : Set where
  opA opB : Op

module Core (D : Set) (apply : Op → D → D) where

  -- a tiny first-order residual language: input, primitive application, and a
  -- runtime dispatch node selecting on the current op register.
  data Prog : Set where
    PInp  : Prog                  -- the runtime data
    PApp  : Op → Prog → Prog      -- apply a primitive op to a subresult
    PDisp : Prog → Prog → Prog    -- dispatch on the runtime op tag (opA→left, opB→right)

  -- evaluation: `o` is the runtime op register, `d` the runtime data.
  eval : Prog → Op → D → D
  eval PInp          o   d = d
  eval (PApp o' p)   o   d = apply o' (eval p o d)
  eval (PDisp pA pB) opA d = eval pA opA d
  eval (PDisp pA pB) opB d = eval pB opB d

  -- the INTERPRETER: reads the op at runtime and dispatches (contains PDisp).
  int : Prog
  int = PDisp (PApp opA PInp) (PApp opB PInp)

  int-correct : ∀ o d → eval int o d ≡ apply o d
  int-correct opA d = refl
  int-correct opB d = refl

  -- the SPECIALISER: with the op STATICALLY known, emit the resolved branch only.
  spec : Op → Prog
  spec o = PApp o PInp

  -- (1) the residual equals the interpreter specialised to that op.
  spec-correct : ∀ o d → eval (spec o) o d ≡ eval int o d
  spec-correct opA d = refl
  spec-correct opB d = refl

  -- (2) the residual no longer depends on the runtime op register (dispatch gone)
  --     yet still uses the runtime DATA: for ANY register r it computes apply o d.
  spec-anyreg : ∀ o r d → eval (spec o) r d ≡ apply o d
  spec-anyreg o r d = refl

  -- structural "is there a dispatch node?" predicate.
  dispatchFree : Prog → Bool
  dispatchFree PInp        = true
  dispatchFree (PApp _ p)  = dispatchFree p
  dispatchFree (PDisp _ _) = false

  -- (3) THE OPTIMISATION: the residual is dispatch-free …
  dispatch-eliminated : ∀ o → dispatchFree (spec o) ≡ true
  dispatch-eliminated o = refl

  -- … and this is non-vacuous: the interpreter genuinely HAD a dispatch to remove.
  int-has-dispatch : dispatchFree int ≡ false
  int-has-dispatch = refl

------------------------------------------------------------------------
-- Non-vacuous witness: D = ℕ, opA = successor, opB = identity.  The residual for
-- opA, run on data 0 with an ARBITRARY op register, yields 1 — the dispatch is
-- resolved and the data input is used.

module Witness where
  open import Data.Nat using (ℕ; suc; zero)
  open Core ℕ (λ { opA n → suc n ; opB n → n }) public

  ex : eval (spec opA) opB zero ≡ suc zero   -- register opB, yet computes opA's apply on 0
  ex = refl
