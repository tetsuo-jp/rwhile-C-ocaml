{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2), the INTEGRATION: a realistic interpreter has BOTH
-- overheads at once — it FOLDS over an op-list AND DISPATCHES on each op's tag.
-- Specialising it to a STATIC op-list must remove BOTH: unroll the fold into a
-- flat chain AND resolve every per-step dispatch.  This unifies
-- RWhileH2HierRecSelf (fold elimination) and RWhileH2HierDispatch (dispatch
-- elimination) into one residual and one theorem.
--
--   intFold ops d   = fold the DISPATCHING step `intStep` over ops  (fold ∘ dispatch)
--   compileFull ops = a flat chain of resolved applications          (neither)
--
-- We prove the residual computes the interpreter's result for ANY runtime op
-- register (dispatch gone), is structurally dispatch-free (no `disp` node), and
-- — being a finite chain built at compile time — contains no fold/loop.  The
-- per-step `intStep` genuinely dispatches (`intStep-has-dispatch`), so the
-- elimination is non-vacuous.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2HierFull where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import RWhileH2HierDispatch using (Op; opA; opB)

module Core (D : Set) (apply : Op → D → D) where

  -- a residual language with a flat chain link (appP) AND a runtime dispatch (disp).
  data P : Set where
    inp  : P
    appP : Op → P → P        -- apply op, THEN run the rest:  eval (appP o p) r d = eval p r (apply o d)
    disp : P → P → P         -- dispatch on the runtime op register

  eval : P → Op → D → D
  eval inp        r   d = d
  eval (appP o p) r   d = eval p r (apply o d)
  eval (disp a b) opA d = eval a opA d
  eval (disp a b) opB d = eval b opB d

  -- the interpreter's meaning: fold the ops over the data.
  foldOps : List Op → D → D
  foldOps []       d = d
  foldOps (o ∷ os) d = foldOps os (apply o d)

  -- the per-element interpreter STEP: dispatch on the runtime op tag.
  intStep : P
  intStep = disp (appP opA inp) (appP opB inp)

  intStep-correct : ∀ o d → eval intStep o d ≡ apply o d
  intStep-correct opA d = refl
  intStep-correct opB d = refl

  -- the UNSPECIALISED interpreter: fold the DISPATCHING step over the op-list
  -- (this is the realistic interpreter — a fold of dispatches).
  intFold : List Op → D → D
  intFold []       d = d
  intFold (o ∷ os) d = intFold os (eval intStep o d)

  intFold≡foldOps : ∀ ops d → intFold ops d ≡ foldOps ops d
  intFold≡foldOps []       d = refl
  intFold≡foldOps (o ∷ os) d rewrite intStep-correct o d = intFold≡foldOps os (apply o d)

  -- the COMPILER: unroll the fold and resolve each dispatch → a flat chain.
  compileFull : List Op → P
  compileFull []       = inp
  compileFull (o ∷ os) = appP o (compileFull os)

  -- (1) correctness: the flat residual computes the interpreter's result for ANY
  --     runtime register r (dispatch resolved → register irrelevant).
  compileFull-correct : ∀ ops r d → eval (compileFull ops) r d ≡ foldOps ops d
  compileFull-correct []       r d = refl
  compileFull-correct (o ∷ os) r d = compileFull-correct os r (apply o d)

  -- structural dispatch-freeness.
  dispatchFree : P → Bool
  dispatchFree inp        = true
  dispatchFree (appP _ p) = dispatchFree p
  dispatchFree (disp _ _) = false

  -- (2) BOTH overheads gone: the residual is a flat chain (fold unrolled, no
  --     loop) AND dispatch-free (every per-step disp resolved).
  compileFull-dispatchFree : ∀ ops → dispatchFree (compileFull ops) ≡ true
  compileFull-dispatchFree []       = refl
  compileFull-dispatchFree (o ∷ os) = compileFull-dispatchFree os

  -- non-vacuous: the interpreter step genuinely HAD a dispatch to remove.
  intStep-has-dispatch : dispatchFree intStep ≡ false
  intStep-has-dispatch = refl

  -- (3) THE INTEGRATION: the flat, dispatch-free residual equals the realistic
  --     interpreter (fold-of-dispatches) — both overheads removed in one go.
  full : ∀ ops r d → eval (compileFull ops) r d ≡ intFold ops d
  full ops r d = trans (compileFull-correct ops r d) (sym (intFold≡foldOps ops d))

------------------------------------------------------------------------
-- Non-vacuous witness: D = ℕ, opA = successor, opB = identity.

module Witness where
  open import Data.Nat using (ℕ; suc; zero)
  open Core ℕ (λ { opA n → suc n ; opB n → n }) public

  -- compiling [opA, opA] gives a flat dispatch-free residual computing +2,
  -- agreeing with the fold-of-dispatches interpreter, for any register.
  ex : eval (compileFull (opA ∷ opA ∷ [])) opB zero ≡ intFold (opA ∷ opA ∷ []) zero
  ex = full (opA ∷ opA ∷ []) opB zero
