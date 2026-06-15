{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A machine-checked FIRST FUTAMURA PROJECTION for a small reversible
-- op-language (the ri_seq/swap object language used for R-WHILE's fp1).
--
-- The first Futamura projection specialises an interpreter to a source
-- program, yielding a COMPILED program in which the interpretive dispatch is
-- gone.  Here:
--   * Op            : the object language (a reversible `swap`, and `id`)
--   * int           : the interpreter — runs a List Op on a pair, with a
--                     per-op dispatch (appOp)
--   * Prim / run    : the residual language — a straight-line list of
--                     effects, with NO dispatch
--   * mix           : the specialiser — compiles a source `List Op` to a
--                     residual `List Prim`, removing `id`s and turning each
--                     dispatch into a primitive effect
--   * fp1           : run (mix src) ≡ int src         ← the projection, proved
--
-- This is the verified counterpart of the OCaml fp1 result
-- ([[spec_av]((ri_seq . src))] computes [ri_seq] with the dispatch removed).
------------------------------------------------------------------------

module RWhileFutamura where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

-- Object language (source) and residual primitives.  Neither depends on the
-- data type, so they live outside the data-parameterised section.
data Op   : Set where `swap `id : Op
data Prim : Set where doSwap     : Prim

-- The specialiser (mix) does not depend on the data type: compile a source to
-- a residual.  `id`s vanish; each `swap` dispatch becomes the effect `doSwap`.
mix : List Op → List Prim
mix []           = []
mix (`swap ∷ os) = doSwap ∷ mix os
mix (`id   ∷ os) = mix os

-- Specialisation shrinks code: the residual is no longer than the source.
mix-length-≤ : ∀ src → length (mix src) ≤ length src
mix-length-≤ []           = z≤n
mix-length-≤ (`swap ∷ os) = s≤s (mix-length-≤ os)
mix-length-≤ (`id   ∷ os) = ≤-suc (mix-length-≤ os)

module _ {A : Set} where

  ----------------------------------------------------------------------
  -- Interpreter: run a source program (List Op) on a pair, dispatching on
  -- each op.  `appOp` is the interpretive overhead the projection removes.

  appOp : Op → A × A → A × A
  appOp `swap (a , b) = (b , a)
  appOp `id    p       = p

  int : List Op → A × A → A × A
  int []       p = p
  int (o ∷ os) p = int os (appOp o p)

  ----------------------------------------------------------------------
  -- Residual language: a straight-line list of effects, NO op dispatch.

  runP : Prim → A × A → A × A
  runP doSwap (a , b) = (b , a)

  run : List Prim → A × A → A × A
  run []       p = p
  run (c ∷ cs) p = run cs (runP c p)

  ----------------------------------------------------------------------
  -- FIRST FUTAMURA PROJECTION: the compiled (residual) program computes
  -- exactly what the interpreter does.

  fp1 : ∀ src p → run (mix src) p ≡ int src p
  fp1 []           p       = refl
  fp1 (`swap ∷ os) (a , b) = fp1 os (b , a)
  fp1 (`id   ∷ os) p       = fp1 os p

  ----------------------------------------------------------------------
  -- Each residual primitive is reversible (doSwap is an involution); so the
  -- compiled program is reversible too — consistent with RWhileIL.il-revS for
  -- the residual reversible IL.

  runP-invol : ∀ c p → runP c (runP c p) ≡ p
  runP-invol doSwap (a , b) = refl
