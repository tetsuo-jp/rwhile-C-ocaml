{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2), step: OPTIMISATION ∧ REVERSIBILITY — the paper's two
-- central themes in one theorem.  RWhileH2HierRecSelf / RWhileRevProj2Self show
-- the optimising residual (interpreter ELIMINATED) computes the op-list fold;
-- here we add that this optimised residual is REVERSIBLE: if every primitive op
-- has an inverse op, then running the compiled fold and then the compiled
-- INVERSE fold (the inverted ops in reversed order) recovers the input.
--
-- So the reversible specialiser does not merely preserve reversibility of the
-- source — its OPTIMISED output (no interpreter, no dispatch) is itself a
-- reversible program, with a syntactically-described inverse (invList).
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileOptRev where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Core (D : Set) (Op : Set) (apply : Op → D → D)
            (invOp : Op → Op)
            (apply-inv : ∀ o d → apply (invOp o) (apply o d) ≡ d) where

  -- the op-list interpreter's fold (= the optimised residual's meaning).
  foldOps : List Op → D → D
  foldOps []       d = d
  foldOps (o ∷ os) d = foldOps os (apply o d)

  -- folding a concatenation = folding the second list over the first's result.
  foldOps-++ : ∀ xs ys d → foldOps (xs ++ ys) d ≡ foldOps ys (foldOps xs d)
  foldOps-++ []       ys d = refl
  foldOps-++ (x ∷ xs) ys d = foldOps-++ xs ys (apply x d)

  -- the inverse program: each op inverted, in REVERSED order.
  invList : List Op → List Op
  invList []       = []
  invList (o ∷ os) = invList os ++ (invOp o ∷ [])

  -- REVERSIBILITY of the optimised residual: compiled fold then compiled inverse
  -- fold is the identity.  (Optimisation is orthogonal — `foldOps` IS the
  -- interpreter-free residual semantics of RWhileH2HierRecSelf.compileOps.)
  foldOps-invert : ∀ ops d → foldOps (invList ops) (foldOps ops d) ≡ d
  foldOps-invert []       d = refl
  foldOps-invert (o ∷ os) d
    rewrite foldOps-++ (invList os) (invOp o ∷ []) (foldOps os (apply o d))
          | foldOps-invert os (apply o d)
    = apply-inv o d

------------------------------------------------------------------------
-- Non-vacuous witness with a GENUINE involution: D = Bool, one op = boolean
-- toggle (apply = not), self-inverse.  Three toggles then their inverse recover
-- the input — the optimised residual round-trips.

module Witness where
  open import Data.Bool using (Bool; true; false; not)
  open import Data.Unit using (⊤; tt)

  not-inv : ∀ b → not (not b) ≡ b
  not-inv true  = refl
  not-inv false = refl

  open Core Bool ⊤ (λ _ b → not b) (λ _ → tt) (λ _ b → not-inv b) public

  ex : foldOps (invList (tt ∷ tt ∷ tt ∷ [])) (foldOps (tt ∷ tt ∷ tt ∷ []) false) ≡ false
  ex = foldOps-invert (tt ∷ tt ∷ tt ∷ []) false
