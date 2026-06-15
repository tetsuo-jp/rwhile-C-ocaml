{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The REVERSIBLE first Futamura projection.
--
-- For the reversible op-language of RWhileFutamura (`swap`/`id` → `doSwap`),
-- specialising a REVERSIBLE interpreter to a source yields a REVERSIBLE
-- compiled program, and the projection commutes with inversion.  Inversion of
-- a program reverses the sequence and inverts each step (here every op/prim is
-- an involution, so `invOp`/`invPrim` are identities; we keep them to mirror
-- the general reverse-and-invert structure of R-WHILE's `inv`).
--
-- Proved (all --safe):
--   mix-commute   : mix (invSrc src) ≡ invComp (mix src)
--                     -- inversion COMMUTES with the projection
--   run-rev       : run (invComp cs) (run cs p) ≡ p
--                     -- every compiled program is reversible
--   int-rev       : int (invSrc src) (int src p) ≡ p
--                     -- the interpreter is reversible
--   reversible-fp1: run (mix (invSrc src)) (run (mix src) p) ≡ p
--                     -- compiling the inverse source inverts the compiled
--                        program (the reversible projection), combining the above
------------------------------------------------------------------------

module RWhileRevFutamura where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import RWhileFutamura

------------------------------------------------------------------------
-- Inversion of sources and residuals: reverse the sequence, invert each step.

invOp : Op → Op
invOp `swap = `swap
invOp `id   = `id

invPrim : Prim → Prim
invPrim doSwap = doSwap

invSrc : List Op → List Op
invSrc []       = []
invSrc (o ∷ os) = invSrc os ++ (invOp o ∷ [])

invComp : List Prim → List Prim
invComp []       = []
invComp (c ∷ cs) = invComp cs ++ (invPrim c ∷ [])

------------------------------------------------------------------------
-- mix distributes over ++, hence inversion COMMUTES with the projection.

mix-++ : ∀ xs ys → mix (xs ++ ys) ≡ mix xs ++ mix ys
mix-++ []           ys = refl
mix-++ (`swap ∷ xs) ys = cong (doSwap ∷_) (mix-++ xs ys)
mix-++ (`id   ∷ xs) ys = mix-++ xs ys

mix-commute : ∀ src → mix (invSrc src) ≡ invComp (mix src)
mix-commute []           = refl
mix-commute (`swap ∷ os) =
  trans (mix-++ (invSrc os) (`swap ∷ []))
        (cong (_++ (doSwap ∷ [])) (mix-commute os))
mix-commute (`id   ∷ os) =
  trans (mix-++ (invSrc os) (`id ∷ []))
        (trans (++-identityʳ (mix (invSrc os))) (mix-commute os))

------------------------------------------------------------------------
-- Reversibility of the residual and the interpreter (depend on the data type).

module _ {A : Set} where

  run-append : ∀ xs ys (p : A × A) → run (xs ++ ys) p ≡ run ys (run xs p)
  run-append []       ys p = refl
  run-append (c ∷ xs) ys p = run-append xs ys (runP c p)

  -- every compiled program is reversible
  run-rev : ∀ cs (p : A × A) → run (invComp cs) (run cs p) ≡ p
  run-rev []            p = refl
  run-rev (doSwap ∷ cs) p
    rewrite run-append (invComp cs) (doSwap ∷ []) (run cs (runP doSwap p))
          | run-rev cs (runP doSwap p)
    = runP-invol doSwap p

  int-append : ∀ xs ys (p : A × A) → int (xs ++ ys) p ≡ int ys (int xs p)
  int-append []       ys p = refl
  int-append (o ∷ xs) ys p = int-append xs ys (appOp o p)

  op-invol : ∀ o (p : A × A) → appOp (invOp o) (appOp o p) ≡ p
  op-invol `swap (a , b) = refl
  op-invol `id    p      = refl

  -- the interpreter is reversible
  int-rev : ∀ src (p : A × A) → int (invSrc src) (int src p) ≡ p
  int-rev []       p = refl
  int-rev (o ∷ os) p
    rewrite int-append (invSrc os) (invOp o ∷ []) (int os (appOp o p))
          | int-rev os (appOp o p)
    = op-invol o p

  ----------------------------------------------------------------------
  -- THE REVERSIBLE FIRST FUTAMURA PROJECTION: compiling the inverse source
  -- inverts the compiled program (inversion commutes with the projection AND
  -- the residual is reversible).

  reversible-fp1 : ∀ src (p : A × A) → run (mix (invSrc src)) (run (mix src) p) ≡ p
  reversible-fp1 src p rewrite mix-commute src = run-rev (mix src) p
