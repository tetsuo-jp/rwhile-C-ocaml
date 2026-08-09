{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- NON-VACUITY FOR BOTH REVERSIBLE DESIGNS — and the concrete refutation.
--
-- RWhileRevProjAlg (garbage on a dead branch of the residual's text) and
-- RWhileRevProjAlgPP (garbage emitted next to the residual) are parametric.
-- This module exhibits a model of each, discharging every hypothesis by
-- `refl`, so neither set of theorems is empty; and in the second model it
-- discharges `NonCyclicʳ` by a size count, turning the abstract
-- `fp4-fails` into an actual proof that
--
--     run cogen rspec ≢ cogen
--
-- for a specialiser that keeps its input.  The two models are deliberately
-- the SAME language except for where rspec puts the garbage — that is what
-- makes the comparison a comparison.
--
-- The source language is one operator `swp` (swap a pair), the same toy used
-- in RWhileFutamura; the interpreter keeps the program in its output, which
-- is what makes it injective.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileRevProjAlgInst where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (m≢1+n+m)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

import RWhileRevProjAlg
import RWhileRevProjAlgPP

------------------------------------------------------------------------
-- 1.  GARBAGE ON A DEAD BRANCH  (the `spec_av_rev` design).
------------------------------------------------------------------------

module DeadCode where

  data U : Set where
    pr    : U → U → U        -- pairing
    cls   : U → U → U        -- the clean residual  (mix p s)
    gb    : U → U → U        -- residual with garbage on a dead branch
    rspec : U                -- the specialiser, as a program
    rint  : U                -- the reversible interpreter, as a program
    swp   : U                -- a source program: swap a pair
    atom  : U

  swap : U → U
  swap (pr a b) = pr b a
  swap x        = x

  -- the source language's semantics (⟦·⟧_S)
  srcSem : U → U → U
  srcSem swp d = swap d
  srcSem _   d = d

  -- The universal `run`.  Only `cls` and `gb` recurse, both on a
  -- structurally smaller first argument, so `run` is total.
  run : U → U → U
  run (cls p s) d      = run p (pr s d)                -- the mix equation
  run (gb g r)  d      = run r d                       -- the branch is DEAD
  run rspec (pr p s)   = gb (pr p s) (cls p s)         -- garbage into the TEXT
  run rint  (pr p d)   = pr p (srcSem p d)             -- program-preserving
  run rspec _          = atom
  run rint  _          = atom
  run (pr a b) d       = d
  run swp d            = swap d
  run atom d           = d

  snd : U → U
  snd (pr a b) = b
  snd x        = x

  open RWhileRevProjAlg.Embed
         U run pr snd (λ a b → refl) srcSem rint rspec
         gb pr cls                       -- emb , γ (= keep the input) , mix
         (λ p d → refl)                  -- def-rint
         (λ g r d → refl)                -- dead
         (λ p s → refl)                  -- out
         (λ p s d → refl)                -- mix-eq
    public

  --------------------------------------------------------------------
  -- The artefacts, concretely: each is ONE embedding layer.
  _ : tgt swp ≡ gb (pr rint swp) (cls rint swp)
  _ = refl

  _ : cogen ≡ gb (pr rspec rspec) (cls rspec rspec)
  _ = refl

  -- the garbage is really there (the artefact is not the clean residual)
  garbage-present : ¬ (cogen ≡ cls rspec rspec)
  garbage-present ()

  -- … and the degeneracy holds ON THE NOSE anyway, garbage included.
  _ : run cogen rspec ≡ cogen
  _ = refl

  _ : run cogen rspec ≡ cogen
  _ = fp4-rev

  -- every level of the tower is that same one-layer term
  _ : tower 4 ≡ gb (pr rspec rspec) (cls rspec rspec)
  _ = refl

  -- the fp1 residual answers ⟨src , ⟦src⟧ d⟩ — code depth 1
  _ : ∀ a b → run (tgt swp) (pr a b) ≡ pr swp (pr b a)
  _ = λ a b → refl

  _ : ∀ a b → snd (run (run (run (tower 3) rint) swp) (pr a b)) ≡ pr b a
  _ = λ a b → tower-proj 3 swp (pr a b)

------------------------------------------------------------------------
-- 2.  GARBAGE IN THE OUTPUT  (the "keep the input" design).
--
-- Identical to §1 except for ONE clause of `run`: rspec pairs the garbage
-- onto the residual instead of embedding it.
------------------------------------------------------------------------

module OutPair where

  data U : Set where
    pr    : U → U → U
    cls   : U → U → U
    rspec : U
    rint  : U
    swp   : U
    atom  : U

  swap : U → U
  swap (pr a b) = pr b a
  swap x        = x

  srcSem : U → U → U
  srcSem swp d = swap d
  srcSem _   d = d

  run : U → U → U
  run (cls p s) d    = run p (pr s d)
  run rspec (pr p s) = pr (pr p s) (cls p s)          -- garbage into the OUTPUT
  run rint  (pr p d) = pr p (srcSem p d)
  run rspec _        = atom
  run rint  _        = atom
  run (pr a b) d     = d
  run swp d          = swap d
  run atom d         = d

  snd : U → U
  snd (pr a b) = b
  snd x        = x

  open RWhileRevProjAlgPP.OutGarbage
         U run pr snd (λ a b → refl) srcSem rint rspec
         pr cls                          -- γ (= keep the input) , mix
         (λ p d → refl)                  -- def-rint
         (λ p s → refl)                  -- out
         (λ p s d → refl)                -- mix-eq
    public

  --------------------------------------------------------------------
  -- The pairing is non-cyclic: `⟨a,b⟩ ≢ b`, by counting constructors.
  size : U → ℕ
  size (pr a b)  = suc (size a + size b)
  size (cls a b) = suc (size a + size b)
  size rspec     = 1
  size rint      = 1
  size swp       = 1
  size atom      = 1

  non-cyclic : NonCyclicʳ
  non-cyclic a b eq = m≢1+n+m (size b) {size a} (sym (cong size eq))

  --------------------------------------------------------------------
  -- THE VERDICT, concretely.

  -- what the fourth projection actually produces here:
  _ : run cogen rspec ≡ pr (pr rspec rspec) (cls rspec rspec)
  _ = refl

  -- it is NOT cogen …
  fp4-really-fails : ¬ (run cogen rspec ≡ cogen)
  fp4-really-fails = fp4-fails non-cyclic

  -- … but one projection restores it, exactly.
  _ : snd (run cogen rspec) ≡ cogen
  _ = refl

  _ : snd (run cogen rspec) ≡ cogen
  _ = fp4-clean

  -- the compiler's output is a pair too — the obligation is inherited
  _ : run comp swp ≡ pr (pr rint swp) (cls rint swp)
  _ = refl

  -- the tower still collapses when the projection is inserted at each level
  _ : tower 4 ≡ cogen
  _ = refl

  -- and, at any height, the answer is ⟨src , ⟦src⟧ d⟩: depth 1, n-free
  _ : ∀ a b → run (snd (run (snd (run (tower 3) rint)) swp)) (pr a b)
              ≡ pr swp (pr b a)
  _ = λ a b → answer-height-free 3 swp (pr a b)
