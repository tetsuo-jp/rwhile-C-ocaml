{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The Futamura HIERARCHY (fp1, fp2, fp3), proved modularly.
--
-- For self-application all of {programs, data, residuals} live in one
-- universal type U, with `run : U → U → U` and a specialiser
-- `spec : U → U → U` (specialise program p to static input s).  The whole
-- hierarchy then follows from just two facts:
--
--   H1  spec-correct : run (spec p s) d ≡ run p ⟨ s , d ⟩
--          — the specialiser is correct (this is fp1, in general form).
--   H2  spec-impl    : run specP ⟨ p , s ⟩ ≡ spec p s
--          — the specialiser is itself a PROGRAM `specP` (self-application).
--
-- Given these:
--   target src = spec int src         [fp1]  run (target src) d ≡ run int ⟨src,d⟩
--   compiler   = spec specP int        [fp2]  run compiler src  ≡ target src
--   cogen      = spec specP specP      [fp3]  run cogen p        ≡ spec specP p
--
-- So fp2/fp3 are DERIVED (two `trans` steps each) from H1 + H2.  H1 is
-- realised concretely for the monovariant compiler in RWhileFutamura
-- (fp1 there: run (mix src) ≡ int src).  H2 — exhibiting a self-applicable
-- specialiser, i.e. one expressible in its own language — is the genuine
-- remaining obligation (the documented hard part of self-application);
-- here it is an explicit hypothesis, so this file certifies the LOGIC of the
-- hierarchy, not a particular self-applicable mix.
------------------------------------------------------------------------

module RWhileFutamura2 where

open import Relation.Binary.PropositionalEquality using (_≡_; trans)

module Hierarchy
  (U      : Set)                     -- one universal type: programs = data = residuals
  (⟨_,_⟩  : U → U → U)               -- pairing of (static . dynamic)
  (run    : U → U → U)               -- run a program on an input
  (spec   : U → U → U)               -- specialise program p to static input s
  (int    : U)                       -- the interpreter (a program)
  (specP  : U)                       -- the specialiser, as a program
  (spec-correct : ∀ p s d → run (spec p s) d ≡ run p ⟨ s , d ⟩)   -- H1
  (spec-impl    : ∀ p s   → run specP ⟨ p , s ⟩ ≡ spec p s)        -- H2
  where

  -- the three artefacts
  target : U → U
  target src = spec int src

  compiler : U
  compiler = spec specP int

  cogen : U
  cogen = spec specP specP

  ----------------------------------------------------------------------
  -- fp1: the specialised interpreter (target) computes the interpreter.
  fp1 : ∀ src d → run (target src) d ≡ run int ⟨ src , d ⟩
  fp1 src d = spec-correct int src d

  ----------------------------------------------------------------------
  -- fp2: the compiler maps each source to its target program.
  fp2 : ∀ src → run compiler src ≡ target src
  fp2 src = trans (spec-correct specP int src) (spec-impl int src)

  ----------------------------------------------------------------------
  -- fp3: the cogen maps each interpreter to its compiler.
  fp3 : ∀ p → run cogen p ≡ spec specP p
  fp3 p = trans (spec-correct specP specP p) (spec-impl specP p)

  -- in particular, cogen applied to the interpreter yields the compiler.
  fp3-int : run cogen int ≡ compiler
  fp3-int = fp3 int
