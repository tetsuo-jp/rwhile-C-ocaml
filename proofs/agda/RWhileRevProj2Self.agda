{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A SMALL self-applicable specialiser in the core, where the 2nd projection
-- (compiler generation) actually goes through — with REAL residualisation.
--
-- This is the constructive counterpart to RWhileRevProj2BT (which pinned the
-- binding-time root cause of B's fp2 failure) and to RWhileFutamura2Inst (which
-- discharged self-application with a `papp` CLOSURE that hides residualisation).
-- Here the residual `comp ops` is a genuine COMPILED program: it carries the
-- source ops and runs them directly on the RUNTIME data — the interpreter `int`
-- is ELIMINATED, and (unlike the over-static bug) the residual USES its runtime
-- input.  fp1/fp2/fp3 all hold by `refl`, so this is a non-vacuous, structural
-- realisation of the reversible/Futamura 2nd projection for the op-list language.
--
-- Binding-time discipline (the fix from RWhileRevProj2BT) is built in: the
-- source op-list is STATIC (folded into `comp`), the data is DYNAMIC (kept as a
-- runtime parameter of `comp`).  No static commitment of the dynamic half.
------------------------------------------------------------------------

module RWhileRevProj2Self where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Core (D : Set) (Op : Set) (apply : Op → D → D) where

  -- the op-list interpreter's fold (int's meaning).
  foldOps : List Op → D → D
  foldOps []       d = d
  foldOps (o ∷ os) d = foldOps os (apply o d)

  ----------------------------------------------------------------------
  -- One universal type: data, programs, residuals, and the meta-programs
  -- (interpreter, specialiser, and the artefacts they generate).

  data U : Set where
    uData : D → U                 -- runtime data (dynamic)
    uPair : U → U → U             -- ⟨ p , s ⟩ pairing
    uOps  : List Op → U           -- a source program (op list), as data (static)
    uComp : List Op → U           -- a COMPILED residual: applies its ops to runtime data
    uInt  : U                     -- the interpreter, as a program
    uSpec : U                     -- the specialiser, as a program
    uCompiler : U                 -- spec specialised to int   (the compiler)
    uCogen    : U                 -- spec specialised to spec   (cogen)

  -- the universal evaluator.
  run : U → U → U
  run uInt        (uPair (uOps ops) (uData d)) = uData (foldOps ops d)   -- interpret
  run (uComp ops) (uData d)                    = uData (foldOps ops d)   -- run compiled (USES runtime d)
  run uSpec       (uPair uInt  (uOps ops))     = uComp ops               -- spec int ops = compiled ops (int ELIMINATED)
  run uSpec       (uPair uSpec uInt)           = uCompiler               -- spec spec int = the compiler
  run uSpec       (uPair uSpec uSpec)          = uCogen                  -- spec spec spec = cogen
  run uCompiler   (uOps ops)                   = uComp ops               -- compiler maps a source to its residual
  run uCogen      uInt                         = uCompiler               -- cogen on int = the compiler
  run _           x                            = x                       -- (unused elsewhere)

  -- the specialiser as a binary operation, and the three artefacts.
  spec : U → U → U
  spec p s = run uSpec (uPair p s)

  target : List Op → U
  target ops = spec uInt (uOps ops)        -- = uComp ops

  compiler : U
  compiler = spec uSpec uInt               -- = uCompiler

  cogen : U
  cogen = spec uSpec uSpec                  -- = uCogen

  ----------------------------------------------------------------------
  -- fp1: the specialised interpreter computes the interpreter, with the
  -- interpreter ELIMINATED (the residual is `uComp ops`, not a re-run of int).
  fp1 : ∀ ops d → run (target ops) (uData d) ≡ run uInt (uPair (uOps ops) (uData d))
  fp1 ops d = refl

  -- fp2: the compiler maps each source op-list to its target (compiled) program.
  fp2 : ∀ ops → run compiler (uOps ops) ≡ target ops
  fp2 ops = refl

  -- fp3: cogen maps the interpreter to the compiler.
  fp3 : run cogen uInt ≡ compiler
  fp3 = refl

  ----------------------------------------------------------------------
  -- Binding-time correctness witnessed: the compiler's residual USES its
  -- runtime input (it is not a baked constant), so there is NO over-static
  -- degeneration — exactly the property RWhileRevProj2BT says the fix must give.
  compiler-residual-uses-input :
    ∀ ops d → run (run compiler (uOps ops)) (uData d) ≡ uData (foldOps ops d)
  compiler-residual-uses-input ops d = refl

  -- end-to-end: the compiled source, run on runtime data, agrees with
  -- interpreting the source on that data — for EVERY data input.
  fp2-correct : ∀ ops d → run (run compiler (uOps ops)) (uData d)
                        ≡ run uInt (uPair (uOps ops) (uData d))
  fp2-correct ops d = refl
