{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Capstone: the HEADLINE machine-checked results of the development, collected
-- (and re-checked together) in one place for citation.  Importing this module
-- type-checks all the marquee theorems at once.  See AGDA_CORRESPONDENCE.md and
-- proofs/agda/README.md for the full module ↔ result map and the remaining
-- obligation (H2 for the full looping spec_av).
--
--   spec-correct          H1: ⟦spec p s⟧ d ≡ ⟦p⟧ (s·d) for the real AV machinery
--   d2p∘p2d / p2d-injective   residual Code program⇄data round-trip + injectivity (G4)
--   dProg∘t / transProg-injective  control-core program⇄data round-trip + injectivity (G4)
--   fp1U / specU-correct  fp1 unconditional for the real AV specialiser, unified value type
--   self-rep / specByProg-correct  H2's recursive core, non-closure (aeval is a data program)
--   hier-fp1/2/3          the Futamura hierarchy as proven theorems (non-closure instance)
--   gen-fp1/2/3, ⇓-det    the hierarchy with general first-class application (big-step), deterministic
--   mirrorP-reversible    a recursive (cata) program proven its-own-inverse at the relation level
--   reify-spec-correct    #5 step2 (constant family): a recursive specialiser emitting a RUNNABLE residual (H1)
--   prepend-spec-correct  #5 step2b: an INPUT-DEPENDENT residual (live `inp` + quoted static), H1
--   deadbranch-true/false  soundness of the residual simplifier's dead-branch elimination
--   recself-correct        option-2 lift: an OPTIMISING residual (interpreter eliminated, uses
--                          runtime input) in the recursion-capable relation; compilation recurses on ops
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileMain where

open import RWhileAVSpec   public using (spec-correct)
open import RWhileP2D      public using (d2p∘p2d; p2d-injective)
open import RWhileP2DProg  public using (dProg∘t; transProg-injective)
open import RWhileAVSelfApp public using (fp1U; specU-correct)
open import RWhileH2       public using (self-rep; specByProg-correct)
open import RWhileSimpSound public using (deadbranch-true; deadbranch-false)

-- the two hierarchy instances both export fp1/fp2/fp3; re-export with prefixes.
open import RWhileH2Hier  public using ()
  renaming (fp1 to hier-fp1; fp2 to hier-fp2; fp3 to hier-fp3; fp3-int to hier-fp3-int)
open import RWhileH2Hier2 public using (⇓-det)
  renaming (fp1-fwd to gen-fp1-fwd; fp1-bwd to gen-fp1-bwd; fp2 to gen-fp2; fp3 to gen-fp3)

-- a genuinely RECURSIVE (cata-defined) program that is its own inverse, proven
-- reversible at the relation level — recursion ∧ reversibility in one theorem.
open import RWhileH2HierRec public
  using (mirrorP; mirrorP-reversible; reify; reify-spec-correct
        ; prependSpec; prepend-spec-correct)

-- option 2: RevProj2Self's OPTIMISING residual (interpreter eliminated, uses
-- runtime input) lifted into the recursion-capable relation, with compilation a
-- genuine recursion over the source op-list.  `recself-correct` = the lifted
-- compileOps-correct; `recself-ex` a concrete machine-checked instance.
import RWhileH2HierRecSelf as RecSelf
open RecSelf.Witness public
  renaming (compileOps-correct to recself-correct; ex to recself-ex)
