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
--   disp-eliminated        option-2: specialising to a static op DELETES the interpreter's runtime
--                          dispatch node (the real spec_av `=? Tag 'op`), proven dispatch-free + correct
--   fp2-fuel / runF-*      Tier-2 #5: a FUEL-INDEXED total interpreter coinciding with the big-step
--                          relation; fp1/fp2/fp3 lifted to fuel-level (the H2 fuel/partiality model)
--   worklist-correct       Tier-2 #5 (eng): the real spec_av WORKLIST (stack machine, begin/end markers)
--                          as a fuel-indexed machine computing the bottom-up fold (sound/complete/monotone)
--   optrev-invert          option-2: the OPTIMISED (interpreter-free) op-list residual is REVERSIBLE
--                          (inverse = inverted, reversed op-list) — optimisation ∧ reversibility
--   selfbridge             option-2 bridge: RevProj2Self (abstract) and HierRecSelf (relational) agree
--   full-integration       option-2: specialising a fold-of-dispatches interpreter removes BOTH the fold
--                          and the dispatch at once (flat, dispatch-free residual)
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
open RecSelf.Witness public using ()
  renaming (compileOps-correct to recself-correct; ex to recself-ex)

-- option 2: STATIC DISPATCH RESOLUTION — specialising the interpreter to a
-- static op deletes its runtime dispatch node (the real spec_av `=? Tag 'op`
-- mechanism), proven dispatch-free, correct, and non-vacuous.
import RWhileH2HierDispatch as Disp
open Disp.Witness public using ()
  renaming (spec-correct to disp-spec-correct; dispatch-eliminated to disp-eliminated;
            int-has-dispatch to disp-int-has-dispatch; ex to disp-ex)

-- option 2: OPTIMISATION ∧ REVERSIBILITY — the optimised (interpreter-free)
-- op-list residual is itself reversible; its inverse is the inverted, reversed
-- op-list (invList).  Witnessed by the boolean-toggle involution.
import RWhileOptRev as OptRev
open OptRev.Witness public using ()
  renaming (foldOps-invert to optrev-invert; ex to optrev-ex)

-- option 2: the TRANSLATION BRIDGE — RWhileRevProj2Self (abstract op-list) and
-- RWhileH2HierRecSelf (relational) agree: both compile to a residual computing
-- foldOps; the abstract residual's data IS the relational residual's value.
import RWhileSelfBridge as SelfBridge
open SelfBridge.Witness public using ()
  renaming (bridge to selfbridge; bridge-exact to selfbridge-exact)

-- option 2: the INTEGRATION — a realistic interpreter folds a DISPATCHING step
-- over an op-list; specialising removes BOTH overheads at once (fold unrolled to
-- a flat chain AND every dispatch resolved): `full` + `compileFull-dispatchFree`.
import RWhileH2HierFull as Full
open Full.Witness public using ()
  renaming (full to full-integration; compileFull-dispatchFree to full-dispatchFree;
            intStep-has-dispatch to full-int-has-dispatch; ex to full-ex)

-- Tier-2 #5: a FUEL-INDEXED total interpreter coinciding with the big-step
-- relation (sound+complete+monotone), lifting fp1/fp2/fp3 to fuel-level total
-- statements -- the fuel/partiality model for the looping self-application (H2).
open import RWhileH2Fuel public
  using (runF; runF-sound; runF-complete; runF-correct; fp1-fuel; fp2-fuel; fp3-fuel)

-- Tier-2 #5 (engineering): the real spec_av WORKLIST (SPEC-EXP-AV stack machine,
-- begin/end markers) concretised as a fuel-indexed abstract machine, proven to
-- compute the bottom-up fold (machine-correct) and fuel-sound/complete/monotone.
open import RWhileH2Worklist using (module Core)
open RWhileH2Worklist.Witness public
  using () renaming (machine-correct to worklist-correct; ex to worklist-ex
                    ; machineF-sound to worklist-sound; machineF-complete to worklist-complete)
