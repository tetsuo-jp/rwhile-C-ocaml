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
--   specByProg-H1         fp1 for the SELF-REPRESENTED specialiser (H2-core ∘ H1, data program)
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
--   worklist-spec-sound    Tier-2 #5 (eng2): that worklist carrying the REAL AV algebra (avCons/avHd/avTl)
--                          assembles AV residuals that are γ-sound w.r.t. concrete eval (partial-static)
--   Core.worklist-store-sound  Tier-2 #5 (eng3): a PARTIAL-STATIC MULTI-SLOT store (each slot an independent
--                          AV); under consistency the worklist residual is γ-sound (store-ex-sound = witness)
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
open import RWhileH2       public using (self-rep; specByProg-correct; specByProg-H1)
open import RWhileSimpSound public using (deadbranch-true; deadbranch-false)

-- the two hierarchy instances both export fp1/fp2/fp3; re-export with prefixes.
open import RWhileH2Hier  public using ()
  renaming (fp1 to hier-fp1; fp2 to hier-fp2; fp3 to hier-fp3; fp3-int to hier-fp3-int)
open import RWhileH2Hier2 public using (⇓-det)
  renaming (fp1-fwd to gen-fp1-fwd; fp1-bwd to gen-fp1-bwd; fp2 to gen-fp2; fp3 to gen-fp3)

-- an OPTIMISING (non-trivial, constant-folding) specialiser instantiating the
-- single-U total-run hierarchy: the FULL fp1/fp2/fp3 hold for a self-applicable
-- spec that folds away the interpreter's projections (not embed-and-apply).
open import RWhileH2HierOpt public using (spec-impl)
  renaming (spec-correct to opt-spec-correct; fp1 to opt-fp1; fp2 to opt-fp2; fp3 to opt-fp3)

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

-- Tier-2 #5 (engineering, step 2): the worklist carrying the REAL AV algebra
-- (avCons/avHd/avTl), assembling AV residuals that are γ-sound w.r.t. concrete
-- evaluation -- spec_av's looping AV specialiser, concretised and verified.
open import RWhileH2WorklistAV public
  using (avEval; avEval-sound; worklist-spec-sound; worklist-fuel-sound)

-- Tier-2 #5 (engineering, last piece): the PARTIAL-STATIC MULTI-SLOT store --
-- each slot an independent AV (static or dynamic); under a consistency condition
-- (static slots match the runtime store) the worklist residual is γ-sound.
open import RWhileH2WorklistStore public using (Consistent; cSlot; cSlot-sound; module Core)
open RWhileH2WorklistStore.Witness public
  using () renaming (residual to store-residual; sound to store-ex-sound; consistent to store-consistent)

-- VERIFIED BRIDGE to the implementation's wire format: encEx / parseEx mirror
-- Program2DataRwhile.transExp / d_exp, the round trip parseEx (encEx e) ≡ just e
-- makes the model↔implementation correspondence a THEOREM, and `wire-sound`
-- composes it with the worklist AV specialiser's γ-soundness.
open import RWhileSpecAVWire public
  using (encEx; parseEx; specWire)
  renaming (parse-enc to wire-parse-enc; wire-sound to wire-spec-sound; bridge to wire-bridge)

-- The wire bridge extended to the WHOLE AST: patterns, commands and programs.
-- The round trips parsePat/parseCom/parseProg ∘ enc ≡ just make the full
-- AST ↔ implementation wire format (transPat/transCom/transProgram ↔
-- d_pat/d_com/data2program) a THEOREM — the syntactic half of a meaning-
-- preserving translation.
open import RWhileSpecAVWireCom public
  using ( encPat; parsePat; parse-enc-pat
        ; encCom; parseCom; parse-enc-com
        ; encProg; parseProg; parse-enc-prog
        ; ass-exp-sound )

-- 案1-B (Agda-first): the LOOP binding-time decision for the optimising
-- specialiser.  comp2's second obstruction (spec_av's 'lcheck '41) is that the
-- 'loop handler unrolls on the ENTRY test's binding time alone; once the inner
-- interpreter unrolls, a static-entry/dynamic-exit loop gets stuck.  This proves
-- the correct rule: a test's static truth is γ-sound, a dynamic exit ALWAYS
-- forces residualisation, and the entry-only predicate is wrong on exactly the
-- '41 scenario -- the verified blueprint for the implementation fix.
open import RWhileLoopBTA public
  using ( staticTruth; staticTruth-sound; unrollable
        ; exit-dynamic-forces-residual; bug-static-entry-dynamic-exit
        ; unroll-step-sound )

-- 案1-B step (a): the loop the decision RESIDUALISES is a reversible R-WHILE loop
-- (a `loop` of RWhileRevFull, so its entry/exit-swapped inversion is sound and
-- involutive) -- residualising preserves reversibility; the implementation only
-- has to emit this shape.
open import RWhileLoopBTARev public
  using (resLoop; resLoop-inv; resLoop-reversible; resLoop-inv-inv
        ; constEntry-no-iter)

-- 案1-(2) (Agda-first): the OFFLINE binding-time analysis blueprint for the
-- "real fp2" (comp2 < |spec|).  comp2's REMAINING obstruction (after the loop
-- fix above) is the OVER-STATIC binding-time bug: spec_av.rwhile:1051 tags the
-- source unconditionally 'S, freezing a slot that is dynamic under self-
-- application.  These five stages prove the diagnosis and the fix as theorems.
--
-- stage 1 -- the bug IS a binding-time congruence violation: a fully-static AV is
-- ρ-independent (static-stability), so no static AV can soundly abstract a dynamic
-- slot (over-commit-unsound); the fix `mkAV` never freezes a dynamic BT to `S`
-- (mkAV-dyn-nonstatic); the honest offline `spec2` is sound and congruent.
open import RWhileOfflineBTA public
  using ( static-stable; over-commit-unsound; no-static-identity
        ; mkAV; mkAV-dyn-nonstatic; spec2; spec2-sound; spec2-static )

-- stage 2 -- the self-application step: generalise the static source to an AV
-- (which may be symbolic).  Pass-through `spec2g` is sound for ANY source
-- (spec2g-sound); fp1 is its static instance (spec2≡spec2g); the :1051 freeze is
-- invisible on static sources (fp1 green) but UNSOUND on symbolic ones (the fp2
-- failure) -- spec2bug-ok-on-static / spec2bug-wrong-on-symbolic.
open import RWhileOfflineBTA2 public
  using ( spec2g; spec2g-sound; spec2≡spec2g
        ; spec2bug; spec2bug-ok-on-static; spec2bug-wrong-on-symbolic )

-- stage 3 -- the Futamura GAIN: a fully-static subexpression collapses to a
-- single leaf (gain); static dispatch is resolved, dynamic parts survive as holes.
open import RWhileOfflineBTA3 public
  using ( gain; dispatch-resolved; dyn-survives )

-- stage 4 -- the two-stage comp2 (the fp2 compiler) with the Futamura fp2 equation
-- (compile ∘ generate = eval); the correct compiler keeps its source symbolic, and
-- freezing it at stage 1 is unsound.
open import RWhileOfflineBTA4 public
  using ( spec1; spec1-sound; compile; fp2-eq
        ; spec1-keeps-source-symbolic; spec1bug-wrong-on-source )

-- stage 5 -- the three-stage cogen (fp3) with the Futamura fp3 equation
-- (compile ∘ generate ∘ gen = eval); the correct cogen keeps the interpreter
-- symbolic, and freezing it is unsound.
open import RWhileOfflineBTA5 public
  using ( gen; gen-sound; fp3-eq
        ; gen-keeps-int-symbolic; genbug-wrong-on-int )

-- stage 6 -- the production-faithful fix locus: the observed `('val.'swap)` embed is
-- AV-LIFT of a static leaf (prodThen-car-const); the BT-driven fix is fp1-identical
-- under 'S (fix-agrees-on-fp1) and residualises under 'D (fixThen-car-tracks).
open import RWhileOfflineBTA6 public
  using ( prodThen; prodThen-car-const; prodThen-car-unsound
        ; fixThen; fix-agrees-on-fp1; fixThen-car-tracks; fixThen-car-nonstatic )

-- stage 7 -- DISPATCH preservation: with an opcode dispatch (`if x2 = 'swap …`), the
-- correct compiler dispatches (comp-swap ≠ comp-id, each correct by spec1-sound),
-- while freezing the opcode collapses the dispatch and is wrong (compbug-wrong) --
-- exactly the comp2 symptom, closed.
open import RWhileOfflineBTA7 public
  using ( dispatchExpr; comp-swap; comp-id; compbug-ignores-opcode; compbug-wrong )

-- stage 8 -- the AGENDA (control-worklist) design rule, from the live-trace root cause
-- (comp2 drops the then-branch, not a frozen value).  Unconditional structure may be
-- flattened onto the agenda (seq-flatten-ok); a DYNAMIC conditional must stay a residual
-- node with BOTH branches specialised (specOff-sound / specOff-keeps-branches), never a
-- branch pushed onto the shared agenda -- doing so drops a branch and is unsound
-- (specBug-riM collapses ri_min to echo-only; specBug-wrong).  Blueprint for the
-- production agenda offline-isation.
open import RWhileOfflineBTA8 public
  using ( seq-flatten-ok; specOff; specOff-sound; specOff-keeps-branches
        ; specBug; specBug-riM; specBug-wrong )
