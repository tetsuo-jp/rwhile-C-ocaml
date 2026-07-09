{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 8: the AGENDA (control-worklist) design rule.
--
-- The live trace (TRACE_comp2_root_cause.md) found the real comp2 defect: it is not a
-- frozen VALUE but a DROPPED BRANCH.  `[comp2]('S.swap)` keeps ri_min's echo
-- (`In <= cons Op X`) but loses the then-branch of `if =? Op 'swap` (the swap body),
-- because spec_av's online worklist handles a conditional by PUSHING the taken branch
-- onto the control agenda `Cd` (`Cd <= cons C Cd`, spec_av_bti.rwhile:963) — which is
-- ill-defined once the test is DYNAMIC under self-application (you cannot residualise
-- "conditionally change what code runs next").
--
-- This module states the offline design rule as theorems, on a minimal command
-- language with dispatch (a faithful abstraction of SPEC-CMD-AV's agenda):
--
--   * `seq-flatten-ok` — UNCONDITIONAL structure (`seqC`) may be flattened onto the
--     agenda; the worklist semantics is unchanged.  (Sequencing on `Cd` is fine.)
--   * `specOff-sound` + `specOff-keeps-branches` — a DYNAMIC conditional must be kept as
--     a RESIDUAL node with BOTH branches specialised (not pushed onto the agenda); this
--     is sound and preserves both branches.  (The fix.)
--   * `specBug-riM` + `specBug-wrong` — pushing/keeping only ONE branch under a dynamic
--     test (the online-agenda failure) collapses ri_min to echo-only and is unsound —
--     exactly comp2's symptom.
------------------------------------------------------------------------
module RWhileOfflineBTA8 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)

open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; veq; hd; tl)

------------------------------------------------------------------------
-- Minimal command language over a store (Val), dispatching on an opcode (the stage-2
-- source).  swap = ri_min's swap body; echoOp = ri_min's `In <= cons Op X`.

swapV : Val → Val
swapV (a · b) = b · a
swapV ⟨⟩      = ⟨⟩

ifV : Val → Val → Val → Val
ifV ⟨⟩      t e = e
ifV (_ · _) t e = t

data Cmd : Set where
  skip   : Cmd
  swap   : Cmd
  echoOp : Cmd                       -- s ↦ (op · s)
  seqC   : Cmd → Cmd → Cmd
  ifOp   : Val → Cmd → Cmd → Cmd     -- if opcode = v then C else D

exec : Cmd → Val → Val → Val         -- exec c op s
exec skip       op s = s
exec swap       op s = swapV s
exec echoOp     op s = op · s
exec (seqC a b) op s = exec b op (exec a op s)
exec (ifOp v c d) op s = ifV (veq op v) (exec c op s) (exec d op s)

-- ri_min model: dispatch on the opcode ('swap ≈ vtrue) then echo it.
riM : Cmd
riM = seqC (ifOp vtrue swap skip) echoOp

------------------------------------------------------------------------
-- Agenda semantics: a list of commands run left to right (models the control worklist).

execList : List Cmd → Val → Val → Val
execList []       op s = s
execList (c ∷ cs) op s = execList cs op (exec c op s)

-- DESIGN RULE 1: unconditional `seqC` may be FLATTENED onto the agenda — sound.
-- (This is why spec_av's `Cd <= cons C Cd` is correct for `seq`.)
seq-flatten-ok : ∀ a b rest op s →
  execList (a ∷ b ∷ rest) op s ≡ execList (seqC a b ∷ rest) op s
seq-flatten-ok a b rest op s = refl

------------------------------------------------------------------------
-- OFFLINE specialiser (opcode symbolic): residualise `ifOp` keeping BOTH branches;
-- never push a branch onto the shared agenda.  DESIGN RULE 2.

specOff : Cmd → Cmd
specOff skip        = skip
specOff swap        = swap
specOff echoOp      = echoOp
specOff (seqC a b)  = seqC (specOff a) (specOff b)
specOff (ifOp v c d) = ifOp v (specOff c) (specOff d)

specOff-sound : ∀ c op s → exec (specOff c) op s ≡ exec c op s
specOff-sound skip        op s = refl
specOff-sound swap        op s = refl
specOff-sound echoOp      op s = refl
specOff-sound (seqC a b)  op s rewrite specOff-sound a op s = specOff-sound b op (exec a op s)
specOff-sound (ifOp v c d) op s rewrite specOff-sound c op s | specOff-sound d op s = refl

-- The residual of a dynamic conditional CONTAINS both specialised branches.
specOff-keeps-branches : ∀ v c d → specOff (ifOp v c d) ≡ ifOp v (specOff c) (specOff d)
specOff-keeps-branches v c d = refl

------------------------------------------------------------------------
-- The online-agenda BUG: under a dynamic test the worklist cannot push a branch, so it
-- keeps only ONE (here the else-branch) — modelling comp2 dropping the swap body.

specBug : Cmd → Cmd
specBug skip        = skip
specBug swap        = swap
specBug echoOp      = echoOp
specBug (seqC a b)  = seqC (specBug a) (specBug b)
specBug (ifOp v c d) = specBug d          -- BUG: then-branch c is dropped

-- On ri_min this collapses to echo-only (skip; echoOp) -- exactly comp2's 39-node output.
specBug-riM : specBug riM ≡ seqC skip echoOp
specBug-riM = refl

vtrue≢⟨⟩ : vtrue ≡ ⟨⟩ → ⊥
vtrue≢⟨⟩ ()

-- ...and it is UNSOUND: at opcode 'swap on a non-symmetric store the dropped swap body
-- gives the wrong result (echoes without swapping).
specBug-wrong : ¬ (∀ op s → exec (specBug riM) op s ≡ exec riM op s)
specBug-wrong hyp = vtrue≢⟨⟩ (cong (λ w → hd (tl w)) (hyp vtrue (vtrue · ⟨⟩)))
