{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A concrete, EXECUTABLE instance of the paper's reversible projections
-- (RWhileRevProjPaper).  A universal type U with:
--   * a closure constructor `papp p s` (= spec p s), interpreted by `run`;
--   * `mkpapp` = the specialiser as a program (rspec);
--   * `rintP` = the reversible interpreter (keeps the program in its output);
--   * source programs `swapS`/`idS` with semantics `srcRun`.
-- Both paper hypotheses (def-rint, def-spec) hold by `refl`, so the three
-- reversible projections hold for actual, runnable programs — and the
-- second reversible projection (comp'') can be COMPUTED and executed.
------------------------------------------------------------------------

module RWhileRevProjInst where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import RWhileRevProjPaper

data U : Set where
  pair   : U → U → U
  papp   : U → U → U      -- specialised closure  (= spec p s)
  mkpapp : U              -- the specialiser as a program  (= rspec)
  rintP  : U              -- the reversible interpreter      (= rint)
  swapS  : U              -- source program "swap"
  idS    : U              -- source program "id"
  ★      : U              -- an atom (data leaf)

-- source-language semantics ⟦·⟧_S
srcRun : U → U → U
srcRun swapS (pair a b) = pair b a
srcRun idS   d          = d
srcRun _     d          = d

-- the universal `run` (only the closure case recurses, on a smaller arg ⇒ total)
run : U → U → U
run (papp p s) d         = run p (pair s d)
run mkpapp     (pair p s) = papp p s                 -- rspec builds the closure
run rintP      (pair p d) = pair p (srcRun p d)       -- rint keeps the program p
run _          d          = d

snd : U → U
snd (pair a b) = b
snd x          = x

snd-β : ∀ a b → snd (pair a b) ≡ b
snd-β a b = refl

------------------------------------------------------------------------
-- Both paper hypotheses hold by refl; instantiate the reversible projections.

open RWhileRevProjPaper.RevProjection
       U run pair snd snd-β srcRun rintP mkpapp
       (λ p d   → refl)     -- def-rint : run rintP (pair p d) ≡ pair p (srcRun p d)
       (λ p s d → refl)     -- def-spec : run (run mkpapp (pair p s)) d ≡ run p (pair s d)
  public

------------------------------------------------------------------------
-- The second reversible projection, concretely.

-- comp'' is computed by self-applying the specialiser to the interpreter:
comp-is : comp ≡ papp mkpapp rintP
comp-is = refl

-- running the compiler on a source yields the target (a reversible simulation):
comp-on-swap : run comp swapS ≡ papp rintP swapS
comp-on-swap = refl

-- and running that target on data reversibly simulates swap: snd = the result,
-- fst keeps the source program (the garbage).  E.g. on (★ . (★.★)):
_ : run (run comp swapS) (pair ★ (pair ★ ★)) ≡ pair swapS (pair (pair ★ ★) ★)
_ = refl

-- the second reversible projection's correctness, on this concrete input:
_ : snd (run (run comp swapS) (pair ★ (pair ★ ★))) ≡ srcRun swapS (pair ★ (pair ★ ★))
_ = rev-proj2 swapS (pair ★ (pair ★ ★))
