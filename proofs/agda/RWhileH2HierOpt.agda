{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2): a GENUINELY OPTIMISING specialiser in the SINGLE universal
-- type / TOTAL `run` setting of RWhileFutamura2.Hierarchy.
--
-- RWhileH2Hier instantiates the modular Futamura hierarchy with the TRIVIAL
-- "embed-and-apply" specialiser  spec p s = run p on ⟨s,d⟩  (no optimisation: the
-- residual keeps the whole source program and re-runs it).  The RWhileH2HierRec /
-- RecSelf / Dispatch / Full family proves OPTIMISING residuals (fold / dispatch
-- elimination) but only as standalone properties — none of them OPENS the
-- single-U total-run Hierarchy with an optimising `spec` and discharges H2.
--
-- Here we build a `spec` that is NOT the embed-and-apply wrapper: it RECURSES
-- over the source program (structural ⇒ total under --safe) and CONSTANT-FOLDS
-- projections of the STATIC input.  Specialising `car hole` (project the static
-- half) to `s` yields the CONSTANT `k s` — the projection AND the runtime input
-- dependency are gone; specialising `cdr hole` (project the dynamic half) yields
-- the bare `hole` — the projection is eliminated, the input genuinely used.
--
-- This file delivers the H1 half: the optimising `spec` with `spec-correct`
-- (fp1), proved by induction, plus witnesses that the optimisation is real (the
-- residual is projection-free where the trivial wrapper is not).  H2 (a program
-- `specP` running this fold, via a structural recursor) and the full fp2/fp3
-- Hierarchy instance are the next increment.  `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2HierOpt where

open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

------------------------------------------------------------------------
-- The universal language: programs = data = residuals = values, ONE total type.
-- (`comp g f` is composition: run g after f — it is what lets a specialiser emit
--  optimised chains.)

data U : Set where
  hole : U                 -- the input position (the hierarchy's `inp`)
  k    : U → U             -- a constant (a quoted value/program)
  pair : U → U → U         -- pairing (also the hierarchy's ⟨_,_⟩)
  car  : U → U
  cdr  : U → U
  comp : U → U → U         -- composition: (comp g f) runs g on f's result

-- total projections (the default branches keep `run` total)
car* : U → U
car* (pair a b) = a
car* t          = t

cdr* : U → U
cdr* (pair a b) = b
cdr* t          = t

------------------------------------------------------------------------
-- The total interpreter.  Structural recursion on the program ⇒ total in --safe.

run : U → U → U
run hole       x = x
run (k v)      x = v
run (pair a b) x = pair (run a x) (run b x)
run (car e)    x = car* (run e x)
run (cdr e)    x = cdr* (run e x)
run (comp g f) x = run g (run f x)

------------------------------------------------------------------------
-- Constant-folding smart constructors: a projection of a SYNTACTIC pair is
-- resolved at specialisation time (this is where the optimisation happens).

caro : U → U
caro (pair a b) = a
caro t          = car t

cdro : U → U
cdro (pair a b) = b
cdro t          = cdr t

-- correctness of the smart constructors: they agree with `car*`/`cdr* ∘ run`.
caro-correct : ∀ t d → run (caro t) d ≡ car* (run t d)
caro-correct hole       d = refl
caro-correct (k v)      d = refl
caro-correct (pair a b) d = refl
caro-correct (car e)    d = refl
caro-correct (cdr e)    d = refl
caro-correct (comp g f) d = refl

cdro-correct : ∀ t d → run (cdro t) d ≡ cdr* (run t d)
cdro-correct hole       d = refl
cdro-correct (k v)      d = refl
cdro-correct (pair a b) d = refl
cdro-correct (car e)    d = refl
cdro-correct (cdr e)    d = refl
cdro-correct (comp g f) d = refl

------------------------------------------------------------------------
-- The OPTIMISING specialiser: recurse over the source, propagating that the
-- input is the pair  ⟨s , d⟩  with s static (k s) and d dynamic (hole), folding
-- away projections.  (For `comp g f`, g sees a dynamic input, so it is kept.)

spec : U → U → U
spec hole       s = pair (k s) hole
spec (k v)      s = k v
spec (pair a b) s = pair (spec a s) (spec b s)
spec (car e)    s = caro (spec e s)
spec (cdr e)    s = cdro (spec e s)
spec (comp g f) s = comp g (spec f s)

------------------------------------------------------------------------
-- H1 (spec-correct = fp1): the residual run on d equals the source run on ⟨s,d⟩.
-- Proof by induction on the source program.

spec-correct : ∀ p s d → run (spec p s) d ≡ run p (pair s d)
spec-correct hole       s d = refl
spec-correct (k v)      s d = refl
spec-correct (pair a b) s d = cong₂ pair (spec-correct a s d) (spec-correct b s d)
spec-correct (car e)    s d =
  trans (caro-correct (spec e s) d) (cong car* (spec-correct e s d))
spec-correct (cdr e)    s d =
  trans (cdro-correct (spec e s) d) (cong cdr* (spec-correct e s d))
spec-correct (comp g f) s d = cong (run g) (spec-correct f s d)

-- fp1 in the hierarchy's shape, for any interpreter `int`.
fp1 : ∀ int src d → run (spec int src) d ≡ run int (pair src d)
fp1 int src d = spec-correct int src d

------------------------------------------------------------------------
-- The optimisation is REAL (non-vacuous): contrast with the trivial wrapper.

-- the trivial embed-and-apply specialiser (what RWhileH2Hier uses).
specTrivial : U → U → U
specTrivial p s = comp p (pair (k s) hole)

-- a structural "does the residual still contain a live projection?" predicate.
projFree : U → Bool
projFree hole       = true
projFree (k v)      = true
projFree (pair a b) = projFree a ∧ projFree b
projFree (car e)    = false
projFree (cdr e)    = false
projFree (comp g f) = projFree g ∧ projFree f

module Witness where
  -- specialising `car hole` (project the STATIC half) folds to the constant `k s`
  -- -- projection AND input dependency eliminated.
  static-proj : ∀ s → spec (car hole) s ≡ k s
  static-proj s = refl

  -- specialising `cdr hole` (project the DYNAMIC half) folds to the bare `hole`
  -- -- the projection is gone, the runtime input genuinely used.
  dyn-proj : ∀ s → spec (cdr hole) s ≡ hole
  dyn-proj s = refl

  -- both optimised residuals are projection-free …
  static-projFree : ∀ s → projFree (spec (car hole) s) ≡ true
  static-projFree s = refl
  dyn-projFree : ∀ s → projFree (spec (cdr hole) s) ≡ true
  dyn-projFree s = refl

  -- … whereas the trivial wrapper KEEPS the projection (optimisation non-vacuous).
  trivial-keeps-proj : ∀ s → projFree (specTrivial (car hole) s) ≡ false
  trivial-keeps-proj s = refl

  -- and the static projection's residual ignores its runtime input (constant):
  static-const : ∀ s d → run (spec (car hole) s) d ≡ s
  static-const s d = refl
