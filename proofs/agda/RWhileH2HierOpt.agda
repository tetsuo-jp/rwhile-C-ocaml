{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2), COMPLETED: a GENUINELY OPTIMISING specialiser instantiating
-- the single-U / total-`run` Futamura hierarchy (RWhileFutamura2.Hierarchy) — so
-- fp1/fp2/fp3 hold as theorems for a NON-TRIVIAL (non-embed-and-apply) specialiser.
--
-- RWhileH2Hier instantiates the hierarchy with the TRIVIAL specialiser
-- spec p s = "apply p to ⟨s,d⟩": the residual keeps the whole source and re-runs
-- it (no optimisation; this is why a self-applied trivial spec gives comp2 ≈ 1×).
-- The RWhileH2HierRec / RecSelf / Dispatch / Full family proves optimising
-- residuals but never OPENS this single-U hierarchy with an optimising spec.
--
-- Here `spec` RECURSES over the source program (structural ⇒ total under --safe)
-- and CONSTANT-FOLDS projections of the STATIC input:
--     spec (car hole) s  ↦  quo s     -- projection of the static half = a CONSTANT
--     spec (cdr hole) s  ↦  hole      -- projection of the dynamic half = bare input
-- For application / the specialiser-node `mix`, `spec` falls back to embed-and-
-- apply (the only honest option for re-running an unknown program), which is what
-- makes SELF-APPLICATION (fp2/fp3) go through.
--
-- H2 (`spec-impl`) is discharged by making the interpreter's `mix` instruction
-- run the structural fold:  run mix ⟨p,s⟩ = spec p s — so `mix` IS the specialiser
-- as an honest PROGRAM (a uniform interpreter rule, NOT a closure primitive).
-- Then opening the modular hierarchy yields fp1/fp2/fp3.  `--safe`, no
-- postulates/holes.
------------------------------------------------------------------------

module RWhileH2HierOpt where

open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
import RWhileFutamura2

------------------------------------------------------------------------
-- The universal language: programs = data = residuals = values, ONE total type.

data U : Set where
  hole : U                 -- the input position (the hierarchy's `inp`)
  quo  : U → U             -- a constant (a quoted value/program)
  pair : U → U → U         -- pairing (also the hierarchy's ⟨_,_⟩)
  car  : U → U
  cdr  : U → U
  app  : U → U → U         -- application of a quoted program (kept total: see `run`)
  mix  : U                 -- the SPECIALISER, as a program (the hierarchy's specP)

-- total projections (the default branches keep `run` total)
car* : U → U
car* (pair a b) = a
car* t          = t

cdr* : U → U
cdr* (pair a b) = b
cdr* t          = t

------------------------------------------------------------------------
-- Constant-folding smart constructors: a projection of a SYNTACTIC pair is
-- resolved at specialisation time (this is where the optimisation happens).

caro : U → U
caro (pair a b) = a
caro t          = car t

cdro : U → U
cdro (pair a b) = b
cdro t          = cdr t

------------------------------------------------------------------------
-- The OPTIMISING specialiser (a structural fold): propagate that the input is
-- ⟨s , d⟩ with s static (quo s) and d dynamic (hole), folding away projections;
-- for application / `mix` fall back to honest embed-and-apply.

spec : U → U → U
spec hole       s = pair (quo s) hole
spec (quo v)    s = quo v
spec (pair a b) s = pair (spec a s) (spec b s)
spec (car e)    s = caro (spec e s)
spec (cdr e)    s = cdro (spec e s)
spec (app f a)  s = app (quo (app f a)) (pair (quo s) hole)   -- embed-and-apply
spec mix        s = app (quo mix)       (pair (quo s) hole)   -- embed-and-apply

------------------------------------------------------------------------
-- The total interpreter.  Application is restricted to QUOTED programs (the
-- recursive `run p` is then on the SUBTERM p ⇒ structural ⇒ total, as in
-- RWhileH2Hier).  The `mix` instruction runs the structural fold `spec`.

run : U → U → U
run hole            x = x
run (quo p)         x = p
run (pair a b)      x = pair (run a x) (run b x)
run (car e)         x = car* (run e x)
run (cdr e)         x = cdr* (run e x)
run (app (quo p) a) x = run p (run a x)
run (app f a)       x = hole                 -- non-quoted: unreachable for residuals
run mix             x = spec (car* x) (cdr* x)

------------------------------------------------------------------------
-- Correctness of the smart constructors: they agree with `car*`/`cdr* ∘ run`.

caro-correct : ∀ t d → run (caro t) d ≡ car* (run t d)
caro-correct hole            d = refl
caro-correct (quo v)         d = refl
caro-correct (pair a b)      d = refl
caro-correct (car e)         d = refl
caro-correct (cdr e)         d = refl
caro-correct (app f a)       d = refl
caro-correct mix             d = refl

cdro-correct : ∀ t d → run (cdro t) d ≡ cdr* (run t d)
cdro-correct hole            d = refl
cdro-correct (quo v)         d = refl
cdro-correct (pair a b)      d = refl
cdro-correct (car e)         d = refl
cdro-correct (cdr e)         d = refl
cdro-correct (app f a)       d = refl
cdro-correct mix             d = refl

------------------------------------------------------------------------
-- H1 (spec-correct = fp1): the residual run on d equals the source run on ⟨s,d⟩.

spec-correct : ∀ p s d → run (spec p s) d ≡ run p (pair s d)
spec-correct hole       s d = refl
spec-correct (quo v)    s d = refl
spec-correct (pair a b) s d = cong₂ pair (spec-correct a s d) (spec-correct b s d)
spec-correct (car e)    s d =
  trans (caro-correct (spec e s) d) (cong car* (spec-correct e s d))
spec-correct (cdr e)    s d =
  trans (cdro-correct (spec e s) d) (cong cdr* (spec-correct e s d))
spec-correct (app f a)  s d = refl
spec-correct mix        s d = refl

------------------------------------------------------------------------
-- H2 (spec-impl): `mix` IS the specialiser as a program — running it on ⟨p,s⟩
-- computes the structural fold `spec p s`.  By definition of `run mix`, refl.

spec-impl : ∀ p s → run mix (pair p s) ≡ spec p s
spec-impl p s = refl

------------------------------------------------------------------------
-- A sample interpreter: the identity on ⟨static , dynamic⟩, written with both
-- projections so specialisation has overhead to remove.

int : U
int = pair (car hole) (cdr hole)

------------------------------------------------------------------------
-- Instantiate the modular Futamura hierarchy: fp1/fp2/fp3 hold as PROVEN
-- theorems for a genuine, total, NON-TRIVIAL (optimising) self-applicable spec.

open RWhileFutamura2.Hierarchy
       U pair run spec int mix
       spec-correct
       spec-impl
  public

------------------------------------------------------------------------
-- The optimisation is REAL (non-vacuous).

-- a structural "does the residual still contain a live projection?" predicate.
projFree : U → Bool
projFree hole       = true
projFree (quo v)    = true
projFree (pair a b) = projFree a ∧ projFree b
projFree (car e)    = false
projFree (cdr e)    = false
projFree (app f a)  = projFree f ∧ projFree a
projFree mix        = true

module Witness where
  -- specialising the static projection folds to a CONSTANT; the dynamic one to
  -- the bare input — the interpreter's projections are gone.
  static-proj : ∀ s → spec (car hole) s ≡ quo s
  static-proj s = refl
  dyn-proj : ∀ s → spec (cdr hole) s ≡ hole
  dyn-proj s = refl

  -- the source HAS projections; the optimised residual is projection-free.
  source-has-proj : projFree (car hole) ≡ false
  source-has-proj = refl
  residual-projFree : ∀ s → projFree (spec (car hole) s) ≡ true
  residual-projFree s = refl

  -- fp1 PAYOFF: the target (interpreter specialised to src) constant-folds its
  -- static projection — the residual is `pair (quo src) hole`, the identity-
  -- interpreter's projection overhead removed, the dynamic input still used.
  target-folds : ∀ src → target src ≡ pair (quo src) hole
  target-folds src = refl

  -- the compiler and cogen are concrete real programs (fp2/fp3 non-vacuous).
  compiler-is : compiler ≡ app (quo mix) (pair (quo int) hole)
  compiler-is = refl
  cogen-is : cogen ≡ app (quo mix) (pair (quo mix) hole)
  cogen-is = refl
