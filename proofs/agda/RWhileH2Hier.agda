{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A FULL, TOTAL instance of the Futamura hierarchy with a genuine (non-closure)
-- self-applicable specialiser — Phase A1: replacing RWhileFutamura2Inst's
-- bespoke `papp`/`mkpapp` constructors with REAL program construction.
--
-- RWhileFutamura2Inst discharges H1/H2 by built-in constructors: `papp p s` is
-- a closure (the residual is opaque, just re-invokes `run p`) and `mkpapp` is a
-- one-step specialiser constructor.  Here, instead:
--
--   * residuals are REAL composite programs over a small applicative language
--     `Tm` (input / quote / pair / car / cdr / application), e.g. the
--     specialisation of `p` to `s` is the program  apT (quo p) (pr (quo s) inp)
--     — "on input d, run p on the pair ⟨s,d⟩";
--   * `run` is a GENERIC interpreter (general structural application of quoted
--     programs), NOT special-cased to the specialiser;
--   * the specialiser `specP` is itself a genuine `Tm` PROGRAM that CONSTRUCTS
--     those residuals from its input, using program-builder operations
--     (bAp / bQuo / pr / fstT / sndT / inp).
--
-- This faithfully models the paper's *trivial* reversible specialiser rspec
-- (embed p and s, run the interpreter, project) — the construction whose
-- empirical fp2/fp3 (comp2 ≈ 1×|spec|) the implementation realises.
--
-- Totality (so this stays `--safe` with no fuel): application is of LITERALLY
-- quoted programs, `run (apT (quo p) a) x = run p (run a x)`, which recurses on
-- the syntactic subterm `p`.  The trivial specialiser only ever emits such
-- residuals, so H1 and H2 hold by pure computation (refl), and `run` is total
-- by structural recursion.  General first-class application (a non-quoted
-- function position) would need a fuel-indexed `run` — that, together with the
-- looping AV specialiser of spec_av, is Phase A2 (route A).  The real AV
-- specialiser's recursive *structure* is separately self-represented in
-- RWhileH2 (`self-rep : cata specAlg ≡ aeval`).
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2Hier where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import RWhileFutamura2

------------------------------------------------------------------------
-- The universal applicative language (programs = data = residuals = values).

data Tm : Set where
  inp  : Tm                 -- the input
  quo  : Tm → Tm            -- a quoted constant program/value
  pr   : Tm → Tm → Tm       -- pairing (also the hierarchy's ⟨_,_⟩)
  fstT : Tm → Tm            -- car
  sndT : Tm → Tm            -- cdr
  apT  : Tm → Tm → Tm       -- application (run the 1st on the 2nd)
  -- program-builder ops (produce program nodes as output values):
  bInp : Tm                 -- build an `inp` node
  bQuo : Tm → Tm            -- build a `quo` node
  bAp  : Tm → Tm → Tm       -- build an `apT` node

fstv : Tm → Tm
fstv (pr a b) = a
fstv t        = t

sndv : Tm → Tm
sndv (pr a b) = b
sndv t        = t

-- The generic interpreter.  Structural recursion ⇒ total.  Application is of
-- literally quoted programs (the `apT (quo p) a` clause recurses on subterm p);
-- a non-quoted function position is unreachable for the trivial specialiser and
-- returns a dummy.
run : Tm → Tm → Tm
run inp             x = x
run (quo p)         x = p
run (pr a b)        x = pr (run a x) (run b x)
run (fstT e)        x = fstv (run e x)
run (sndT e)        x = sndv (run e x)
run (apT (quo p) a) x = run p (run a x)
run (apT f a)       x = inp               -- non-quoted function: unreachable here
run bInp            x = inp
run (bQuo a)        x = quo (run a x)
run (bAp a b)       x = apT (run a x) (run b x)

------------------------------------------------------------------------
-- The trivial specialiser, as a META-function and as a genuine PROGRAM.

-- spec p s : the residual "on input d, run p on ⟨s,d⟩".
spec : Tm → Tm → Tm
spec p s = apT (quo p) (pr (quo s) inp)

-- specP : a real Tm program that BUILDS `spec p s` from its input ⟨p,s⟩,
-- using the builder ops (no bespoke specialiser constructor).
specP : Tm
specP = bAp (bQuo (fstT inp)) (pr (bQuo (sndT inp)) bInp)

-- a sample interpreter program (here the identity: run int x = x).
int : Tm
int = inp

------------------------------------------------------------------------
-- H1 and H2 — both by pure computation.

-- H1: run (spec p s) d  reduces to  run p (pr s d)  =  run p ⟨s,d⟩.
spec-correct : ∀ p s d → run (spec p s) d ≡ run p (pr s d)
spec-correct p s d = refl

-- H2: run specP ⟨p,s⟩  reduces to  apT (quo p) (pr (quo s) inp)  =  spec p s.
spec-impl : ∀ p s → run specP (pr p s) ≡ spec p s
spec-impl p s = refl

------------------------------------------------------------------------
-- Instantiate the modular hierarchy: fp1/fp2/fp3 hold as PROVEN theorems for a
-- genuine, total, non-closure self-applicable specialiser.

open RWhileFutamura2.Hierarchy
       Tm pr run spec int specP
       spec-correct
       spec-impl
  public

------------------------------------------------------------------------
-- Witnesses of non-vacuity (concrete, by computation).

-- the compiler and cogen are concrete real programs:
compiler-is : compiler ≡ apT (quo specP) (pr (quo int) inp)
compiler-is = refl

cogen-is : cogen ≡ apT (quo specP) (pr (quo specP) inp)
cogen-is = refl

-- fp2 on a concrete source, by computation:
_ : run compiler (pr int specP) ≡ target (pr int specP)
_ = refl

-- fp3: cogen applied to the interpreter yields the compiler:
fp3-example : run cogen int ≡ compiler
fp3-example = fp3-int
