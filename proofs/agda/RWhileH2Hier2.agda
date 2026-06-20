{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Phase A2 (step 1): the Futamura hierarchy with GENERAL first-class
-- application, via a big-step evaluation RELATION (no fuel, no quote
-- restriction).
--
-- RWhileH2Hier (Phase A1) kept `run` total by restricting application to
-- literally quoted functions — enough for the trivial specialiser, but an
-- artificial limit.  Here we equip the SAME language `Tm` with a big-step
-- relation `prog · x ⇓ v` whose application rule `⇓ap` evaluates the function
-- POSITION to a program value and then applies it — genuine first-class,
-- general application.  A relation sidesteps the totality wall that blocks a
-- total `--safe` `run` for general application (it is an inductive family, so it
-- is fine in `--safe`; partiality = "some programs have no derivation"), and it
-- avoids fuel bookkeeping entirely.
--
-- We prove the relation DETERMINISTIC (so `⇓` is a partial function), discharge
-- H1 (both directions) and H2 for the trivial specialiser of RWhileH2Hier, and
-- derive fp1/fp2/fp3 as relational theorems with general application.
--
-- Remaining for full Phase A2: replace the trivial specialiser by the LOOPING
-- AV specialiser of spec_av (its bounded worklist) expressed in this general
-- model — the genuinely Turing-complete part (route A, future work).  Its
-- recursive structure is already self-represented in RWhileH2.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2Hier2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import RWhileH2Hier using
  (Tm; inp; quo; pr; fstT; sndT; apT; bInp; bQuo; bAp; spec; specP; int)

------------------------------------------------------------------------
-- Big-step evaluation relation: `prog · x ⇓ v` (run program on input x to v).
-- ⇓ap is GENERAL application: evaluate the function position to a program `fv`,
-- the argument to `av`, then run `fv` on `av`.

infix 4 _·_⇓_
data _·_⇓_ : Tm → Tm → Tm → Set where
  ⇓inp  : ∀ x                                      → inp     · x ⇓ x
  ⇓quo  : ∀ p x                                    → quo p   · x ⇓ p
  ⇓pr   : ∀ {a b x va vb}  → a · x ⇓ va → b · x ⇓ vb → pr a b  · x ⇓ pr va vb
  ⇓fst  : ∀ {e x va vb}    → e · x ⇓ pr va vb        → fstT e  · x ⇓ va
  ⇓snd  : ∀ {e x va vb}    → e · x ⇓ pr va vb        → sndT e  · x ⇓ vb
  ⇓ap   : ∀ {f a x fv av rv}
        → f · x ⇓ fv → a · x ⇓ av → fv · av ⇓ rv     → apT f a · x ⇓ rv
  ⇓bInp : ∀ x                                      → bInp    · x ⇓ inp
  ⇓bQuo : ∀ {a x va}       → a · x ⇓ va             → bQuo a  · x ⇓ quo va
  ⇓bAp  : ∀ {a b x va vb}  → a · x ⇓ va → b · x ⇓ vb → bAp a b · x ⇓ apT va vb

------------------------------------------------------------------------
-- The relation is deterministic: `⇓` is a partial function.

⇓-det : ∀ {prog x v w} → prog · x ⇓ v → prog · x ⇓ w → v ≡ w
⇓-det (⇓inp _)    (⇓inp _)    = refl
⇓-det (⇓quo _ _)  (⇓quo _ _)  = refl
⇓-det (⇓pr a1 b1) (⇓pr a2 b2) = cong₂ pr (⇓-det a1 a2) (⇓-det b1 b2)
⇓-det (⇓fst d1)   (⇓fst d2)   with ⇓-det d1 d2
... | refl = refl
⇓-det (⇓snd d1)   (⇓snd d2)   with ⇓-det d1 d2
... | refl = refl
⇓-det (⇓ap f1 a1 r1) (⇓ap f2 a2 r2) with ⇓-det f1 f2 | ⇓-det a1 a2
... | refl | refl = ⇓-det r1 r2
⇓-det (⇓bInp _)   (⇓bInp _)   = refl
⇓-det (⇓bQuo d1)  (⇓bQuo d2)  with ⇓-det d1 d2
... | refl = refl
⇓-det (⇓bAp a1 b1) (⇓bAp a2 b2) = cong₂ apT (⇓-det a1 a2) (⇓-det b1 b2)

------------------------------------------------------------------------
-- H1 (spec-correct), both directions.  spec p s = apT (quo p) (pr (quo s) inp).

h1-bwd : ∀ p s d {v} → p · pr s d ⇓ v → spec p s · d ⇓ v
h1-bwd p s d pf = ⇓ap (⇓quo p d) (⇓pr (⇓quo s d) (⇓inp d)) pf

h1-fwd : ∀ p s d {v} → spec p s · d ⇓ v → p · pr s d ⇓ v
h1-fwd p s d (⇓ap (⇓quo .p .d) (⇓pr (⇓quo .s .d) (⇓inp .d)) rpf) = rpf

------------------------------------------------------------------------
-- H2 (spec-impl): specP, run on ⟨p,s⟩ = pr p s, builds the residual spec p s.

h2 : ∀ p s → specP · pr p s ⇓ spec p s
h2 p s = ⇓bAp (⇓bQuo (⇓fst (⇓inp (pr p s))))
              (⇓pr (⇓bQuo (⇓snd (⇓inp (pr p s)))) (⇓bInp (pr p s)))

------------------------------------------------------------------------
-- The three artefacts and the three projections (relational, general app).

target : Tm → Tm
target src = spec int src

compiler : Tm
compiler = spec specP int

cogen : Tm
cogen = spec specP specP

-- fp1: the specialised interpreter computes the interpreter on ⟨src,d⟩.
fp1-fwd : ∀ src d {v} → target src · d ⇓ v → int · pr src d ⇓ v
fp1-fwd src d = h1-fwd int src d

fp1-bwd : ∀ src d {v} → int · pr src d ⇓ v → target src · d ⇓ v
fp1-bwd src d = h1-bwd int src d

-- fp2: the compiler maps each source to its target program.
fp2 : ∀ src → compiler · src ⇓ target src
fp2 src = h1-bwd specP int src (h2 int src)

-- fp3: the cogen maps each program to its specialiser-compiler.
fp3 : ∀ q → cogen · q ⇓ spec specP q
fp3 q = h1-bwd specP specP q (h2 specP q)

-- in particular, cogen on the interpreter yields the compiler.
fp3-int : cogen · int ⇓ compiler
fp3-int = fp3 int
