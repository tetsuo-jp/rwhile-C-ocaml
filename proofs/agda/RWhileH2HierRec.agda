{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Phase B / #5 (step 1): a big-step relational hierarchy with GENUINE STRUCTURAL
-- RECURSION — the enabler for modelling the LOOPING AV specialiser (spec_av's
-- worklist), beyond the embed-and-apply trivial specialiser of RWhileH2Hier2.
--
-- RWhileH2Hier2 added general first-class application; its specialiser still only
-- *embeds* its argument.  spec_av instead RECURSES over the program structure.
-- Here we extend the big-step relation `_·_⇓_` with a structural fold `cata z f`
-- that recurses on the INPUT's cons-structure:
--
--     cata z f · nv        ⇓ r   when  z · nv ⇓ r            (base)
--     cata z f · (cn a b)  ⇓ r   when  cata z f · a ⇓ ra,
--                                      cata z f · b ⇓ rb,
--                                      f · (cn ra rb) ⇓ r     (combine recursed kids)
--
-- A relation (not a total function) keeps this `--safe` even though the language
-- is now recursion-capable.  We prove the relation DETERMINISTIC and give a
-- worked, machine-checked RECURSIVE program (`mirrorP`, a recursive tree mirror)
-- with full correctness — demonstrating the model genuinely supports looping
-- computation.  A recursive specialiser is then a `cata` that folds a program
-- into residual code; its fp1/fp2/fp3 follow by the H1-then-hierarchy route of
-- RWhileH2Hier2 (the continuing work of #5).
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2HierRec where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- A small language: values (nv / cn) and programs (inp/car/cdr/quo/ap/cata).

data Tm : Set where
  nv   : Tm                  -- nil value
  cn   : Tm → Tm → Tm        -- cons
  inp  : Tm                  -- the input
  car  : Tm → Tm
  cdr  : Tm → Tm
  quo  : Tm → Tm             -- quoted constant
  ap   : Tm → Tm → Tm        -- general application
  cata : Tm → Tm → Tm        -- structural fold over the input (z base, f combine)

------------------------------------------------------------------------
-- big-step evaluation relation.

infix 4 _·_⇓_
data _·_⇓_ : Tm → Tm → Tm → Set where
  ⇓nv   : ∀ x → nv · x ⇓ nv
  ⇓cn   : ∀ {a b x va vb} → a · x ⇓ va → b · x ⇓ vb → cn a b · x ⇓ cn va vb
  ⇓inp  : ∀ x → inp · x ⇓ x
  ⇓car  : ∀ {e x a b} → e · x ⇓ cn a b → car e · x ⇓ a
  ⇓cdr  : ∀ {e x a b} → e · x ⇓ cn a b → cdr e · x ⇓ b
  ⇓quo  : ∀ p x → quo p · x ⇓ p
  ⇓ap   : ∀ {f a x fv av rv} → f · x ⇓ fv → a · x ⇓ av → fv · av ⇓ rv → ap f a · x ⇓ rv
  ⇓cataN : ∀ {z f r} → z · nv ⇓ r → cata z f · nv ⇓ r
  ⇓cataC : ∀ {z f a b ra rb r}
         → cata z f · a ⇓ ra → cata z f · b ⇓ rb → f · cn ra rb ⇓ r
         → cata z f · cn a b ⇓ r

------------------------------------------------------------------------
-- determinism: `⇓` is a partial function.

⇓-det : ∀ {p x v w} → p · x ⇓ v → p · x ⇓ w → v ≡ w
⇓-det (⇓nv _)     (⇓nv _)     = refl
⇓-det (⇓cn a1 b1) (⇓cn a2 b2) = cong₂ cn (⇓-det a1 a2) (⇓-det b1 b2)
⇓-det (⇓inp _)    (⇓inp _)    = refl
⇓-det (⇓car d1)   (⇓car d2)   with ⇓-det d1 d2
... | refl = refl
⇓-det (⇓cdr d1)   (⇓cdr d2)   with ⇓-det d1 d2
... | refl = refl
⇓-det (⇓quo _ _)  (⇓quo _ _)  = refl
⇓-det (⇓ap f1 a1 r1) (⇓ap f2 a2 r2) with ⇓-det f1 f2 | ⇓-det a1 a2
... | refl | refl = ⇓-det r1 r2
⇓-det (⇓cataN z1)      (⇓cataN z2)      = ⇓-det z1 z2
⇓-det (⇓cataC a1 b1 f1) (⇓cataC a2 b2 f2) with ⇓-det a1 a2 | ⇓-det b1 b2
... | refl | refl = ⇓-det f1 f2

------------------------------------------------------------------------
-- A worked RECURSIVE program: a tree mirror (recursively swap cons children).

-- meta-level mirror on values.
data IsVal : Tm → Set where
  vnv : IsVal nv
  vcn : ∀ {a b} → IsVal a → IsVal b → IsVal (cn a b)

mirror : Tm → Tm
mirror nv       = nv
mirror (cn a b) = cn (mirror b) (mirror a)
mirror _        = nv          -- non-value forms: irrelevant (we use it on values)

-- the program: fold the input, swapping the (already-mirrored) children.
mirrorP : Tm
mirrorP = cata (quo nv) (cn (cdr inp) (car inp))

-- correctness: on any value, mirrorP computes the meta-level mirror.
mirror-correct : ∀ {t} → IsVal t → mirrorP · t ⇓ mirror t
mirror-correct vnv = ⇓cataN (⇓quo nv nv)
mirror-correct (vcn {a} {b} va vb) =
  ⇓cataC (mirror-correct va) (mirror-correct vb)
         (⇓cn (⇓cdr (⇓inp (cn (mirror a) (mirror b))))
              (⇓car (⇓inp (cn (mirror a) (mirror b)))))

-- mirror is its own inverse on values (a reversible recursive transformation).
mirror-invol : ∀ {t} → IsVal t → mirror (mirror t) ≡ t
mirror-invol vnv = refl
mirror-invol (vcn va vb) = cong₂ cn (mirror-invol va) (mirror-invol vb)

-- mirror preserves value-hood (so the output can be re-run).
mirror-isval : ∀ {t} → IsVal t → IsVal (mirror t)
mirror-isval vnv = vnv
mirror-isval (vcn va vb) = vcn (mirror-isval vb) (mirror-isval va)

-- REVERSIBILITY AT THE PROGRAM LEVEL (the paper's central theme, on a genuinely
-- RECURSIVE program).  Running `mirrorP` produces some output `s`, and running
-- `mirrorP` AGAIN on `s` recovers the original input `t` — both as actual `⇓`
-- derivations in the relation.  This is a machine-checked reversible recursive
-- computation: a `cata`-defined loop that is its own inverse.
mirrorP-reversible :
  ∀ {t} → IsVal t → Σ Tm (λ s → (mirrorP · t ⇓ s) × (mirrorP · s ⇓ t))
mirrorP-reversible {t} vt =
  mirror t
  , mirror-correct vt
  , subst (λ z → mirrorP · mirror t ⇓ z)
          (mirror-invol vt)
          (mirror-correct (mirror-isval vt))

------------------------------------------------------------------------
-- A second worked recursion: the structural IDENTITY fold reconstructs its
-- input.  This is the primitive a recursive specialiser uses to TRAVERSE and
-- rebuild a program (rather than embed it whole like the trivial specialiser).

idFold : Tm
idFold = cata (quo nv) (cn (car inp) (cdr inp))

idFold-correct : ∀ {t} → IsVal t → idFold · t ⇓ t
idFold-correct vnv = ⇓cataN (⇓quo nv nv)
idFold-correct (vcn {a} {b} va vb) =
  ⇓cataC (idFold-correct va) (idFold-correct vb)
         (⇓cn (⇓car (⇓inp (cn a b))) (⇓cdr (⇓inp (cn a b))))

------------------------------------------------------------------------
-- #5 STEP 2 (the recursive specialiser) — DISCHARGED for the constant-output
-- family.  The step-2 obstruction was "make the fold emit a RUNNABLE residual,
-- i.e. construct *quoted program* structure as it recurses".  Here we do exactly
-- that for the simplest non-trivial specialisation: specialising the constant
-- function `λx. t` (the program that ignores its dynamic input and returns the
-- static value `t`).  The recursive specialiser
--
--     reify = cata (quo (quo nv)) inp
--
-- folds the STATIC value `t` into a residual PROGRAM `build t` whose leaves are
-- `quo nv` and whose nodes are `cn` — a runnable Tm, NOT inert data.  Running
-- that residual on ANY dynamic input reproduces `t`.  This is genuine
-- quoted-construction-under-recursion: the fold's base case emits `quo nv`
-- (a program), and `inp` at each combine re-emits the cons of the two residual
-- subprograms.  H1 (`reify-spec-correct`) then holds: ⟦reify·t⟧ x ≡ ⟦const t⟧ x.

-- the residual program produced for a static value (quoted leaves, cn nodes).
build : Tm → Tm
build nv       = quo nv
build (cn a b) = cn (build a) (build b)
build _        = quo nv         -- non-value forms unused (we reify values)

-- (a) the recursive specialiser folds the static value into the residual.
reify : Tm
reify = cata (quo (quo nv)) inp

reify-builds : ∀ {t} → IsVal t → reify · t ⇓ build t
reify-builds vnv = ⇓cataN (⇓quo (quo nv) nv)
reify-builds (vcn {a} {b} va vb) =
  ⇓cataC (reify-builds va) (reify-builds vb) (⇓inp (cn (build a) (build b)))

-- (b) the residual is RUNNABLE: on ANY dynamic input it reproduces the static t.
build-runs : ∀ {t} (x : Tm) → IsVal t → build t · x ⇓ t
build-runs x vnv               = ⇓quo nv x
build-runs x (vcn {a} {b} va vb) = ⇓cn (build-runs x va) (build-runs x vb)

-- H1 for the constant family: specialise once (reify·t ⇓ R), then R on any
-- dynamic input x computes the source's output t = ⟦λ_. t⟧ x.  A self-contained
-- machine-checked recursive specialiser emitting a runnable residual.
reify-spec-correct :
  ∀ {t} (x : Tm) → IsVal t → Σ Tm (λ R → (reify · t ⇓ R) × (R · x ⇓ t))
reify-spec-correct {t} x vt = build t , reify-builds vt , build-runs x vt

------------------------------------------------------------------------
-- BEYOND the constant family: specialising a program that USES its dynamic input
-- (so the residual must contain live `inp`/`car`/`cdr`, not only `quo`/`cn`) is
-- the general looping spec_av.  The constant case above shows the mechanism
-- (cata emitting runnable quoted structure) works; lifting it to input-dependent
-- residuals — threading the dynamic projections through the fold — is the
-- continuing research of #5.
