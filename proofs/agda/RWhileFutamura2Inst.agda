{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A CONCRETE, non-vacuous instance of the Futamura hierarchy: we exhibit a
-- universal type U with a self-applicable specialiser, discharging BOTH
-- hypotheses (H1 spec-correct, H2 spec-impl) by computation (refl).  So
-- fp1/fp2/fp3 from RWhileFutamura2 hold for actual, distinct programs.
--
-- The trick that makes H2 hold: U has a constructor `papp p s` ("p with
-- static input s baked in" — a specialised closure) that `run` interprets,
-- and a constructor `mkpapp` (the specialiser AS a program) that builds a
-- `papp` from a pair.  Then:
--     spec p s        := papp p s
--     run (papp p s) d = run p (pair s d)        -- H1 holds by definition
--     run mkpapp ⟨p,s⟩ = papp p s = spec p s     -- H2 holds by definition
--
-- (This is the standard "specialise = build a partial-application closure"
-- realisation.  It is honest about scope: a real R-WHILE specialiser has no
-- built-in closure constructor and must residualise structurally — that is
-- the engineering still open.  But it shows the hierarchy is INSTANTIABLE:
-- a self-applicable specialiser exists and fp2/fp3 are non-vacuous.)
------------------------------------------------------------------------

module RWhileFutamura2Inst where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import RWhileFutamura2

-- The universal language: programs = data = residuals.
data U : Set where
  pair   : U → U → U      -- pairing ⟨static , dynamic⟩
  papp   : U → U → U      -- specialised closure  (= spec p s)
  mkpapp : U              -- the specialiser, as a program  (= specP)
  idP    : U              -- a (placeholder) interpreter: run idP d = d

-- The universal `run`.  Only the closure case recurses, on a structurally
-- smaller first argument (papp p s ⟶ p), so `run` is total.
run : U → U → U
run (papp p s)  d         = run p (pair s d)
run mkpapp      (pair p s) = papp p s
run mkpapp      mkpapp     = mkpapp
run mkpapp      idP        = mkpapp
run mkpapp      (papp p s) = mkpapp
run idP         d          = d
run (pair a b)  d          = d

------------------------------------------------------------------------
-- Discharge the hierarchy's hypotheses — BOTH by refl — and instantiate it.
--   spec := papp ,  int := idP ,  specP := mkpapp ,  ⟨_,_⟩ := pair

open RWhileFutamura2.Hierarchy
       U pair run papp idP mkpapp
       (λ p s d → refl)     -- H1 spec-correct : run (papp p s) d ≡ run p (pair s d)
       (λ p s   → refl)     -- H2 spec-impl    : run mkpapp (pair p s) ≡ papp p s
  public

------------------------------------------------------------------------
-- The hierarchy now holds CONCRETELY.  A few computations witness it:

-- the compiler is a concrete program
compiler-is : compiler ≡ papp mkpapp idP
compiler-is = refl

-- fp2 on a concrete source, by pure computation:
fp2-example : ∀ src → run compiler src ≡ target src
fp2-example = fp2

_ : run compiler (pair idP mkpapp) ≡ target (pair idP mkpapp)
_ = refl

-- fp3: cogen applied to the interpreter yields the compiler, concretely:
fp3-example : run cogen idP ≡ compiler
fp3-example = fp3-int

_ : run cogen idP ≡ papp mkpapp idP
_ = refl
