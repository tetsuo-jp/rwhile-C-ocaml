{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The algebra of the tower, CONCRETELY — and the one reading of "cogen is a
-- fixed point" that is FALSE.
--
-- RWhileFutamura2Inst exhibits a universal type with a self-applicable
-- specialiser discharging H1 and H2 by `refl`.  Opening RWhileFutamuraAlg
-- with it makes every law of that module hold for actual, distinct programs,
-- and lets the laws be re-checked by COMPUTATION (the `_ = refl` blocks
-- below are the tests, written before the abstract proofs were trusted).
--
-- The point of the module, though, is the negative result.  ④ of
-- RESEARCH_ROADMAP calls the degeneracy "cogen の不動点性".  There are two
-- operators it could mean:
--
--     Φ X = run X specP    — apply X to the specialiser's text
--     Ψ X = run cogen X    — feed X to cogen
--
-- `fp4` is `Φ cogen ≡ cogen`: TRUE, and one line.  The other reading, that
-- cogen is a fixed point of `run cogen` (equivalently: that cogen is its own
-- generator when applied to ITSELF, `run cogen cogen ≡ cogen`) is refuted
-- here: in this model `run cogen cogen = papp mkpapp cogen`, which is a
-- STRICTLY LARGER term than cogen.  Since the model satisfies H1 and H2, no
-- proof of that statement can exist from the hypotheses of the hierarchy.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileFutamuraAlgInst where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import RWhileFutamura2Inst using (U; pair; papp; mkpapp; idP; run)
import RWhileFutamuraAlg

-- H1 and H2 hold by `refl` in this model (RWhileFutamura2Inst discharges
-- them the same way); opening the algebra gives all its laws here.
open RWhileFutamuraAlg.Algebra
       U pair run papp idP mkpapp
       (λ p s d → refl)     -- H1
       (λ p s   → refl)     -- H2
  public

------------------------------------------------------------------------
-- 1.  The laws, re-checked by computation.

_ : cogen ≡ papp mkpapp mkpapp
_ = refl

_ : compiler ≡ papp mkpapp idP
_ = refl

-- cogen curried, on concrete arguments
_ : run (run cogen idP) mkpapp ≡ papp idP mkpapp
_ = refl

-- (`spec` is instantiated to `papp` here, so the general law reads:)
_ : ∀ p s → run (run cogen p) s ≡ papp p s
_ = cogen-curry

-- the degeneracy, by computation
_ : run cogen mkpapp ≡ cogen
_ = refl

-- two- and three-stage composition
_ : ∀ src → run (run cogen idP) src ≡ target src
_ = cogen-target

_ : ∀ src → run (run (run cogen mkpapp) idP) src ≡ target src
_ = cogen-target₃

-- the tower is constant from level 0 (= cogen) on
_ : tower 5 ≡ cogen
_ = refl

------------------------------------------------------------------------
-- 2.  THE FALSE READING.  `run cogen cogen ≢ cogen`.
--
-- Size counts constructors; `papp` and `pair` are nodes, the two atoms are
-- leaves.  It is only used to separate two closed terms.

size : U → ℕ
size (pair a b) = suc (size a + size b)
size (papp a b) = suc (size a + size b)
size mkpapp     = 1
size idP        = 1

-- what cogen actually does to itself: it builds a bigger closure.
cogen-self : run cogen cogen ≡ papp mkpapp cogen
cogen-self = refl

_ : size cogen ≡ 3
_ = refl

_ : size (run cogen cogen) ≡ 5
_ = refl

-- so cogen is NOT a fixed point of `run cogen`.
cogen-not-self-applicable : ¬ (run cogen cogen ≡ cogen)
cogen-not-self-applicable eq = absurd (cong size eq)
  where
    absurd : suc (suc (suc (suc (suc zero)))) ≡ suc (suc (suc zero)) → ⊥
    absurd ()

-- The same in the shape that matters for ④: the level-4 candidate obtained
-- by feeding cogen to itself is a NEW program, whereas the one obtained by
-- feeding it the specialiser is cogen again.  Only the latter degenerates.
fp4-is-about-specP : run cogen mkpapp ≡ cogen
fp4-is-about-specP = fp4
