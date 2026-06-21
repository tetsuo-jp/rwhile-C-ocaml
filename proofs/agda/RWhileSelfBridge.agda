{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2), the TRANSLATION BRIDGE: the two realisations of the
-- optimising self-applicable specialiser AGREE.
--
--   RWhileRevProj2Self  — abstract op-list model, total hard-coded `run`,
--                         fp1/2/3 by refl, `compiler-residual-uses-input`.
--   RWhileH2HierRecSelf — the SAME optimising guarantee lifted into the
--                         recursion-capable big-step relation `_·_⇓_`, with
--                         compilation a genuine recursion (`compileOps-correct`).
--
-- Instantiated with the SAME op alphabet and action `apply`, the two compilers
-- produce residuals that compute the SAME result.  The common semantic
-- denominator is `foldOps`; we prove the two modules' (separately defined)
-- `foldOps` agree, then bridge: the relational residual's (unique, by `⇓-det`)
-- value equals the data the abstract compiler's residual yields.  This is the
-- formal content of HANDOFF's "選択肢2 = bridge the small core to the model by
-- meaning preservation".
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileSelfBridge where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import RWhileH2HierRec using (Tm; _·_⇓_; ⇓-det; cn; inp; ⇓cn; ⇓inp)
import RWhileH2HierRecSelf as Rec
import RWhileRevProj2Self as Rev

module Bridge (Op : Set) (apply : Op → Tm → Tm)
              (opTm : Op → Tm) (op-runs : ∀ o d → opTm o · d ⇓ apply o d) where

  -- the relational model (compileOps over `_·_⇓_`).
  open Rec.Core Op apply opTm op-runs public using (foldOps; compileOps; compileOps-correct)
  -- the abstract op-list model, over the same Tm/Op/apply.
  module R = Rev.Core Tm Op apply

  -- the two separately-defined folds coincide (same definition, same args).
  foldOps-agree : ∀ ops d → R.foldOps ops d ≡ foldOps ops d
  foldOps-agree []       d = refl
  foldOps-agree (o ∷ os) d = foldOps-agree os (apply o d)

  -- THE BRIDGE: (a) the relational residual reduces to foldOps ops d, and
  -- (b) the abstract compiler's residual, run on uData d, yields exactly that
  -- same value (as uData).  Same optimising compiler, two formalisations.
  bridge : ∀ ops d →
      (compileOps ops · d ⇓ foldOps ops d)
    × (R.run (R.run R.compiler (R.uOps ops)) (R.uData d) ≡ R.uData (foldOps ops d))
  bridge ops d =
      compileOps-correct ops d
    , trans (R.compiler-residual-uses-input ops d) (cong R.uData (foldOps-agree ops d))

  -- corollary: the abstract residual's value is THE value the relational
  -- residual evaluates to (determinism pins it), making the agreement exact.
  bridge-exact : ∀ ops d {v} → compileOps ops · d ⇓ v →
                 R.run (R.run R.compiler (R.uOps ops)) (R.uData d) ≡ R.uData v
  bridge-exact ops d {v} ev
    with ⇓-det (compileOps-correct ops d) ev
  ... | refl = trans (R.compiler-residual-uses-input ops d) (cong R.uData (foldOps-agree ops d))

------------------------------------------------------------------------
-- Non-vacuous witness: the `dup` op (d ↦ cn d d), as in RWhileH2HierRecSelf.

module Witness where
  open import Data.Unit using (⊤; tt)
  open Bridge ⊤ (λ _ d → cn d d) (λ _ → cn inp inp)
              (λ _ d → ⇓cn (⇓inp d) (⇓inp d)) public

  -- both models compile [dup,dup] to a residual computing cn(cn d d)(cn d d).
  ex : R.run (R.run R.compiler (R.uOps (tt ∷ tt ∷ []))) (R.uData inp)
       ≡ R.uData (foldOps (tt ∷ tt ∷ []) inp)
  ex = proj₂ (bridge (tt ∷ tt ∷ []) inp)
    where open import Data.Product using (proj₂)
