{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Offline BTA, stage 3: the SPECIALISATION GAIN (the paper's goal ①, comp2 < |spec|).
--
-- Continues RWhileOfflineBTA / RWhileOfflineBTA2.  Stages 1-2 showed the correct
-- offline specialiser is sound and free of the over-static bug.  This stage shows it
-- delivers the FUTAMURA GAIN: static work is DONE at specialisation time.
--
--   * `spec2-noD-isS` / `gain`:  a fully-static subexpression — however large —
--     specialises to a SINGLE static leaf (`isS`, size 1).  All static structure is
--     folded away.  This is the maximal specialisation gain and the CORRECT behaviour.
--   * `dispatch-resolved`:  a static dispatch (hd of a cons with a static head)
--     collapses to the selected value — the residual does NOT re-run the dispatch.
--   * `dyn-survives`:  a dynamic sub-part is RESIDUALISED (kept as a `D` hole), NOT
--     frozen to a static value — so the residual is a genuine partially-static term.
--
-- Contrast (from stages 1-2): the OVER-STATIC bug also collapses to a single leaf,
-- but UNSOUNDLY (it freezes dynamic parts, `spec2bug-wrong-on-symbolic`); the TRIVIAL
-- DYNAMICIZE-ALL keeps everything dynamic (sound but NO gain).  The congruent offline
-- specialiser collapses EXACTLY the static parts — sound AND non-trivial.
------------------------------------------------------------------------
module RWhileOfflineBTA3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; suc; _+_)

open import RWhileAVSound
  using ( Val; ⟨⟩; _·_; hd; tl
        ; Code; cVar
        ; AV; S; D; C
        ; avHd; avTl; avCons )

open import RWhileOfflineBTA
  using ( Exp; eS; eD; eK; eHd; eTl; eCons; spec2
        ; noD; ndS; ndK; ndHd; ndTl; ndCons )

open import RWhileOfflineBTA2 using (spec2g)

------------------------------------------------------------------------
-- "Is a single static leaf": the maximally-specialised shape (all work done).

data isS : AV → Set where
  mkS : ∀ v → isS (S v)

-- The AV operations keep a single static leaf single (they compute, not residualise).
avHd-isS : ∀ {a} → isS a → isS (avHd a)
avHd-isS (mkS v) = mkS (hd v)

avTl-isS : ∀ {a} → isS a → isS (avTl a)
avTl-isS (mkS v) = mkS (tl v)

avCons-isS : ∀ {a b} → isS a → isS b → isS (avCons a b)
avCons-isS (mkS v1) (mkS v2) = mkS (v1 · v2)

-- GAIN (structural): a fully-static (noD) expression specialises to a single static
-- leaf.  Every static hd/tl/cons is performed at specialisation time.
spec2-noD-isS : ∀ {e} s → noD e → isS (spec2 e s)
spec2-noD-isS s ndS            = mkS _
spec2-noD-isS s (ndK v)        = mkS v
spec2-noD-isS s (ndHd nd)      = avHd-isS (spec2-noD-isS s nd)
spec2-noD-isS s (ndTl nd)      = avTl-isS (spec2-noD-isS s nd)
spec2-noD-isS s (ndCons na nb) = avCons-isS (spec2-noD-isS s na) (spec2-noD-isS s nb)

------------------------------------------------------------------------
-- GAIN (quantitative): the residual of a fully-static expression has size 1,
-- regardless of the source expression's size.  (Leaf-count size; a D hole = 1 leaf.)

sizeAV : AV → ℕ
sizeAV (S _)   = 1
sizeAV (D _)   = 1
sizeAV (C a b) = suc (sizeAV a + sizeAV b)

isS-size1 : ∀ {a} → isS a → sizeAV a ≡ 1
isS-size1 (mkS v) = refl

gain : ∀ {e} s → noD e → sizeAV (spec2 e s) ≡ 1
gain s nd = isS-size1 (spec2-noD-isS s nd)

------------------------------------------------------------------------
-- Concrete: static dispatch is RESOLVED, dynamic parts SURVIVE (not frozen).

-- `hd (cons (static a) dynamic)` — the static head is selected at spec time; the
-- dynamic tail never has to be built.  Residual = the value `a`.
dispatch-resolved : ∀ a sₐ → spec2g (eHd (eCons (eK a) eD)) sₐ ≡ S a
dispatch-resolved a sₐ = refl

-- `cons dynamic (static b)` — the dynamic input is residualised as a `D` hole; only
-- the partially-static structure is materialised.  NOT frozen to a static value.
dyn-survives : ∀ b sₐ → spec2g (eCons eD (eK b)) sₐ ≡ C (D cVar) (S b)
dyn-survives b sₐ = refl
