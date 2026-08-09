{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- REVERSIBLE JONES OPTIMALITY, RESTATED ON THE `-work` METER.
--
-- RWhileJonesRev's `Criterion` takes the cost model as a PARAMETER and
-- nothing in it inspects the parameter, so the work meter slots straight
-- in: `residual-pp`, `pp-unique`, `pp-injective`, `classical⇒rev`,
-- `rev-mono`, `basis-adequate` all hold verbatim with `cost := work`.  That
-- is what this module does, and it adds the one thing that is NOT
-- cost-agnostic and is the whole content of the work meter:
--
--     work(p⁺ on d) = work(p on d) + |⌜p⌝| + 1                  (⁺-cost)
--
-- so that the reversible criterion, unfolded at the work meter, reads
--
--     work(residual on d)  ≤  work(p on d) + |⌜p⌝| + 1 .        (rev-unfold)
--
-- Compare the STEP meter, where RWhileProgPres.pp-cost gives `+ 8`: there
-- the slack is an absolute constant, here it is linear in the size of the
-- program text.  The criterion is the same criterion; the basis is dearer,
-- and dearer in a way that depends on what is being specialised.  That is
-- the honest statement, and it is the one the measured table obeys
-- (RWhileProgWork.measured-law).
--
-- WHAT IS PARAMETRIC HERE.  `WorkModel` abstracts over the program set, the
-- encoding, the semantics and the BODY work, and assumes exactly the two
-- facts `Simp.program_preserving` provides: it pairs ⌜p⌝ onto the answer
-- (`⁺-sem`), and its emit charges no work of its own (`⁺-body`; the OCaml
-- emit is an assignment into a FRESH slot plus a `CRep` whose patterns are
-- variables, and the cost model charges neither).  `Model` below is a
-- concrete instance, so none of this is vacuous.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileJonesRevWork where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import RWhileTime using (V; nil; atm; _∙_)
open import RWhileWorkV using (nodes)
open import RWhileProgWork using (progW; pp-progW-ocaml)
open import RWhileJonesRev

------------------------------------------------------------------------
-- 0.  The pairing of R-WHILE data is injective on the right, so the
--     `⊗-injectiveʳ` hypothesis of `pp-injective` is discharged, not
--     assumed, once the criterion is instantiated at `_∙_`.

∙-injʳ : ∀ {a x z : V} → (a ∙ x) ≡ (a ∙ z) → x ≡ z
∙-injʳ refl = refl

------------------------------------------------------------------------
-- 1.  The work model.

module WorkModel
  (P       : Set)
  (code    : P → V)                          -- ⌜·⌝ (Program2DataRwhile)
  (runp    : P → V → V)                      -- ⟦·⟧, on its defined fragment
  (wbody   : P → V → ℕ)                      -- work of p's BODY
  (_⁺      : P → P)                          -- Simp.program_preserving
  (⁺-sem   : ∀ p d → runp (p ⁺) d ≡ code p ∙ runp p d)
  (⁺-body  : ∀ p d → wbody (p ⁺) d ≡ wbody p d)
  (ans≢nil : ∀ p d → ¬ (runp p d ≡ nil))
  where

  -- the cost model: RWhileProgWork.progW, i.e. `./ri -work`
  workOf : P → V → ℕ
  workOf p d = progW (wbody p d) (runp p d)

  open Criterion V P runp workOf code _∙_ public

  ----------------------------------------------------------------------
  -- p⁺ meets the obligation (this is `Simp.program_preserving`'s spec).

  ⁺-PP : ∀ p → PP (p ⁺) p
  ⁺-PP p d = ⁺-sem p d

  ----------------------------------------------------------------------
  -- THE WORK LAW.  Not a constant: linear in |⌜p⌝|.

  ⁺-cost : ∀ p d → workOf (p ⁺) d ≡ workOf p d + suc (nodes (code p))
  ⁺-cost p d =
    trans (cong₂ progW (⁺-body p d) (⁺-sem p d))
          (pp-progW-ocaml (wbody p d) (code p) (runp p d) (ans≢nil p d))

  -- hence the basis is at least as expensive as p -- the side condition of
  -- `classical⇒rev`, discharged rather than assumed.
  ⁺-mono : ∀ p d → workOf p d ≤ workOf (p ⁺) d
  ⁺-mono p d = subst (workOf p d ≤_) (sym (⁺-cost p d))
                     (m≤m+n (workOf p d) (suc (nodes (code p))))

  ----------------------------------------------------------------------
  -- The criterion at the work meter, and the theorems that come with it.

  RevJonesWork : P → P → Set
  RevJonesWork r p = RevJonesOptimal r p (p ⁺)

  -- classical ⇒ reversible, at the work meter (RWhileJonesRev.classical⇒rev
  -- with the monotonicity side condition supplied by ⁺-mono)
  classical⇒rev-work : ∀ {r p} → JonesOptimal r p → RevJonesWork r p
  classical⇒rev-work {r} {p} = classical⇒rev (⁺-PP p) (⁺-mono p)

  -- what the criterion SAYS, unfolded: the residual is allowed |⌜p⌝| + 1
  -- more work than p, and not one unit more.
  rev-unfold : ∀ {r p} → RevJonesWork r p
             → ∀ d → workOf r d ≤ workOf p d + suc (nodes (code p))
  rev-unfold {r} {p} (_ , le) d = subst (workOf r d ≤_) (⁺-cost p d) (le d)

  rev-fold : ∀ {r p} → (∀ d → workOf r d ≤ workOf p d + suc (nodes (code p)))
           → RevJonesWork r p
  rev-fold {r} {p} h = ⁺-PP p , λ d → subst (workOf r d ≤_) (sym (⁺-cost p d)) (h d)

  -- injectivity: the ⊗-injectivity hypothesis is discharged for R-WHILE
  -- data, so a program-preserving program is reversible whenever p is.
  pp-injective-∙ : ∀ {q p} → PP q p → Injective (runp p) → Injective (runp q)
  pp-injective-∙ = pp-injective ∙-injʳ

  ----------------------------------------------------------------------
  -- The fp1 layer, verbatim.  Given the two defining equations of a
  -- reversible Futamura projection, `residual-pp` and friends hold at the
  -- work meter with no change at all -- they never look at the cost.

  module Fp1Work
    (rint     : P)
    (spec     : P → V → P)
    (def-rint : ∀ p d → runp rint (code p ∙ d) ≡ code p ∙ runp p d)
    (def-spec : ∀ q s d → runp (spec q s) d ≡ runp q (s ∙ d))
    where

    open Fp1 rint spec def-rint def-spec public

    -- the fp1 residual satisfies the obligation, so `p ⁺` is an adequate
    -- basis for it -- and the criterion to check is exactly `rev-unfold`.
    residual-basis : ∀ p → ∀ d → runp (residual p) d ≡ runp (p ⁺) d
    residual-basis p = residual-same-spec p (p ⁺) (⁺-PP p)

    -- the reversible criterion for the fp1 residual, in measurable form
    residual-optimal-iff : ∀ p
                         → (∀ d → workOf (residual p) d
                                  ≤ workOf p d + suc (nodes (code p)))
                         → RevJonesWork (residual p) p
    residual-optimal-iff p = rev-fold

------------------------------------------------------------------------
-- 2.  A CONCRETE INSTANCE, so that none of the above is vacuous.
--
-- Programs are ℕ: `n` is a base program extended n times.  `codeOf n` is a
-- growing value standing for ⌜·⌝, `runp` tags its input (so the answer is
-- never nil), and the body work is 0 -- the extension is pure emit, which
-- is the case the OCaml `program_preserving` builds.

module Model where

  codeOf : ℕ → V
  codeOf zero    = atm 0 ∙ nil
  codeOf (suc n) = atm 0 ∙ codeOf n

  runN : ℕ → V → V
  runN zero    d = atm 0 ∙ d
  runN (suc n) d = codeOf n ∙ runN n d

  bodyW : ℕ → V → ℕ
  bodyW _ _ = 0

  runN≢nil : ∀ n d → ¬ (runN n d ≡ nil)
  runN≢nil zero    d ()
  runN≢nil (suc n) d ()

  open WorkModel ℕ codeOf runN bodyW suc
                 (λ n d → refl) (λ n d → refl) runN≢nil public

  -- the law, on a concrete row: the base program on input nil costs 3
  -- (it walks its own three-node answer at `write`), its extension costs 7
  -- = 3 + (3 + 1) where 3 = |⌜p⌝|.
  base-cost : workOf 0 nil ≡ 3
  base-cost = refl

  ext-cost : workOf 1 nil ≡ 7
  ext-cost = refl

  code-size : nodes (codeOf 0) ≡ 3
  code-size = refl

  law-here : workOf 1 nil ≡ workOf 0 nil + suc (nodes (codeOf 0))
  law-here = ⁺-cost 0 nil

  -- ... and the overhead really does grow with the program text
  ext-cost₂ : workOf 2 nil ≡ 7 + suc (nodes (codeOf 1))
  ext-cost₂ = ⁺-cost 1 nil

  overhead-differs : ¬ (suc (nodes (codeOf 0)) ≡ suc (nodes (codeOf 1)))
  overhead-differs ()
