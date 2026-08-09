{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE SAME BRIDGE, ON THE `-work` METER.
--
-- RWhileJonesRevTimed instantiates the relational criterion at the timed
-- core with the STEP count as the cost.  Nothing in the criterion inspects
-- the cost, so the work meter slots straight in — and this module does it,
-- reusing RWhileProgWork's `_▷_⇒_∥_` verbatim: the very relation whose
-- numbers `RWhileProgWork.measured-law` checks against the eleven rows of
-- `./measure_proj jones-self`.
--
-- What is proved here that the step instance cannot state:
--
--   ⁺-PP     p⁺ meets the obligation on the work meter too, in both
--            directions.  The backward half forgets the work, uses the
--            step-level inversion (RWhileProgPresBack.pp-back), and puts
--            the work annotation back with `RWhileWork.wk-sound` —
--            legitimate because `⇒w-det` says there is only one.
--   ⁺-costW  work(p⁺) = work(p) + (|⌜p⌝| + |answer|) + |⌜p⌝| + 1, exactly.
--   ⁺-mono   hence work(p) ≤ work(p⁺): `classical⇒rev`'s side condition,
--            discharged on this meter as well.
--
-- HOW THIS RELATES TO THE MEASURED TABLE (the honest statement).  The eleven
-- measured rows obey `work(p⁺) = work(p) + |⌜p⌝| + 1`
-- (`RWhileProgWork.pp-progW-ocaml`, checked row by row by `measured-law`).
-- The law proved HERE has `|⌜p⌝| + |answer|` more, and that is not a
-- discrepancy but the known model difference: the OCaml emit is a `CAss`
-- plus a pattern replacement `CRep`, whose variable patterns are read and
-- written FREE, whereas the timed core has no `<=` and must clear both slots
-- with `^=`, paying for exactly those two walks.  `overhead-gap` states the
-- difference as an equation instead of leaving it to prose.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileJonesRevTimedWork where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; yes; no)

open import RWhileTime
open import RWhileWork using (_⊢_⇒_∣_∥_; w-seq; ⇒w-steps; wk-sound)
open import RWhileWorkDet using (⇒w-det)
open import RWhileWorkV using (nodes; rupdW)
open import RWhileProgWork
  using (Program; prog; _▷_⇒_∥_; run; progW; pp-progW; pp-progW-ocaml)
open import RWhileProgPresBack using (module PPBack)
open import RWhileProgPresWork using (module PPW)
open import RWhileJonesRevRel using (module CriterionR)
open import RWhileJonesRevTimed using (∙-injʳ)

private
  open +-*-Solver
  shuffle : ∀ w e r → (w + e) + r ≡ (w + r) + e
  shuffle = solve 3 (λ w e r → (w :+ e) :+ r := (w :+ r) :+ e) refl

------------------------------------------------------------------------
-- The work instance.

module TimedWork (code : Program → V) where

  ----------------------------------------------------------------------
  -- 1.  Determinism of the work meter at whole-program level.

  ▷-det : ∀ {p d v₁ v₂ W₁ W₂}
        → p ▷ d ⇒ v₁ ∥ W₁ → p ▷ d ⇒ v₂ ∥ W₂ → (v₁ ≡ v₂) × (W₁ ≡ W₂)
  ▷-det (run d₁ h₁ _) (run d₂ h₂ _) with ⇒w-det d₁ d₂
  ... | refl , refl , refl = veq , cong (progW _) veq
    where veq = trans (sym h₁) h₂

  open CriterionR V Program _▷_⇒_∥_ ▷-det code _∙_ public

  ----------------------------------------------------------------------
  -- 2.  p⁺ on the work meter.

  module Ext (x y self o : ℕ) (c : Cmd)
             (self≢y : ¬ (self ≡ y))
             (self≢o : ¬ (self ≡ o))
             (o≢y    : ¬ (o ≡ y))
             where

    p : Program
    p = prog x y c

    open PPBack y self o (code p) self≢y self≢o o≢y
    open PPW    y self o (code p) self≢y self≢o o≢y using (pp-work)

    p⁺ : Program
    p⁺ = prog x o (ppBody c)

    ------------------------------------------------------------------
    -- Forwards.  The cost is existential in `PP`, so the plain work
    -- annotation of `wk-sound` suffices here; the EXACT cost is `⁺-costW`.

    ⁺-runW : ∀ {d v W} → p ▷ d ⇒ v ∥ W
           → Σ[ W′ ∈ ℕ ] (p⁺ ▷ d ⇒ (code p ∙ v) ∥ W′)
    ⁺-runW (run {τ = τ} {v = v} dw hy hcl) =
      _ , run (w-seq dw (wk-sound (emit-run τ v (hcl self y≢self)
                                                (hcl o y≢out) hy)))
              (final-out τ v) cl
      where
        cl : ∀ z → ¬ (o ≡ z) → get (final τ v) z ≡ nil
        cl z ne with y ≟ z | self ≟ z
        ... | yes refl | _        = final-y τ v
        ... | no ny    | yes refl = final-self τ v
        ... | no ny    | no ns    = trans (final-frame τ v z ny ns ne) (hcl z ny)

    ------------------------------------------------------------------
    -- Backwards.  Forget the work, invert at the step level, put the work
    -- back (unique by `⇒w-det`).

    back : ∀ {d u W} → p⁺ ▷ d ⇒ u ∥ W → Conv p d
    back (run dpp _ hcl) with pp-back (⇒w-steps dpp) hcl
    ... | τ , k , db , hs , ho , ρ≡ , _ =
          get τ y , _ , run (wk-sound db) refl cl
      where
        cl : ∀ z → ¬ (y ≡ z) → get τ z ≡ nil
        cl z ny with self ≟ z | o ≟ z
        ... | yes refl | _        = hs
        ... | no ns    | yes refl = ho
        ... | no ns    | no no′   =
              trans (sym (final-frame τ (get τ y) z ny ns no′))
                    (trans (cong (λ σ → get σ z) (sym ρ≡)) (hcl z no′))

    -- THE OBLIGATION, on the work meter.
    ⁺-PP : PP p⁺ p
    ⁺-PP = ⁺-runW , back

    ⁺-injective : Inj p → Inj p⁺
    ⁺-injective = pp-injective ∙-injʳ ⁺-PP

    ------------------------------------------------------------------
    -- 3.  THE EXACT WORK.  Unlike the step meter's constant 8, the work
    --     overhead depends on the program text AND on the answer, so the
    --     side conditions of RWhileProgPresWork are needed: the two
    --     clearings must actually walk something.

    Δ : V → ℕ
    Δ v = (nodes (code p) + nodes v) + suc (nodes (code p))

    ⁺-costW : ∀ {d v W} → ¬ (code p ≡ nil) → ¬ (v ≡ nil) → p ▷ d ⇒ v ∥ W
            → Σ[ W′ ∈ ℕ ] ((p⁺ ▷ d ⇒ (code p ∙ v) ∥ W′) × (W′ ≡ W + Δ v))
    ⁺-costW pd≢nil v≢nil (run {τ = τ} {w = w} {v = v} dw hy hcl) =
        progW (w + (nodes (code p) + nodes v)) (code p ∙ v)
      , run (pp-work v pd≢nil v≢nil dw (hcl self y≢self) (hcl o y≢out) hy)
            (final-out τ v) cl
      , pp-progW w (nodes (code p) + nodes v) (code p) v v≢nil
      where
        cl : ∀ z → ¬ (o ≡ z) → get (final τ v) z ≡ nil
        cl z ne with y ≟ z | self ≟ z
        ... | yes refl | _        = final-y τ v
        ... | no ny    | yes refl = final-self τ v
        ... | no ny    | no ns    = trans (final-frame τ v z ny ns ne) (hcl z ny)

    ------------------------------------------------------------------
    -- 4.  Hence the basis is never cheaper than p.

    ⁺-mono : ¬ (code p ≡ nil)
           → (∀ {d v W} → p ▷ d ⇒ v ∥ W → ¬ (v ≡ nil))
           → p ≼ p⁺
    ⁺-mono pd≢nil ans≢nil dpp with back dpp
    ... | v , W₀ , dp with ⁺-costW pd≢nil (ans≢nil dp) dp
    ...   | W′ , dpp′ , eq =
          v , W₀ , dp
        , subst (W₀ ≤_) (sym (trans (sym (proj₂ (▷-det dpp′ dpp))) eq))
                (m≤m+n W₀ (Δ v))

    RevJonesWork : Program → Set
    RevJonesWork r = RevJonesOptimal r p p⁺

    classical⇒rev-work : ∀ {r} → ¬ (code p ≡ nil)
                       → (∀ {d v W} → p ▷ d ⇒ v ∥ W → ¬ (v ≡ nil))
                       → JonesOptimal r p → RevJonesWork r
    classical⇒rev-work pd≢nil ans≢nil =
      classical⇒rev ⁺-PP (⁺-mono pd≢nil ans≢nil)

    -- what the criterion allows, unfolded: `Δ v` more work than p, and not
    -- one unit more.
    rev-unfold : ∀ {r} → RevJonesWork r → ¬ (code p ≡ nil)
               → ∀ {d v W} → ¬ (v ≡ nil) → p ▷ d ⇒ v ∥ W
               → Σ[ u ∈ V ] Σ[ j ∈ ℕ ] ((r ▷ d ⇒ u ∥ j) × (j ≤ W + Δ v))
    rev-unfold (_ , le) pd≢nil v≢nil dp with ⁺-costW pd≢nil v≢nil dp
    ... | W′ , dpp , eq with le dpp
    ...   | u , j , dr , j≤ = u , j , dr , subst (j ≤_) eq j≤

  ----------------------------------------------------------------------
  -- 5.  THE FLAT-CORE LAW AGAINST THE MEASURED (OCaml) LAW.
  --
  -- `pp-progW-ocaml` is the equation `measured-law` checks against eleven
  -- measured rows: work(p⁺) = work(p) + |⌜p⌝| + 1.  The flat-core emit pays
  -- |⌜p⌝| + |answer| more, because it clears with `^=` what `CRep` clears
  -- for free.  Stated, rather than asserted.

  overhead-gap : ∀ w pd v → ¬ (v ≡ nil)
               → progW (w + (nodes pd + nodes v)) (pd ∙ v)
                 ≡ (progW w v + suc (nodes pd)) + (nodes pd + nodes v)
  overhead-gap w pd v v≢nil =
    trans (shuffle w (nodes pd + nodes v) (rupdW (pd ∙ v) (pd ∙ v)))
          (cong (_+ (nodes pd + nodes v)) (pp-progW-ocaml w pd v v≢nil))

------------------------------------------------------------------------
-- A CONCRETE INSTANCE, so that none of the above is vacuous: the worked
-- example of RWhileProgPres on the work meter.
--
--   p  = read V0;  V0 ^= 'seven;  write V0
--   p⁺ = read V0;  V0 ^= 'seven;  emit;  write V2
--
-- with ⌜p⌝ = atm 42 (one node) and the answer 'seven (one node).  p's work
-- is 1 (the `write` clearing test walks the one-node answer); p⁺'s is
-- (0 + 2) + |⟨⌜p⌝ , answer⟩| = 2 + 3 = 5 -- i.e. p's + Δ = 1 + 4.

module Example where

  codeEx : Program → V
  codeEx _ = atm 42

  open TimedWork codeEx
  open Ext 0 0 1 2 (0 ^= opd (cst (atm 7))) (λ ()) (λ ()) (λ ())

  bodyEx : Cmd
  bodyEx = 0 ^= opd (cst (atm 7))

  runEx : p ▷ nil ⇒ atm 7 ∥ progW 0 (atm 7)
  runEx = run {τ = atm 7 ∷ []} (wk-sound (exec-sound 1 bodyEx (nil ∷ [])
                                                     (atm 7 ∷ []) 1 refl))
              refl cl
    where
      cl : ∀ z → ¬ (0 ≡ z) → get (atm 7 ∷ []) z ≡ nil
      cl zero    ne with ne refl
      ... | ()
      cl (suc z) _ = refl

  work-p : progW 0 (atm 7) ≡ 1
  work-p = refl

  -- the overhead really is Δ = 4 here, not the step meter's 8 and not the
  -- OCaml emit's |⌜p⌝| + 1 = 2
  delta-ex : Δ (atm 7) ≡ 4
  delta-ex = refl

  ⁺-ex : Σ[ W′ ∈ ℕ ] ((p⁺ ▷ nil ⇒ (atm 42 ∙ atm 7) ∥ W′)
                       × (W′ ≡ progW 0 (atm 7) + Δ (atm 7)))
  ⁺-ex = ⁺-costW (λ ()) (λ ()) runEx

  basis-ex : PP p⁺ p
  basis-ex = ⁺-PP
