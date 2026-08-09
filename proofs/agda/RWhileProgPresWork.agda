{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE WORK COST OF p⁺.  The point of the whole `-work` layer.
--
-- On the STEP meter RWhileProgPres proves `cost(p⁺) = cost(p) + 8`: a
-- CONSTANT, independent of the program and of the input.  That is a happy
-- accident of the meter, not of the construction: `-steps` cannot see the
-- SIZE of ⌜p⌝, and the emit's job is precisely to move ⌜p⌝ around.
--
-- On the WORK meter the constant is gone.  The emit's third command,
-- `self ^= con pd`, is a CLEARING test against the constant ⌜p⌝ (the slot
-- holds ⌜p⌝ at that point), so it walks all of ⌜p⌝; its fourth command
-- clears p's answer slot and walks all of the answer.  The first two are
-- free, being writes into nil slots.  Hence
--
--     work(p⁺) = work(p) + |⌜p⌝| + |⟦p⟧d|                        (emit-work)
--
-- where |v| = `nodes v` is the number of value nodes.  The overhead is
-- linear in the size of the program text, and `work-not-constant` shows no
-- constant can replace it.
--
-- WHICH MODEL OF THE EMIT.  This module costs the FLAT-CORE emit of
-- RWhileProgPres (four `^=`), because that is the emit the timed core can
-- express.  The OCaml `Simp.program_preserving` emits `CAss` + a pattern
-- replacement `CRep`, whose variable patterns are read and written FREE
-- under the cost model, so its emit charges 0 and the |⌜p⌝| appears one
-- step later, at the `write` clearing test.  Both accounts are given: this
-- module proves the flat-core one, RWhileProgWork proves the OCaml one and
-- checks it against the 11 measured rows of `./measure_proj jones-self`.
-- The two differ by exactly the clearings that `CRep` gets for free.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileProgPresWork where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-monoˡ-<)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import RWhileTime
open import RWhileWorkV using (nodes; nodes-pos; rupdW; rupdW-fresh; rupdW-self)
open import RWhileWork
open import RWhileWorkDet using (⇒w-det)
open import RWhileSIWf using (get-set-≡; get-set-≢)
open import RWhileProgPres using (module PP)

module PPW (y self out : ℕ) (pd : V)
           (self≢y   : ¬ (self ≡ y))
           (self≢out : ¬ (self ≡ out))
           (out≢y    : ¬ (out ≡ y))
           where

  open PP y self out pd self≢y self≢out out≢y public

  ----------------------------------------------------------------------
  -- The four steps, now with their work.  Compare RWhileProgPres.step1-4:
  -- the derivations are the same, the annotation is new.

  -- (1) writing ⌜p⌝ into the FRESH slot: `rupdate` sees a nil slot and
  --     takes the free branch.  Cost 0 -- however big ⌜p⌝ is.
  step1W : ∀ τ → get τ self ≡ nil → (self ^= con pd) ⊢ τ ⇒ s1 τ ∣ 1 ∥ 0
  step1W τ hs =
    subst (λ w → (self ^= con pd) ⊢ τ ⇒ s1 τ ∣ 1 ∥ w) eq (w-ass refl r)
    where
      r : rupd (get τ self) pd ≡ just pd
      r = subst (λ w → rupd w pd ≡ just pd) (sym hs) refl
      eq : rupdW (get τ self) pd ≡ 0
      eq = cong (λ w → rupdW w pd) hs

  -- (2) building the pair into the FRESH output slot: also free.  `cns` is
  --     one cons cell; the slot is nil.
  step2W : ∀ τ v → get τ out ≡ nil → get τ y ≡ v
         → (out ^= cns (var self) (var y)) ⊢ s1 τ ⇒ s2 τ v ∣ 1 ∥ 0
  step2W τ v ho hy =
    subst (λ w → (out ^= cns (var self) (var y)) ⊢ s1 τ ⇒ s2 τ v ∣ 1 ∥ w)
          eq (w-ass ev r)
    where
      gself : get (s1 τ) self ≡ pd
      gself = get-set-≡ τ self pd
      gy : get (s1 τ) y ≡ v
      gy = trans (get-set-≢ τ self y pd self≢y) hy
      gout : get (s1 τ) out ≡ nil
      gout = trans (get-set-≢ τ self out pd self≢out) ho
      ev : evalE (s1 τ) (cns (var self) (var y)) ≡ just (pd ∙ v)
      ev = cong just (cong₂ _∙_ gself gy)
      r : rupd (get (s1 τ) out) (pd ∙ v) ≡ just (pd ∙ v)
      r = subst (λ w → rupd w (pd ∙ v) ≡ just (pd ∙ v)) (sym gout) refl
      eq : rupdW (get (s1 τ) out) (pd ∙ v) ≡ 0
      eq = cong (λ w → rupdW w (pd ∙ v)) gout

  -- (3) CLEARING the scratch slot.  It holds ⌜p⌝ and is XOR-ed with ⌜p⌝, so
  --     `rupdate` runs the clearing test on two equal copies of ⌜p⌝ and
  --     walks all |⌜p⌝| nodes.  THIS is where p⁺'s work overhead lives.
  step3W : ∀ τ v → ¬ (pd ≡ nil)
         → (self ^= con pd) ⊢ s2 τ v ⇒ s3 τ v ∣ 1 ∥ nodes pd
  step3W τ v pd≢nil =
    subst (λ w → (self ^= con pd) ⊢ s2 τ v ⇒ s3 τ v ∣ 1 ∥ w) eq (w-ass refl r)
    where
      g : get (s2 τ v) self ≡ pd
      g = trans (get-set-≢ (s1 τ) out self (pd ∙ v) out≢self)
                (get-set-≡ τ self pd)
      r : rupd (get (s2 τ v) self) pd ≡ just nil
      r = subst (λ w → rupd w pd ≡ just nil) (sym g) (rupd-self pd)
      eq : rupdW (get (s2 τ v) self) pd ≡ nodes pd
      eq = trans (cong (λ w → rupdW w pd) g) (rupdW-self pd pd≢nil)

  -- (4) clearing p's answer slot, likewise: it walks the answer.
  step4W : ∀ τ v → get τ y ≡ v → ¬ (v ≡ nil)
         → (y ^= tlE (var out)) ⊢ s3 τ v ⇒ final τ v ∣ 1 ∥ nodes v
  step4W τ v hy v≢nil =
    subst (λ w → (y ^= tlE (var out)) ⊢ s3 τ v ⇒ final τ v ∣ 1 ∥ w)
          eq (w-ass ev r)
    where
      gout : get (s3 τ v) out ≡ pd ∙ v
      gout = trans (get-set-≢ (s2 τ v) self out nil self≢out)
                   (get-set-≡ (s1 τ) out (pd ∙ v))
      gy : get (s3 τ v) y ≡ v
      gy = trans (get-set-≢ (s2 τ v) self y nil self≢y)
           (trans (get-set-≢ (s1 τ) out y (pd ∙ v) out≢y)
           (trans (get-set-≢ τ self y pd self≢y) hy))
      ev : evalE (s3 τ v) (tlE (var out)) ≡ just v
      ev = subst (λ w → tlM w ≡ just v) (sym gout) refl
      r : rupd (get (s3 τ v) y) v ≡ just nil
      r = subst (λ w → rupd w v ≡ just nil) (sym gy) (rupd-self v)
      eq : rupdW (get (s3 τ v) y) v ≡ nodes v
      eq = trans (cong (λ w → rupdW w v) gy) (rupdW-self v v≢nil)

  ----------------------------------------------------------------------
  -- The emit suffix: 7 steps (as before) and |⌜p⌝| + |answer| work.

  emit-work : ∀ τ v → ¬ (pd ≡ nil) → ¬ (v ≡ nil)
            → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
            → emit ⊢ τ ⇒ final τ v ∣ 7 ∥ (nodes pd + nodes v)
  emit-work τ v pd≢nil v≢nil hs ho hy =
    w-seq (step1W τ hs)
          (w-seq (step2W τ v ho hy)
                 (w-seq (step3W τ v pd≢nil) (step4W τ v hy v≢nil)))

  ----------------------------------------------------------------------
  -- MAIN THEOREM.  p⁺'s work is p's work plus |⌜p⌝| plus |⟦p⟧d| -- and its
  -- step count is still p's + 8.  One run, two meters, and only one of them
  -- sees the program text.

  pp-work : ∀ {body σ τ k w} v → ¬ (pd ≡ nil) → ¬ (v ≡ nil)
          → body ⊢ σ ⇒ τ ∣ k ∥ w
          → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
          → ppBody body ⊢ σ ⇒ final τ v ∣ (k + 8) ∥ (w + (nodes pd + nodes v))
  pp-work {body} {σ} {τ} {k} {w} v pd≢nil v≢nil d hs ho hy =
    subst (λ n → ppBody body ⊢ σ ⇒ final τ v ∣ n ∥ (w + (nodes pd + nodes v)))
          (sym (+-suc k 7))
          (w-seq d (emit-work τ v pd≢nil v≢nil hs ho hy))

  -- ... and by determinism that is THE work, not an upper bound.
  pp-work-exact : ∀ {body σ τ ρ k m w w′} v → ¬ (pd ≡ nil) → ¬ (v ≡ nil)
                → body ⊢ σ ⇒ τ ∣ k ∥ w
                → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
                → ppBody body ⊢ σ ⇒ ρ ∣ m ∥ w′
                → w′ ≡ w + (nodes pd + nodes v)
  pp-work-exact v pd≢nil v≢nil d hs ho hy dpp =
    sym (proj₂ (proj₂ (⇒w-det (pp-work v pd≢nil v≢nil d hs ho hy) dpp)))

  -- the overhead in isolation, for quoting
  pp-overhead : V → ℕ
  pp-overhead v = nodes pd + nodes v

------------------------------------------------------------------------
-- THE CONTRAST WITH `-steps`, made formal.
--
-- `RWhileProgPres.pp-cost` says the STEP overhead is the constant 8.  The
-- WORK overhead cannot be any constant: it already differs between a
-- one-node ⌜p⌝ and a three-node one.  (This is the whole reason the paper
-- has to say which meter its Jones-optimality claim is made on.)

work-overhead : V → V → ℕ
work-overhead pd v = nodes pd + nodes v

-- strictly monotone in the size of the program text
work-overhead-mono : ∀ pd₁ pd₂ v → nodes pd₁ < nodes pd₂
                   → work-overhead pd₁ v < work-overhead pd₂ v
work-overhead-mono pd₁ pd₂ v h = +-monoˡ-< (nodes v) h

-- and therefore not constant
work-not-constant : ¬ (Σ[ c ∈ ℕ ] (∀ pd → work-overhead pd nil ≡ c))
work-not-constant (c , h) = one≢three (trans (h (atm 0)) (sym (h (atm 0 ∙ atm 0))))
  where
    one≢three : ¬ (2 ≡ 4)
    one≢three ()

-- ... whereas on the step meter it IS constant: 8, for every pd and every
-- answer.  (RWhileProgPres.pp-cost; restated here only for the contrast.)
step-overhead : ℕ
step-overhead = 8
