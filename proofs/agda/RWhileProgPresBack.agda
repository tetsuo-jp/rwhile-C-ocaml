{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- RUNNING p⁺ BACKWARDS ONTO p: the missing half of the bridge.
--
-- RWhileProgPres builds p⁺ and proves the FORWARD direction: if p's body
-- converges leaving its answer in `y` and the two fresh slots nil, then p⁺
-- converges to ⟨⌜p⌝ , answer⟩ in k + 8 steps.
--
-- To say that p⁺ MEETS THE OBLIGATION of RWhileJonesRev over a PARTIAL
-- semantics one also needs the converse: p⁺ converges only where p does,
-- and its run really is p's run followed by the emit.  That is what this
-- module proves.  It is not bookkeeping: `pp-injective` and `pp-unique` of
-- the relational criterion (RWhileJonesRevRel) are false without it, since
-- nothing else stops a "program-preserving" q from computing whatever it
-- likes on inputs where p diverges.
--
-- THE POINT OF DIFFICULTY.  Inverting `ppBody body = body ⨾ emit` gives p's
-- run for free — but NOT the store invariant p's run is supposed to have:
-- from a derivation alone, nothing says the two fresh slots were nil when
-- the emit began.  They need not be: if `self` already held ⌜p⌝, the first
-- assignment would CLEAR it (`^=` is XOR, not binding) and the run would
-- still exist.  What rules that out is p⁺'s own `all_cleared` obligation on
-- its final store, pushed backwards through the four assignments:
--
--   `self` ends nil    ⟹  the third assignment cleared it  ⟹  it held ⌜p⌝
--                      ⟹  the first assignment SET it      ⟹  it began nil
--   `y` ends nil       ⟹  the fourth assignment cleared it ⟹  `out` held
--                          ⟨_ , answer⟩ ⟹ the second assignment set it
--                      ⟹  `out` began nil
--
-- The three `rupd` facts that carry this are `rupd-clear` / `rupd-fix` /
-- `rupd-cons` below; all three are corollaries of RWhileTimeInv.rupd-invol,
-- i.e. of the very partial-involution property that makes `^=` reversible.
-- The backward reasoning is available BECAUSE the language is reversible.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileProgPresBack where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import RWhileTime
open import RWhileSIWf using (get-set-≡; get-set-≢)
open import RWhileTimeDet using (⇒-det)
open import RWhileTimeInv using (rupd-invol)
open import RWhileProgPres using (module PP)

private
  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  n≢j : ∀ {A B : Set} {a : A} → nothing ≡ just a → B
  n≢j ()

------------------------------------------------------------------------
-- 1.  Reading `rupd` backwards.  Each of these says what the slot must
--     have held, given what the update produced.

-- the update CLEARED the slot: the slot held exactly the assigned value
rupd-clear : ∀ w v → rupd w v ≡ just nil → w ≡ v
rupd-clear w v p = sym (just-inj (rupd-invol w v nil p))

-- the update left the assigned value in the slot: the slot was empty
rupd-fix : ∀ w v → rupd w v ≡ just v → w ≡ nil
rupd-fix w v p = sym (just-inj (trans (sym (rupd-self v)) (rupd-invol w v v p)))

-- XOR-ing a cons cell against a cons cell can only clear it (or fail): the
-- "assign nil is the identity" branch is unreachable, since a cons is never
-- nil.  This is what forbids `out` from holding rubbish before the emit.
rupd-cons : ∀ a b c d w → rupd (a ∙ b) (c ∙ d) ≡ just w → w ≡ nil
rupd-cons a b c d w p with eqV (a ∙ b) (c ∙ d)
... | true  = sym (just-inj p)
... | false = n≢j p

-- `tl u` is defined only on a cons, and then fixes its tail
tlM-cons : ∀ u v → tlM u ≡ just v → Σ[ a ∈ V ] (u ≡ a ∙ v)
tlM-cons (a ∙ b) v p = a , cong (a ∙_) (just-inj p)

------------------------------------------------------------------------
-- 2.  The backward run.

module PPBack (y self out : ℕ) (pd : V)
              (self≢y   : ¬ (self ≡ y))
              (self≢out : ¬ (self ≡ out))
              (out≢y    : ¬ (out ≡ y))
              where

  open PP y self out pd self≢y self≢out out≢y public

  ----------------------------------------------------------------------
  -- THE KEY LEMMA.  If a run of the emit suffix ends in a store satisfying
  -- p⁺'s `all_cleared` (everything but the output slot is nil), then the
  -- store it STARTED from had both fresh slots nil -- which is exactly the
  -- hypothesis `pp-cost` needs.

  emit-clean : ∀ {τ ρ l}
             → emit ⊢ τ ⇒ ρ ∣ l
             → (∀ z → ¬ (out ≡ z) → get ρ z ≡ nil)
             → (get τ self ≡ nil) × (get τ out ≡ nil)
  emit-clean {τ} (e-seq (e-ass {v = v₁} {u = u₁} ev₁ ru₁)
                 (e-seq (e-ass {v = v₂} {u = u₂} ev₂ ru₂)
                 (e-seq (e-ass {v = v₃} {u = u₃} ev₃ ru₃)
                        (e-ass {v = v₄} {u = u₄} ev₄ ru₄)))) hcl = gs , go
    where
      τ₁ τ₂ τ₃ : Store
      τ₁ = set τ  self u₁
      τ₂ = set τ₁ out  u₂
      τ₃ = set τ₂ self u₃

      -- what p⁺'s store invariant says about the final store
      hself : get (set τ₃ y u₄) self ≡ nil
      hself = hcl self out≢self

      hyfin : get (set τ₃ y u₄) y ≡ nil
      hyfin = hcl y out≢y

      u₃nil : u₃ ≡ nil
      u₃nil = trans (sym (trans (get-set-≢ τ₃ y self u₄ y≢self)
                                (get-set-≡ τ₂ self u₃)))
                    hself

      u₄nil : u₄ ≡ nil
      u₄nil = trans (sym (get-set-≡ τ₃ y u₄)) hyfin

      -- the two assignments of the constant ⌜p⌝ do assign ⌜p⌝
      v₁pd : v₁ ≡ pd
      v₁pd = sym (just-inj ev₁)

      v₃pd : v₃ ≡ pd
      v₃pd = sym (just-inj ev₃)

      ------------------------------------------------------------------
      -- (a) the scratch slot.

      g₂self : get τ₂ self ≡ u₁
      g₂self = trans (get-set-≢ τ₁ out self u₂ out≢self) (get-set-≡ τ self u₁)

      -- the third assignment cleared the slot, so the slot held ⌜p⌝ ...
      u₁pd : u₁ ≡ pd
      u₁pd = trans (sym g₂self)
                   (rupd-clear (get τ₂ self) pd
                     (subst (λ w → rupd (get τ₂ self) w ≡ just nil) v₃pd
                            (trans ru₃ (cong just u₃nil))))

      -- ... so the first assignment SET it, so it started nil.
      gs : get τ self ≡ nil
      gs = rupd-fix (get τ self) pd
             (subst (λ w → rupd (get τ self) w ≡ just pd) v₁pd
                    (trans ru₁ (cong just u₁pd)))

      ------------------------------------------------------------------
      -- (b) the output slot.

      g₃y : get τ₃ y ≡ get τ y
      g₃y = trans (get-set-≢ τ₂ self y u₃ self≢y)
            (trans (get-set-≢ τ₁ out  y u₂ out≢y)
                   (get-set-≢ τ  self y u₁ self≢y))

      -- the fourth assignment cleared p's answer slot, so `tl out` was
      -- p's answer
      gyv₄ : get τ y ≡ v₄
      gyv₄ = trans (sym g₃y)
                   (rupd-clear (get τ₃ y) v₄ (trans ru₄ (cong just u₄nil)))

      g₃out : get τ₃ out ≡ u₂
      g₃out = trans (get-set-≢ τ₂ self out u₃ self≢out) (get-set-≡ τ₁ out u₂)

      tl₂ : tlM u₂ ≡ just v₄
      tl₂ = subst (λ w → tlM w ≡ just v₄) g₃out ev₄

      g₁self : get τ₁ self ≡ u₁
      g₁self = get-set-≡ τ self u₁

      g₁y : get τ₁ y ≡ get τ y
      g₁y = get-set-≢ τ self y u₁ self≢y

      v₂eq : v₂ ≡ pd ∙ v₄
      v₂eq = trans (sym (just-inj ev₂))
                   (cong₂ _∙_ (trans g₁self u₁pd) (trans g₁y gyv₄))

      g₁out : get τ₁ out ≡ get τ out
      g₁out = get-set-≢ τ self out u₁ self≢out

      ru₂′ : rupd (get τ out) (pd ∙ v₄) ≡ just u₂
      ru₂′ = subst (λ w → rupd (get τ out) w ≡ just u₂) v₂eq
                   (subst (λ w → rupd w v₂ ≡ just u₂) g₁out ru₂)

      -- the second assignment produced a CONS, and XOR-ing a cons against a
      -- cons can only clear -- so the slot was nil to begin with.
      go : get τ out ≡ nil
      go with tlM-cons u₂ v₄ tl₂
      ... | a , u₂eq =
            rupd-cons a v₄ pd v₄ (get τ out)
              (subst (λ w → rupd w (pd ∙ v₄) ≡ just (get τ out)) u₂eq
                     (rupd-invol (get τ out) (pd ∙ v₄) u₂ ru₂′))

  ----------------------------------------------------------------------
  -- THE BACKWARD RUN, packaged.  Every run of p⁺ that respects p⁺'s store
  -- invariant IS a run of p followed by the emit -- same intermediate
  -- store, same answer, and the step count is p's + 8.
  --
  -- Together with RWhileProgPres.pp-cost this makes `PP p⁺ p` a genuine
  -- Kleene equality: p⁺ converges exactly where p does.

  pp-back : ∀ {body σ ρ m}
          → ppBody body ⊢ σ ⇒ ρ ∣ m
          → (∀ z → ¬ (out ≡ z) → get ρ z ≡ nil)
          → Σ[ τ ∈ Store ] Σ[ k ∈ ℕ ]
              ((body ⊢ σ ⇒ τ ∣ k)
               × (get τ self ≡ nil) × (get τ out ≡ nil)
               × (ρ ≡ final τ (get τ y)) × (m ≡ k + 8))
  pp-back (e-seq {t = τ} {k = k} db de) hcl with emit-clean de hcl
  ... | hs , ho =
        τ , k , db , hs , ho , proj₁ eq
      , trans (cong (λ n → suc (k + n)) (proj₂ eq)) (sym (+-suc k 7))
    where
      eq = ⇒-det de (emit-run τ (get τ y) hs ho refl)

------------------------------------------------------------------------
-- 3.  The backward direction, RUN inside the type checker, on the worked
--     example of RWhileProgPres.Examples (p = `V0 ^= 'seven`, ⌜p⌝ = atm 42).

module Examples where

  open PPBack 0 1 2 (atm 42) (λ ()) (λ ()) (λ ())

  σ₀ τ₀ : Store
  σ₀ = nil ∷ nil ∷ nil ∷ []
  τ₀ = atm 7 ∷ nil ∷ nil ∷ []

  bodyEx : Cmd
  bodyEx = 0 ^= opd (cst (atm 7))

  run-pp : ppBody bodyEx ⊢ σ₀ ⇒ final τ₀ (atm 7) ∣ 9
  run-pp = exec-sound 9 (ppBody bodyEx) σ₀ (final τ₀ (atm 7)) 9 refl

  -- p⁺'s store invariant: everything but slot 2 (OUT-PP) is nil
  cleanEx : ∀ z → ¬ (2 ≡ z) → get (final τ₀ (atm 7)) z ≡ nil
  cleanEx zero             _  = refl
  cleanEx (suc zero)       _  = refl
  cleanEx (suc (suc zero)) ne with ne refl
  ... | ()
  cleanEx (suc (suc (suc z))) _ = refl

  -- and the emit really is recovered: the store it began from had both
  -- fresh slots nil.
  back-ex : (get τ₀ 1 ≡ nil) × (get τ₀ 2 ≡ nil)
  back-ex = emit-clean (proj₂ (proj₂ (seq-of run-pp))) cleanEx
    where
      seq-of : ∀ {σ ρ m} → ppBody bodyEx ⊢ σ ⇒ ρ ∣ m
             → Σ[ τ ∈ Store ] Σ[ l ∈ ℕ ] (emit ⊢ τ ⇒ ρ ∣ l)
      seq-of (e-seq {t = τ} {l = l} _ de) = τ , l , de
