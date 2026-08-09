{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- DETERMINISM of the work meter.
--
-- RWhileTimeDet proves that the result store and the STEP count of a run
-- are uniquely determined.  The same is true of the WORK count, and it has
-- to be proved rather than inherited: `⇒-det` says nothing about the second
-- annotation, and a cost model that only gave upper bounds would not let us
-- say "p⁺ pays exactly |⌜p⌝| + 1 more", only "at most".
--
-- With `⇒w-det` in hand, `RWhileProgPresWork.pp-work` (a construction of
-- ONE work-annotated run) upgrades to a statement about THE work of p⁺,
-- exactly as `pp-cost-exact` does for the step count.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileWorkDet where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileWork
open import RWhileWorkV using (rupdW)

private
  tf : ∀ {A : Set} → (just true) ≡ (just false) → A
  tf ()

  ft : ∀ {A : Set} → (just false) ≡ (just true) → A
  ft ()

⇒w-det    : ∀ {c σ τ₁ τ₂ k₁ k₂ w₁ w₂}
          → c ⊢ σ ⇒ τ₁ ∣ k₁ ∥ w₁ → c ⊢ σ ⇒ τ₂ ∣ k₂ ∥ w₂
          → τ₁ ≡ τ₂ × k₁ ≡ k₂ × w₁ ≡ w₂
RestW-det : ∀ {e D L f σ τ₁ τ₂ n₁ n₂ w₁ w₂}
          → RestW e D L f σ τ₁ n₁ w₁ → RestW e D L f σ τ₂ n₂ w₂
          → τ₁ ≡ τ₂ × n₁ ≡ n₂ × w₁ ≡ w₂

⇒w-det w-skip w-skip = refl , refl , refl

⇒w-det {σ = σ} (w-ass {x = x} {e = e} {v = v₁} {u = u₁} ev₁ ru₁)
               (w-ass {v = v₂} {u = u₂} ev₂ ru₂) =
  cong (set σ x) u₁≡u₂ , refl , cong (λ v → expW σ e + rupdW (get σ x) v) v₁≡v₂
  where
    v₁≡v₂ : v₁ ≡ v₂
    v₁≡v₂ = just-injective (trans (sym ev₁) ev₂)
    u₁≡u₂ : u₁ ≡ u₂
    u₁≡u₂ = just-injective
              (trans (sym ru₁) (trans (cong (rupd (get σ x)) v₁≡v₂) ru₂))

⇒w-det (w-seq {l = l₁} {w′ = w′₁} d₁ d₂) (w-seq {l = l₂} {w′ = w′₂} d₁′ d₂′) =
  proj₁ snd
  , cong suc (cong₂ _+_ (proj₁ (proj₂ fst)) (proj₁ (proj₂ snd)))
  , cong₂ _+_ (proj₂ (proj₂ fst)) (proj₂ (proj₂ snd))
  where
    fst = ⇒w-det d₁ d₁′
    snd = ⇒w-det d₂ (subst (λ t → _ ⊢ t ⇒ _ ∣ l₂ ∥ w′₂) (sym (proj₁ fst)) d₂′)

⇒w-det {σ = σ} (w-then {e = e} {f = f} _ dc _) (w-then _ dc′ _) =
  proj₁ h
  , cong suc (proj₁ (proj₂ h))
  , cong₂ (λ w t → expW σ e + w + expW t f) (proj₂ (proj₂ h)) (proj₁ h)
  where h = ⇒w-det dc dc′
⇒w-det (w-then t₁ _ _) (w-else t₂ _ _) = tf (trans (sym t₁) t₂)
⇒w-det (w-else t₁ _ _) (w-then t₂ _ _) = ft (trans (sym t₁) t₂)
⇒w-det {σ = σ} (w-else {e = e} {f = f} _ dd _) (w-else _ dd′ _) =
  proj₁ h
  , cong suc (proj₁ (proj₂ h))
  , cong₂ (λ w t → expW σ e + w + expW t f) (proj₂ (proj₂ h)) (proj₁ h)
  where h = ⇒w-det dd dd′

⇒w-det {σ = σ} (w-loop {e = e} _ dD₁ r₁) (w-loop {n = n₂} {wr = wr₂} _ dD₂ r₂) =
  proj₁ rst
  , cong suc (cong₂ _+_ (proj₁ (proj₂ dD)) (proj₁ (proj₂ rst)))
  , cong₂ (λ w wr → expW σ e + w + wr) (proj₂ (proj₂ dD)) (proj₂ (proj₂ rst))
  where
    dD  = ⇒w-det dD₁ dD₂
    rst = RestW-det r₁
            (subst (λ t → RestW _ _ _ _ t _ n₂ wr₂) (sym (proj₁ dD)) r₂)

RestW-det (rw-exit _)  (rw-exit _)            = refl , refl , refl
RestW-det (rw-exit t₁) (rw-iter t₂ _ _ _ _)   = tf (trans (sym t₁) t₂)
RestW-det (rw-iter t₁ _ _ _ _) (rw-exit t₂)   = ft (trans (sym t₁) t₂)

RestW-det {e} {f = f} {σ = σ}
          (rw-iter _ dL₁ _ dD₁ r₁)
          (rw-iter {m = m₂} {n = n₂} {wd = wd₂} {wr = wr₂} _ dL₂ _ dD₂ r₂) =
    proj₁ rst
  , cong₂ _+_ (cong₂ _+_ (proj₁ (proj₂ dL)) (proj₁ (proj₂ dD)))
              (proj₁ (proj₂ rst))
  , work-eq
  where
    dL  = ⇒w-det dL₁ dL₂
    dD  = ⇒w-det dD₁ (subst (λ t → _ ⊢ t ⇒ _ ∣ m₂ ∥ wd₂) (sym (proj₁ dL)) dD₂)
    rst = RestW-det r₁
            (subst (λ t → RestW _ _ _ _ t _ n₂ wr₂) (sym (proj₁ dD)) r₂)
    -- the two runs share the store `x` reached by L, so `expW x e` matches
    work-eq : _ ≡ _
    work-eq =
      cong₂ _+_
        (cong₂ _+_
          (cong₂ (λ wl x → expW σ f + wl + expW x e)
                 (proj₂ (proj₂ dL)) (proj₁ dL))
          (proj₂ (proj₂ dD)))
        (proj₂ (proj₂ rst))
