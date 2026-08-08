{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- HOW MINIMAL IS p⁺?  Lower bounds in the timed core.
--
-- RWhileJonesRevCE refutes the strongest wish — p⁺ is NOT the cheapest of all
-- programs meeting the program-preserving obligation, because the obligation
-- is extensional and cost is not.  This module proves what IS true, namely
-- that p⁺ is essentially the cheapest *extension* of p, and that the
-- classical criterion is unsatisfiable for extensions at all:
--
--   * `ext-cost`           any run of `p ; e` costs at least cost(p) + 2;
--   * `ext-not-classical`  hence NO extension of p can satisfy the classical
--                          criterion `residual ≤ p`.  A residual obliged to
--                          run p and then emit ⌜p⌝ is such an extension, so
--                          measuring it against p measures the definition of
--                          the projection, not the specialiser.  This is the
--                          formal reason the basis has to move;
--   * `cost1-one-slot`     a one-step run changes at most one store slot;
--   * `two-slots-cost`     hence a run changing two slots costs at least 2;
--   * `ext-lb`             an extension whose suffix must fill an output slot
--                          AND clear p's answer slot — precisely the emit's
--                          obligation — costs at least cost(p) + 3;
--   * `gap` / `+8-not-≤`   p⁺ pays cost(p) + 8 (RWhileProgPres.pp-cost), so
--                          its overhead is within an additive 5 of that bound
--                          and is in every case a CONSTANT, never a factor.
--
-- The upshot for the criterion: `residual ≤ p⁺` is `residual ≤ p` relaxed by
-- an additive constant, and that constant is forced (up to +5) by the
-- obligation itself.  What is NOT claimed: that 8 is optimal.  The exact
-- optimum is a small synthesis problem over the four command forms, and the
-- flat-expression modelling of the OCaml `CRep` (see RWhileProgPres) would
-- make any such number an artefact of the model anyway.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileProgPresMin where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties
  using (+-comm; +-monoˡ-≤; +-monoʳ-≤
        ; suc-injective; m+n≡0⇒m≡0; n≤1+n; m≤n+m; ≤-trans; 1+n≰n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import RWhileTime
open import RWhileSIWf using (get-set-≢)
open import RWhileTimeDet using (⇒-det)

------------------------------------------------------------------------
-- 0.  Small arithmetic facts used below.

1≰0 : ¬ (1 ≤ 0)
1≰0 ()

suc≤+ : ∀ m l → 1 ≤ l → suc m ≤ m + l
suc≤+ m l h = subst (λ n → n ≤ m + l) (+-comm m 1) (+-monoʳ-≤ m h)

2+≤+ : ∀ m l → 2 ≤ l → suc (suc m) ≤ m + l
2+≤+ m l h = subst (λ n → n ≤ m + l) (+-comm m 2) (+-monoʳ-≤ m h)

------------------------------------------------------------------------
-- 1.  Extending a program costs at least two extra steps (the `⨾` node and
--     whatever the suffix does — every executed command node costs ≥ 1).

seq-lb : ∀ {c d σ τ k} → (c ⨾ d) ⊢ σ ⇒ τ ∣ k
       → Σ[ t ∈ Store ] Σ[ m ∈ ℕ ] (c ⊢ σ ⇒ t ∣ m) × (suc (suc m) ≤ k)
seq-lb (e-seq {t = t} {k = m} {l = l} d₁ d₂) =
  t , m , d₁ , s≤s (suc≤+ m l (cost-pos d₂))

ext-cost : ∀ {c d σ τ ρ k m} → c ⊢ σ ⇒ τ ∣ k → (c ⨾ d) ⊢ σ ⇒ ρ ∣ m
         → suc (suc k) ≤ m
ext-cost dc dseq with seq-lb dseq
... | t , k′ , dc′ , le = subst (λ n → suc (suc n) ≤ _) (proj₂ (⇒-det dc′ dc)) le

-- COROLLARY.  The classical Jones criterion is unsatisfiable for a residual
-- that runs p and then does anything at all.
ext-not-classical : ∀ {c d σ τ ρ k m} → c ⊢ σ ⇒ τ ∣ k → (c ⨾ d) ⊢ σ ⇒ ρ ∣ m
                  → ¬ (m ≤ k)
ext-not-classical {k = k} dc dseq le =
  1+n≰n {k} (≤-trans (≤-trans (n≤1+n (suc k)) (ext-cost dc dseq)) le)

------------------------------------------------------------------------
-- 2.  A one-step run changes at most one slot of the store.

cost1-one-slot : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k → k ≡ 1
               → Σ[ x ∈ ℕ ] (∀ z → ¬ (x ≡ z) → get τ z ≡ get σ z)
cost1-one-slot e-skip _ = 0 , λ z _ → refl
cost1-one-slot (e-ass {x = x} {s = σ} {u = u} _ _) _ =
  x , λ z ne → get-set-≢ σ x z u ne
cost1-one-slot (e-seq {k = k} {l = l} d₁ _) eq =
  ⊥-elim (1≰0 (subst (1 ≤_) (m+n≡0⇒m≡0 k (suc-injective eq)) (cost-pos d₁)))
cost1-one-slot (e-then {k = k} _ dc _) eq =
  ⊥-elim (1≰0 (subst (1 ≤_) (suc-injective eq) (cost-pos dc)))
cost1-one-slot (e-else {k = k} _ dd _) eq =
  ⊥-elim (1≰0 (subst (1 ≤_) (suc-injective eq) (cost-pos dd)))
cost1-one-slot (e-loop {k = k} {n = n} _ dD _) eq =
  ⊥-elim (1≰0 (subst (1 ≤_) (m+n≡0⇒m≡0 k (suc-injective eq)) (cost-pos dD)))

-- Hence: changing two DIFFERENT slots takes at least two steps.
two-slots-cost : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k
               → ∀ {a b} → ¬ (a ≡ b)
               → ¬ (get τ a ≡ get σ a) → ¬ (get τ b ≡ get σ b)
               → 2 ≤ k
two-slots-cost {k = zero} d ne na nb = ⊥-elim (1≰0 (cost-pos d))
two-slots-cost {k = suc zero} d {a} {b} ne na nb with cost1-one-slot d refl
... | x , h with x ≟ a
...   | no  x≢a = ⊥-elim (na (h a x≢a))
...   | yes refl = ⊥-elim (nb (h b ne))
two-slots-cost {k = suc (suc _)} d ne na nb = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- 3.  The lower bound for an extension carrying the emit's obligation.
--
-- The emit must (i) fill the fresh output slot with ⟨⌜p⌝ , answer⟩ and
-- (ii) clear p's answer slot (R-WHILE's `all_cleared`).  Those are two
-- distinct slots, so:

ext-lb : ∀ {c d σ τ ρ k m} → c ⊢ σ ⇒ τ ∣ k → (c ⨾ d) ⊢ σ ⇒ ρ ∣ m
       → ∀ {a b} → ¬ (a ≡ b)
       → ¬ (get ρ a ≡ get τ a) → ¬ (get ρ b ≡ get τ b)
       → 3 + k ≤ m
ext-lb {k = k} dc (e-seq {t = t} {k = k₁} {l = l} d₁ d₂) ne na nb
  with ⇒-det d₁ dc
... | refl , refl = s≤s (2+≤+ k l (two-slots-cost d₂ ne na nb))

------------------------------------------------------------------------
-- 4.  Comparing with what p⁺ actually pays (RWhileProgPres.pp-cost: k + 8).

-- the construction is within an additive 5 of the bound above
gap : ∀ k → 3 + k ≤ k + 8
gap k = subst (λ n → 3 + k ≤ n) (sym (+-comm k 8)) (+-monoˡ-≤ k (s≤s (s≤s (s≤s z≤n))))

-- and it is strictly dearer than p — so p⁺ never satisfies the CLASSICAL
-- criterion against p, whatever p is.  (The same fact as
-- `ext-not-classical`, stated on the constant the construction pays.)
+8-not-≤ : ∀ k → ¬ (k + 8 ≤ k)
+8-not-≤ k h =
  1+n≰n {7 + k} (≤-trans (subst (λ n → n ≤ k) (+-comm k 8) h) (m≤n+m k 7))
