{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- p⁺ IS REVERSIBLE, AT THE SAME COST.
--
-- The point of insisting on a program-preserving basis is that a reversible
-- projection deals in reversible programs.  So p⁺ had better BE one whenever
-- p is.  Building on RWhileProgPres (the construction) and RWhileTimeInv
-- (cost-preserving syntactic inversion of the timed core) this module proves:
--
--   * `emit-Wf` / `pp-Wf`     the emit suffix is well-formed (`X ^= E` never
--                             mentions X), so p⁺ is well-formed whenever p is;
--   * `InR-emit` / `InR-pp`   p⁺ stays inside the store when p does and the
--                             two fresh slots are allocated;
--   * `pp-rev`                inv(p⁺) runs p⁺'s output back to p's input in
--                             EXACTLY the same number of steps, k + 8;
--   * `pp-injective`          two inputs that p⁺ maps to one store are equal.
--
-- Note what makes this cheap: `inv` on a sequence reverses it, so
-- `inv (body ⨾ emit) = inv emit ⨾ inv body` — the emit suffix is undone
-- first, restoring p's answer to Y, and then p itself is undone.  The three
-- fresh assignments of the emit are their own inverses (they are XOR
-- updates), which is exactly why `program_preserving` can be a *reversible*
-- transformation rather than a re-implementation.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileProgPresRev where

open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (⊔-lub)
open import Data.List using (length)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)

open import RWhileTime
open import RWhileSIWf
  using (Wf; wf-ass; wf-seq; NotIn; NotInO; ni-opd; ni-cns; ni-tl; ni-var; ni-cst
        ; InR)
open import RWhileTimeInv using (inv; inv-sound; inv-inv)
open import RWhileTimeDet using (⇒-det)
open import RWhileProgPres using (module PP)

module PPRev (y self out : ℕ) (pd : V)
             (self≢y   : ¬ (self ≡ y))
             (self≢out : ¬ (self ≡ out))
             (out≢y    : ¬ (out ≡ y))
             where

  open PP y self out pd self≢y self≢out out≢y public

  ----------------------------------------------------------------------
  -- 1.  Well-formedness: no assignment mentions the variable it updates.

  emit-Wf : Wf emit
  emit-Wf = wf-seq (wf-ass (ni-opd ni-cst))
            (wf-seq (wf-ass (ni-cns (ni-var out≢self) (ni-var out≢y)))
            (wf-seq (wf-ass (ni-opd ni-cst))
                    (wf-ass (ni-tl (ni-var y≢out)))))

  pp-Wf : ∀ {body} → Wf body → Wf (ppBody body)
  pp-Wf w = wf-seq w emit-Wf

  ----------------------------------------------------------------------
  -- 2.  Range: p⁺ touches exactly p's slots plus the two fresh ones.

  InR-emit : ∀ {σ} → suc y ≤ length σ → suc self ≤ length σ → suc out ≤ length σ
           → InR emit σ
  InR-emit hy hs ho =
    ⊔-lub (⊔-lub hs z≤n)
    (⊔-lub (⊔-lub ho (⊔-lub hs hy))
    (⊔-lub (⊔-lub hs z≤n) (⊔-lub hy ho)))

  InR-pp : ∀ {body σ} → InR body σ
         → suc y ≤ length σ → suc self ≤ length σ → suc out ≤ length σ
         → InR (ppBody body) σ
  InR-pp {σ = σ} irb hy hs ho = ⊔-lub irb (InR-emit {σ} hy hs ho)

  ----------------------------------------------------------------------
  -- 3.  The inverse program is the emit undone, then p undone.

  inv-ppBody : ∀ body → inv (ppBody body) ≡ (inv emit ⨾ inv body)
  inv-ppBody body = refl

  -- undoing the emit alone returns p's own final store.
  emit-rev : ∀ {τ σ′} v → InR emit τ
           → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
           → σ′ ≡ τ
           → inv emit ⊢ final τ v ⇒ σ′ ∣ 7
  emit-rev {τ} v ir hs ho hy refl = inv-sound emit-Wf ir (emit-run τ v hs ho hy)

  ----------------------------------------------------------------------
  -- 4.  MAIN THEOREM: p⁺ is reversible, and running it backwards costs
  --     exactly what running it forwards cost (k + 8).

  pp-rev : ∀ {body σ τ k} v → Wf body → InR (ppBody body) σ
         → body ⊢ σ ⇒ τ ∣ k
         → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
         → inv (ppBody body) ⊢ final τ v ⇒ σ ∣ (k + 8)
  pp-rev v w ir d hs ho hy = inv-sound (pp-Wf w) ir (pp-cost v d hs ho hy)

  ----------------------------------------------------------------------
  -- 5.  Semantic injectivity: p⁺ never merges two inputs.  (This is the
  --     property `RWhileJonesRev.pp-injective` states abstractly; here it is
  --     derived from syntactic inversion plus determinism, so it holds for
  --     the R-WHILE construction itself.)

  pp-injective : ∀ {body σ₁ σ₂ ρ k₁ k₂} → Wf body
               → InR (ppBody body) σ₁ → InR (ppBody body) σ₂
               → ppBody body ⊢ σ₁ ⇒ ρ ∣ k₁
               → ppBody body ⊢ σ₂ ⇒ ρ ∣ k₂
               → σ₁ ≡ σ₂
  pp-injective w ir₁ ir₂ d₁ d₂ =
    proj₁ (⇒-det (inv-sound (pp-Wf w) ir₁ d₁) (inv-sound (pp-Wf w) ir₂ d₂))

  -- ... and the backward run of p⁺ is deterministic too, so "the" inverse is
  -- well defined.
  pp-rev-cost : ∀ {body σ τ ρ k m} v → Wf body → InR (ppBody body) σ
              → body ⊢ σ ⇒ τ ∣ k
              → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
              → inv (ppBody body) ⊢ final τ v ⇒ ρ ∣ m
              → m ≡ k + 8
  pp-rev-cost v w ir d hs ho hy dinv =
    sym (proj₂ (⇒-det (pp-rev v w ir d hs ho hy) dinv))
