{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- COMPLETENESS of the fuel-indexed evaluator.
--
-- `RWhileTime.exec-sound` says a computed run is a derivation.  This module
-- proves the converse: every derivation is FOUND by `exec`, given enough
-- fuel.  Together with `exec-sound` and determinism (`RWhileTimeDet`) the
-- relation and the executable evaluator agree completely, so
--
--     "c has no terminating run from σ"  ⟺  "exec n c σ ≡ nothing for all n"
--
-- which is the honest handle on divergence in a big-step setting: the
-- semantics says nothing about non-terminating programs, and now that fact
-- is a theorem about `exec` rather than an informal remark.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileTimeExec where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m∸n+n≡m; ≤-refl; ≤-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime

------------------------------------------------------------------------
-- 1.  More fuel never hurts.

exec-mono  : ∀ n c s r → exec n c s ≡ just r → exec (suc n) c s ≡ just r
execR-mono : ∀ n e D L f w r → execR n e D L f w ≡ just r → execR (suc n) e D L f w ≡ just r

exec-mono (suc n) skip     s r eq = eq
exec-mono (suc n) (x ^= e) s r eq = eq

exec-mono (suc n) (c ⨾ d) s r eq with bind-inv (exec n c s) _ eq
... | (t , k) , ec , rest with bind-inv (exec n d t) _ rest
...   | (u , l) , ed , fin
      rewrite exec-mono n c s (t , k) ec | exec-mono n d t (u , l) ed = fin

exec-mono (suc n) (cond e c d f) s r eq with bind-inv (evalT s e) _ eq
... | true  , et , rest with bind-inv (exec n c s) _ rest
...   | (t , k) , ec , rest₂ with bind-inv (evalT t f) _ rest₂
...     | true  , ef , fin
        rewrite et | exec-mono n c s (t , k) ec | ef = fin
...     | false , ef , ()
exec-mono (suc n) (cond e c d f) s r eq | false , et , rest with bind-inv (exec n d s) _ rest
...   | (t , k) , ed , rest₂ with bind-inv (evalT t f) _ rest₂
...     | true  , ef , ()
...     | false , ef , fin
        rewrite et | exec-mono n d s (t , k) ed | ef = fin

exec-mono (suc n) (loop e D L f) s r eq with bind-inv (evalT s e) _ eq
... | true  , et , rest with bind-inv (exec n D s) _ rest
...   | (t , k) , eD , rest₂ with bind-inv (execR n e D L f t) _ rest₂
...     | (u , m) , eR , fin
        rewrite et | exec-mono n D s (t , k) eD | execR-mono n e D L f t (u , m) eR = fin
exec-mono (suc n) (loop e D L f) s r eq | false , et , ()

execR-mono (suc n) e D L f w r eq with bind-inv (evalT w f) _ eq
... | true  , ef , fin rewrite ef = fin
... | false , ef , rest with bind-inv (exec n L w) _ rest
...   | (x , k) , eL , rest₂ with bind-inv (evalT x e) _ rest₂
...     | true  , ee , ()
...     | false , ee , rest₃ with bind-inv (exec n D x) _ rest₃
...       | (y , m) , eD , rest₄ with bind-inv (execR n e D L f y) _ rest₄
...         | (z , p) , eR , fin
            rewrite ef | exec-mono n L w (x , k) eL | ee
                  | exec-mono n D x (y , m) eD
                  | execR-mono n e D L f y (z , p) eR = fin

------------------------------------------------------------------------
-- 2.  Raising the fuel to any larger amount.

exec-plus : ∀ i n c s r → exec n c s ≡ just r → exec (i + n) c s ≡ just r
exec-plus zero    n c s r eq = eq
exec-plus (suc i) n c s r eq = exec-mono (i + n) c s r (exec-plus i n c s r eq)

execR-plus : ∀ i n e D L f w r → execR n e D L f w ≡ just r → execR (i + n) e D L f w ≡ just r
execR-plus zero    n e D L f w r eq = eq
execR-plus (suc i) n e D L f w r eq = execR-mono (i + n) e D L f w r (execR-plus i n e D L f w r eq)

exec-≤ : ∀ {n m c s r} → n ≤ m → exec n c s ≡ just r → exec m c s ≡ just r
exec-≤ {n} {m} {c} {s} {r} le eq =
  subst (λ i → exec i c s ≡ just r) (m∸n+n≡m le) (exec-plus (m ∸ n) n c s r eq)

execR-≤ : ∀ {n m e D L f w r} → n ≤ m → execR n e D L f w ≡ just r → execR m e D L f w ≡ just r
execR-≤ {n} {m} {e} {D} {L} {f} {w} {r} le eq =
  subst (λ i → execR i e D L f w ≡ just r) (m∸n+n≡m le) (execR-plus (m ∸ n) n e D L f w r eq)

------------------------------------------------------------------------
-- 3.  COMPLETENESS: every derivation is found, given enough fuel.

exec-complete  : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k → Σ[ n ∈ ℕ ] exec n c σ ≡ just (τ , k)
execR-complete : ∀ {e D L f σ τ n} → Rest e D L f σ τ n
               → Σ[ m ∈ ℕ ] execR m e D L f σ ≡ just (τ , n)

exec-complete e-skip = 1 , refl

exec-complete {σ = σ} (e-ass {x = x} {e = e} {v = v} {u = u} ev ru) = 1 , go
  where
    go : exec 1 (x ^= e) σ ≡ just (set σ x u , 1)
    go rewrite ev | ru = refl

exec-complete {σ = σ} (e-seq {c = c} {d = d} {u = u} {k = k} {l = l} d₁ d₂) =
  suc (n₁ ⊔ n₂) , go
  where
    h₁ = exec-complete d₁
    h₂ = exec-complete d₂
    n₁ = proj₁ h₁
    n₂ = proj₁ h₂
    go : exec (suc (n₁ ⊔ n₂)) (c ⨾ d) σ ≡ just (u , suc (k + l))
    go rewrite exec-≤ (m≤m⊔n n₁ n₂) (proj₂ h₁)
             | exec-≤ (m≤n⊔m n₁ n₂) (proj₂ h₂) = refl

exec-complete {σ = σ} (e-then {e = e} {c = c} {d = d} {f = f} {t = t} {k = k} te dc tf) =
  suc (proj₁ h) , go
  where
    h = exec-complete dc
    go : exec (suc (proj₁ h)) (cond e c d f) σ ≡ just (t , suc k)
    go rewrite te | proj₂ h | tf = refl

exec-complete {σ = σ} (e-else {e = e} {c = c} {d = d} {f = f} {t = t} {k = k} te dd tf) =
  suc (proj₁ h) , go
  where
    h = exec-complete dd
    go : exec (suc (proj₁ h)) (cond e c d f) σ ≡ just (t , suc k)
    go rewrite te | proj₂ h | tf = refl

exec-complete {σ = σ} (e-loop {e = e} {D = D} {L = L} {f = f} {u = u} {k = k} {n = n}
                              te dD rest) =
  suc (n₁ ⊔ n₂) , go
  where
    h₁ = exec-complete dD
    h₂ = execR-complete rest
    n₁ = proj₁ h₁
    n₂ = proj₁ h₂
    go : exec (suc (n₁ ⊔ n₂)) (loop e D L f) σ ≡ just (u , suc (k + n))
    go rewrite te | exec-≤ (m≤m⊔n n₁ n₂) (proj₂ h₁)
             | execR-≤ (m≤n⊔m n₁ n₂) (proj₂ h₂) = refl

execR-complete {e} {D} {L} {f} {σ} (r-exit tf) = 1 , go
  where
    go : execR 1 e D L f σ ≡ just (σ , 0)
    go rewrite tf = refl

execR-complete {e} {D} {L} {f} {σ} {τ}
               (r-iter {k = k} {m = m} {n = n} ff dL fe dD rest) =
  suc (n₁ ⊔ (n₂ ⊔ n₃)) , go
  where
    h₁ = exec-complete dL
    h₂ = exec-complete dD
    h₃ = execR-complete rest
    n₁ = proj₁ h₁
    n₂ = proj₁ h₂
    n₃ = proj₁ h₃
    go : execR (suc (n₁ ⊔ (n₂ ⊔ n₃))) e D L f σ ≡ just (τ , k + m + n)
    go rewrite ff
             | exec-≤ (m≤m⊔n n₁ (n₂ ⊔ n₃)) (proj₂ h₁) | fe
             | exec-≤ (≤-trans (m≤m⊔n n₂ n₃) (m≤n⊔m n₁ (n₂ ⊔ n₃))) (proj₂ h₂)
             | execR-≤ (≤-trans (m≤n⊔m n₂ n₃) (m≤n⊔m n₁ (n₂ ⊔ n₃))) (proj₂ h₃) = refl

------------------------------------------------------------------------
-- 4.  What this says about NON-terminating programs.
--
-- The big-step relation only describes terminating runs.  With soundness
-- AND completeness, "there is no terminating run" is exactly "the evaluator
-- never returns", which is a statement one can actually check:
--
--   NOTE what it does NOT say: `exec n c σ ≡ nothing` for all n lumps
--   together a program that loops forever and one that gets STUCK (a failed
--   `rupd`, or a conditional whose exit assertion does not hold).  The
--   timed semantics cannot tell those apart -- distinguishing them needs a
--   small-step semantics, which is outside this development.

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

no-run→exec-nothing : ∀ {c σ} → (∀ {τ k} → c ⊢ σ ⇒ τ ∣ k → ⊥)
                    → ∀ n → exec n c σ ≡ nothing
no-run→exec-nothing {c} {σ} nr n with exec n c σ in eq
... | nothing      = refl
... | just (t , k) = ⊥-elim (nr (exec-sound n c σ t k eq))

exec-nothing→no-run : ∀ {c σ} → (∀ n → exec n c σ ≡ nothing)
                    → ∀ {τ k} → c ⊢ σ ⇒ τ ∣ k → ⊥
exec-nothing→no-run {c} {σ} ex d = bad (trans (sym (proj₂ h)) (ex (proj₁ h)))
  where
    h = exec-complete d
    bad : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
    bad ()
