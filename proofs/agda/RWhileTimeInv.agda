{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Program inversion for the TIMED semantics, and its soundness.
--
-- `inv c` is the syntactic inverse of `c` (the Agda counterpart of
-- src/InvRwhile.ml): sequences are reversed, a conditional's test and
-- assertion are swapped, and a loop's entry test and exit assertion are
-- swapped.  Assignments are their own inverse -- that is the whole point of
-- `^=` being the partial involution `rupd`.
--
-- The theorem is COST-PRESERVING:
--
--     c ⊢ σ ⇒ τ ∣ k   ⟹   inv c ⊢ τ ⇒ σ ∣ k       (same k)
--
-- Running a program backwards costs exactly what running it forwards did.
-- Combined with `RWhileSISim.si-linear` this gives linear-time *inverse*
-- interpretation for free (see RWhileSIInv).
--
-- The loop case is the interesting one: the backward run visits the same
-- stores in the opposite order, but its iterations are SHIFTED by one --
-- each backward iteration pairs `inv L` of one forward iteration with
-- `inv D` of the PREVIOUS one.  `inv-rest` therefore walks the forward
-- `Rest` while accumulating the backward `Rest`, carrying the backward run
-- of the `D` that led into the current store.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileTimeInv where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-comm; +-identityʳ; ≤-trans; ≤-refl; ≤-reflexive; ≤-antisym
        ; ⊔-comm; ⊔-lub; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

open import RWhileTime
open import RWhileSIEnc using (vmax; vmaxᵉ; vmaxᵒ)
open import RWhileSIWf

------------------------------------------------------------------------
-- 1.  Store: undoing a `set`.

set-get : ∀ σ x u → x < length σ → set (set σ x u) x (get σ x) ≡ σ
set-get (w ∷ σ) zero    u _        = refl
set-get (w ∷ σ) (suc x) u (s≤s lt) = cong (w ∷_) (set-get σ x u lt)

------------------------------------------------------------------------
-- 2.  Equality tests are sound (needed to invert `rupd`).

eqℕ-sound : ∀ m n → eqℕ m n ≡ true → m ≡ n
eqℕ-sound zero    zero    _ = refl
eqℕ-sound (suc m) (suc n) p = cong suc (eqℕ-sound m n p)

private
  f≢t : ∀ {A : Set} → false ≡ true → A
  f≢t ()

  n≢j : ∀ {A B : Set} {a : A} → nothing ≡ just a → B
  n≢j ()

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  ∙-cong : ∀ {a c b d} → a ≡ c → b ≡ d → (a ∙ b) ≡ (c ∙ d)
  ∙-cong refl refl = refl

eqV-sound : ∀ u v → eqV u v ≡ true → u ≡ v
eqV-sound nil     nil     _ = refl
eqV-sound (atm m) (atm n) p = cong atm (eqℕ-sound m n p)
eqV-sound (a ∙ b) (c ∙ d) p with eqV a c in q
... | true  = ∙-cong (eqV-sound a c q) (eqV-sound b d p)
... | false = f≢t p

------------------------------------------------------------------------
-- 3.  `rupd` is a partial involution: the very property that makes `^=`
--     reversible in src/EvalRwhile.ml.

rupd-invol : ∀ w v u → rupd w v ≡ just u → rupd u v ≡ just w
rupd-invol nil     v u refl = rupd-self v
rupd-invol (atm m) v u p with eqV (atm m) v in q
... | true  = subst (λ w → rupd w v ≡ just (atm m)) (just-inj p)
                    (cong just (sym (eqV-sound (atm m) v q)))
... | false = n≢j p
rupd-invol (a ∙ b) v u p with eqV (a ∙ b) v in q
... | true  = subst (λ w → rupd w v ≡ just (a ∙ b)) (just-inj p)
                    (cong just (sym (eqV-sound (a ∙ b) v q)))
... | false = n≢j p

------------------------------------------------------------------------
-- 4.  Program inversion (mirrors src/InvRwhile.ml).

inv : Cmd → Cmd
inv skip           = skip
inv (x ^= e)       = x ^= e
inv (c ⨾ d)        = inv d ⨾ inv c
inv (cond e c d f) = cond f (inv c) (inv d) e
inv (loop e D L f) = loop f (inv D) (inv L) e

inv-inv : ∀ c → inv (inv c) ≡ c
inv-inv skip           = refl
inv-inv (x ^= e)       = refl
inv-inv (c ⨾ d)        = cong₂′ (inv-inv c) (inv-inv d)
  where
    cong₂′ : ∀ {c₁ c₂ d₁ d₂} → c₁ ≡ c₂ → d₁ ≡ d₂ → (c₁ ⨾ d₁) ≡ (c₂ ⨾ d₂)
    cong₂′ refl refl = refl
inv-inv (cond e c d f) = go (inv-inv c) (inv-inv d)
  where
    go : ∀ {c₁ c₂ d₁ d₂} → c₁ ≡ c₂ → d₁ ≡ d₂ → cond e c₁ d₁ f ≡ cond e c₂ d₂ f
    go refl refl = refl
inv-inv (loop e D L f) = go (inv-inv D) (inv-inv L)
  where
    go : ∀ {D₁ D₂ L₁ L₂} → D₁ ≡ D₂ → L₁ ≡ L₂ → loop e D₁ L₁ f ≡ loop e D₂ L₂ f
    go refl refl = refl

Wf-inv : ∀ {c} → Wf c → Wf (inv c)
Wf-inv wf-skip           = wf-skip
Wf-inv (wf-ass ni)       = wf-ass ni
Wf-inv (wf-seq w₁ w₂)    = wf-seq (Wf-inv w₂) (Wf-inv w₁)
Wf-inv (wf-cond w₁ w₂)   = wf-cond (Wf-inv w₁) (Wf-inv w₂)
Wf-inv (wf-loop w₁ w₂)   = wf-loop (Wf-inv w₁) (Wf-inv w₂)

------------------------------------------------------------------------
-- 5.  Inversion does not move variables, so "in range" is preserved.

private
  in1 : ∀ a b c d → a ≤ a ⊔ b ⊔ c ⊔ d
  in1 a b c d = ≤-trans (m≤m⊔n a b) (≤-trans (m≤m⊔n (a ⊔ b) c) (m≤m⊔n (a ⊔ b ⊔ c) d))
  in2 : ∀ a b c d → b ≤ a ⊔ b ⊔ c ⊔ d
  in2 a b c d = ≤-trans (m≤n⊔m a b) (≤-trans (m≤m⊔n (a ⊔ b) c) (m≤m⊔n (a ⊔ b ⊔ c) d))
  in3 : ∀ a b c d → c ≤ a ⊔ b ⊔ c ⊔ d
  in3 a b c d = ≤-trans (m≤n⊔m (a ⊔ b) c) (m≤m⊔n (a ⊔ b ⊔ c) d)
  in4 : ∀ a b c d → d ≤ a ⊔ b ⊔ c ⊔ d
  in4 a b c d = m≤n⊔m (a ⊔ b ⊔ c) d

  -- the only rearrangement inversion needs: the outer two swap
  ⊔4-swap : ∀ a b c d → d ⊔ b ⊔ c ⊔ a ≡ a ⊔ b ⊔ c ⊔ d
  ⊔4-swap a b c d =
    ≤-antisym
      (⊔-lub (⊔-lub (⊔-lub (in4 a b c d) (in2 a b c d)) (in3 a b c d)) (in1 a b c d))
      (⊔-lub (⊔-lub (⊔-lub (in4 d b c a) (in2 d b c a)) (in3 d b c a)) (in1 d b c a))

vmax-inv : ∀ c → vmax (inv c) ≡ vmax c
vmax-inv skip           = refl
vmax-inv (x ^= e)       = refl
vmax-inv (c ⨾ d)        rewrite vmax-inv c | vmax-inv d = ⊔-comm (vmax d) (vmax c)
vmax-inv (cond e c d f) rewrite vmax-inv c | vmax-inv d =
  ⊔4-swap (vmaxᵉ e) (vmax c) (vmax d) (vmaxᵉ f)
vmax-inv (loop e D L f) rewrite vmax-inv D | vmax-inv L =
  ⊔4-swap (vmaxᵉ e) (vmax D) (vmax L) (vmaxᵉ f)

inR-inv : ∀ {c σ} → InR c σ → InR (inv c) σ
inR-inv {c} ir = ≤-trans (≤-reflexive (vmax-inv c)) ir

------------------------------------------------------------------------
-- 6.  SOUNDNESS OF INVERSION, with the cost preserved exactly.

private
  cast≤ : ∀ {a m n} → n ≡ m → a ≤ m → a ≤ n
  cast≤ eq le = subst (_ ≤_) (sym eq) le

  -- the loop's bookkeeping: the backward run pairs `inv L` of one forward
  -- iteration with `inv D` of the previous one, so the costs come out
  -- permuted -- and only permuted.
  rot : ∀ a b a′ n′ q → suc (a′ + (n′ + (b + a + q))) ≡ suc (a + (b + a′ + n′ + q))
  rot a b a′ n′ q = cong suc (go a b a′ n′ q)
    where
      go : ∀ a b a′ n′ q → a′ + (n′ + (b + a + q)) ≡ a + (b + a′ + n′ + q)
      go = solve 5 (λ a b a′ n′ q → a′ :+ (n′ :+ (b :+ a :+ q)) :=
                                    a :+ (b :+ a′ :+ n′ :+ q)) refl

inv-sound : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k → inv c ⊢ τ ⇒ σ ∣ k

-- Walking the forward `Rest` while accumulating the backward one.
-- `invD` is the backward run of the `D` that led into the current store `w`,
-- and `acc` is the part of the backward loop already built.
inv-rest : ∀ {e D L f w z n} → Wf D → Wf L → InR (loop e D L f) w
         → Rest e D L f w z n
         → ∀ {v s a q}
         → inv D ⊢ w ⇒ v ∣ a
         → Rest f (inv D) (inv L) e v s q
         → loop f (inv D) (inv L) e ⊢ z ⇒ s ∣ suc (a + (n + q))

inv-sound _ _ e-skip = e-skip

inv-sound {x ^= e} {σ} (wf-ass ni) ir (e-ass {v = v} {u = u} ev ru) =
  subst (λ ρ → (x ^= e) ⊢ set σ x u ⇒ ρ ∣ 1)
        (set-get σ x u (ass-in-range {x} {e} {σ} ir))
        (e-ass (trans (evalE-frame σ x u e ni) ev)
               (subst (λ w → rupd w v ≡ just (get σ x)) (sym (get-set-≡ σ x u))
                      (rupd-invol (get σ x) v u ru)))

inv-sound {c ⨾ d} {σ} (wf-seq w₁ w₂) ir (e-seq {t = t} {u = u} {k = k} {l = l} d₁ d₂) =
  subst (λ i → (inv d ⨾ inv c) ⊢ u ⇒ σ ∣ i) (cong suc (+-comm l k))
        (e-seq (inv-sound w₂ ird d₂) (inv-sound w₁ irc d₁))
  where
    irc = inR-seqˡ {c} {d} {σ} ir
    ird = cast≤ (⇒-length irc d₁) (inR-seqʳ {c} {d} {σ} ir)

inv-sound {cond e c d f} {σ} (wf-cond w₁ w₂) ir (e-then te dc tf) =
  e-then tf (inv-sound w₁ (inR-condˡ {e} {c} {d} {f} {σ} ir) dc) te

inv-sound {cond e c d f} {σ} (wf-cond w₁ w₂) ir (e-else te dd tf) =
  e-else tf (inv-sound w₂ (inR-condʳ {e} {c} {d} {f} {σ} ir) dd) te

inv-sound {loop e D L f} {σ} (wf-loop w₁ w₂) ir
          (e-loop {t = t} {u = u} {k = k} {n = n} te dD rest) =
  subst (λ i → loop f (inv D) (inv L) e ⊢ u ⇒ σ ∣ i)
        (cong suc (cong (k +_) (+-identityʳ n)))
        (inv-rest w₁ w₂ irT rest (inv-sound w₁ irD dD) (r-exit te))
  where
    irD = inR-loopˡ {e} {D} {L} {f} {σ} ir
    irT = cast≤ (⇒-length irD dD) ir

inv-rest _ _ _ (r-exit tf) invD acc = e-loop tf invD acc

inv-rest {e} {D} {L} {f} {w} {z} wfD wfL ir
         (r-iter {x = x} {k = b} {m = a′} {n = n′} ff dL fe dD rest)
         {s = s} {a = a} {q = q} invD acc =
  subst (λ i → loop f (inv D) (inv L) e ⊢ z ⇒ s ∣ i) (rot a b a′ n′ q)
        (inv-rest wfD wfL irY rest (inv-sound wfD irDx dD)
                  (r-iter fe (inv-sound wfL irL dL) ff invD acc))
  where
    irL  = inR-loopʳ {e} {D} {L} {f} {w} ir
    irX  = cast≤ (⇒-length irL dL) ir
    irDx = inR-loopˡ {e} {D} {L} {f} {x} irX
    irY  = cast≤ (⇒-length irDx dD) irX

------------------------------------------------------------------------
-- 7.  Executable tests (checked by the type checker via `exec`).

private
  -- X0 ^= 'a ; X1 ^= X0     on the empty store [nil,nil]
  p₁ : Cmd
  p₁ = (0 ^= opd (cst (atm 1))) ⨾ (1 ^= opd (var 0))

  test-p₁ : exec 10 p₁ (nil ∷ nil ∷ []) ≡ just (atm 1 ∷ atm 1 ∷ [] , 3)
  test-p₁ = refl

  -- the inverse is the reversed sequence, and it undoes p₁ at the same cost
  test-inv-p₁-syntax : inv p₁ ≡ ((1 ^= opd (var 0)) ⨾ (0 ^= opd (cst (atm 1))))
  test-inv-p₁-syntax = refl

  test-inv-p₁ : exec 10 (inv p₁) (atm 1 ∷ atm 1 ∷ []) ≡ just (nil ∷ nil ∷ [] , 3)
  test-inv-p₁ = refl

  -- a loop: from (=? X0 nil) do skip loop (X0 ^= '7) until (=? X0 '7)
  lp : Cmd
  lp = loop (eqE (var 0) (cst nil)) skip (0 ^= opd (cst (atm 7))) (eqE (var 0) (cst (atm 7)))

  test-lp : exec 20 lp (nil ∷ []) ≡ just (atm 7 ∷ [] , 4)
  test-lp = refl

  -- inversion swaps the loop's entry test and exit assertion
  test-inv-lp-syntax :
    inv lp ≡ loop (eqE (var 0) (cst (atm 7))) skip (0 ^= opd (cst (atm 7)))
                  (eqE (var 0) (cst nil))
  test-inv-lp-syntax = refl

  -- ... and the backward run costs exactly the 4 steps the forward one did
  test-inv-lp : exec 20 (inv lp) (atm 7 ∷ []) ≡ just (nil ∷ [] , 4)
  test-inv-lp = refl

  test-inv-inv : inv (inv lp) ≡ lp
  test-inv-inv = refl
