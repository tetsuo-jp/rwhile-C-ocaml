{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Pure-arithmetic scaffolding for the composition in RWhileSISim.
--
-- Each lemma packages the bound bookkeeping of one object-level case: the
-- constants contributed by the dispatch steps, the induction hypotheses'
-- budgets (`jᵢ + SL ≤ CC * kᵢ`) and the case's side condition (`cond*`),
-- yielding the case's goal `j + SL ≤ CC * k`.  Keeping this separate from
-- RWhileSISim keeps the (very large) machine-state types out of the
-- arithmetic, which is what makes the composition elaborate cheaply.
--
-- --safe, no postulates, no holes.
module RWhileSIArith where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

-- C * suc n = C + C * n  (already *-suc); C * (k+l) = C*k + C*l (*-distribˡ-+)
eqSuc : ∀ C k l → C * suc (k + l) ≡ C + (C * k + C * l)
eqSuc C k l = trans (*-suc C (k + l)) (cong (C +_) (*-distribˡ-+ C k l))

lemAss : ∀ {j A S C} → j ≤ suc A → A + 1 + S ≤ C → j + S ≤ C * 1
lemAss {j} {A} {S} {C} h1 h2 =
  ≤-trans (+-monoˡ-≤ S (≤-trans h1 (≤-reflexive (+-comm 1 A))))
          (≤-trans h2 (≤-reflexive (sym (*-identityʳ C))))

lemSeq : ∀ {j₁ j₂ j₃ j₄ S C k l}
       → j₁ ≤ 81 → j₄ ≤ 82 → j₂ + S ≤ C * k → j₃ + S ≤ C * l → 163 ≤ C + S
       → (j₁ + (j₂ + (j₃ + j₄))) + S ≤ C * suc (k + l)
lemSeq {j₁} {j₂} {j₃} {j₄} {S} {C} {k} {l} h1 h4 h2 h3 hc =
  ≤-trans (+-monoˡ-≤ S (+-mono-≤ h1 (+-monoʳ-≤ j₂ (+-monoʳ-≤ j₃ h4))))
    (≤-trans (≤-reflexive (e1 j₂ j₃ S))
      (≤-trans (+-monoˡ-≤ (j₂ + (j₃ + S)) hc)
        (≤-trans (≤-reflexive (e2 C j₂ j₃ S))
          (≤-trans (+-monoʳ-≤ C (+-mono-≤ h2 h3))
                   (≤-reflexive (sym (eqSuc C k l)))))))
  where
    e1 : ∀ a b s → (81 + (a + (b + 82))) + s ≡ 163 + (a + (b + s))
    e1 = solve 3 (λ a b s → (con 81 :+ (a :+ (b :+ con 82))) :+ s :=
                            con 163 :+ (a :+ (b :+ s))) refl
    e2 : ∀ c a b s → (c + s) + (a + (b + s)) ≡ c + ((a + s) + (b + s))
    e2 = solve 4 (λ c a b s → (c :+ s) :+ (a :+ (b :+ s)) :=
                              c :+ ((a :+ s) :+ (b :+ s))) refl

lemCond : ∀ {j₁ j₂ j₃ P Q S C k}
        → j₁ ≤ suc P → j₃ ≤ suc Q → j₂ + S ≤ C * k → P + Q + 2 ≤ C
        → (j₁ + (j₂ + j₃)) + S ≤ C * suc k
lemCond {j₁} {j₂} {j₃} {P} {Q} {S} {C} {k} h1 h3 h2 hc =
  ≤-trans (+-monoˡ-≤ S (+-mono-≤ h1 (+-monoʳ-≤ j₂ h3)))
    (≤-trans (≤-reflexive (e1 P Q j₂ S))
      (≤-trans (+-monoˡ-≤ (j₂ + S) hc)
        (≤-trans (+-monoʳ-≤ C h2) (≤-reflexive (sym (*-suc C k))))))
  where
    e1 : ∀ p q a s → (suc p + (a + suc q)) + s ≡ (p + q + 2) + (a + s)
    e1 = solve 4 (λ p q a s → (con 1 :+ p :+ (a :+ (con 1 :+ q))) :+ s :=
                              (p :+ q :+ con 2) :+ (a :+ s)) refl

lemLoop : ∀ {j₁ j₂ j₃ j₄ P S C k n}
        → j₁ ≤ 55 → j₂ ≤ suc P → j₃ + S ≤ C * k → j₄ ≤ C * n + S → 56 + P + S ≤ C
        → (j₁ + (j₂ + (j₃ + j₄))) + S ≤ C * suc (k + n)
lemLoop {j₁} {j₂} {j₃} {j₄} {P} {S} {C} {k} {n} h1 h2 h3 h4 hc =
  ≤-trans (+-monoˡ-≤ S (+-mono-≤ h1 (+-mono-≤ h2 (+-monoʳ-≤ j₃ h4))))
    (≤-trans (≤-reflexive (e1 P j₃ (C * n) S))
      (≤-trans (+-monoˡ-≤ ((j₃ + S) + C * n) hc)
        (≤-trans (≤-reflexive (e2 C (j₃ + S) (C * n)))
          (≤-trans (+-monoʳ-≤ C (+-monoˡ-≤ (C * n) h3))
                   (≤-reflexive (sym (eqSuc C k n)))))))
  where
    e1 : ∀ p a b s → (55 + (suc p + (a + (b + s)))) + s ≡ (56 + p + s) + ((a + s) + b)
    e1 = solve 4 (λ p a b s → (con 55 :+ (con 1 :+ p :+ (a :+ (b :+ s)))) :+ s :=
                              (con 56 :+ p :+ s) :+ ((a :+ s) :+ b)) refl
    e2 : ∀ c a b → c + (a + b) ≡ c + (a + b)
    e2 _ _ _ = refl

lemExit : ∀ {j₁ j₂ D S C} → j₁ ≤ suc D → j₂ ≤ 58 → D + 59 ≤ S → j₁ + j₂ ≤ C * 0 + S
lemExit {j₁} {j₂} {D} {S} {C} h1 h2 hc =
  ≤-trans (+-mono-≤ h1 h2)
    (≤-trans (≤-reflexive (e1 D))
      (≤-trans hc (≤-reflexive (sym (trans (cong (_+ S) (*-zeroʳ C)) refl)))))
  where
    e1 : ∀ d → suc d + 58 ≡ d + 59
    e1 = solve 1 (λ d → (con 1 :+ d) :+ con 58 := d :+ con 59) refl

lemIter : ∀ {j₁ j₂ j₃ j₄ j₅ j₆ j₇ D P S C k m n}
        → j₁ ≤ suc D → j₂ ≤ 85 → j₄ ≤ 87 → j₅ ≤ suc P
        → j₃ + S ≤ C * k → j₆ + S ≤ C * m → j₇ ≤ C * n + S
        → D + P + 175 ≤ S + S
        → (j₁ + (j₂ + (j₃ + (j₄ + (j₅ + (j₆ + j₇)))))) ≤ C * (k + m + n) + S
lemIter {j₁} {j₂} {j₃} {j₄} {j₅} {j₆} {j₇} {D} {P} {S} {C} {k} {m} {n}
        h1 h2 h4 h5 h3 h6 h7 hc =
  ≤-trans (+-mono-≤ h1 (+-mono-≤ h2 (+-monoʳ-≤ j₃
            (+-mono-≤ h4 (+-mono-≤ h5 (+-monoʳ-≤ j₆ h7))))))
    (≤-trans (≤-reflexive (e1 D P j₃ j₆ (C * n) S))
      (≤-trans (+-monoˡ-≤ ((j₃ + j₆) + (C * n + S))
                 (≤-trans (+-monoʳ-≤ (D + P) (n≤1+n 174)) hc))
        (≤-trans (≤-reflexive (e2 S j₃ j₆ (C * n + S)))
          (≤-trans (+-monoˡ-≤ (C * n + S) (+-mono-≤ h3 h6))
                   (≤-reflexive (e3 C k m n))))))
  where
    e1 : ∀ d p a b x s →
         (suc d + (85 + (a + (87 + (suc p + (b + (x + s))))))) ≡
         (d + p + 174) + ((a + b) + (x + s))
    e1 = solve 6 (λ d p a b x s →
           (con 1 :+ d) :+ (con 85 :+ (a :+ (con 87 :+ ((con 1 :+ p) :+ (b :+ (x :+ s)))))) :=
           (d :+ p :+ con 174) :+ ((a :+ b) :+ (x :+ s))) refl
    e2 : ∀ s a b y → (s + s) + ((a + b) + y) ≡ ((a + s) + (b + s)) + y
    e2 = solve 4 (λ s a b y → (s :+ s) :+ ((a :+ b) :+ y) := ((a :+ s) :+ (b :+ s)) :+ y) refl
    e3 : ∀ c k m n → (c * k + c * m) + (c * n + S) ≡ c * (k + m + n) + S
    e3 c k m n =
      trans (sym (+-assoc (c * k + c * m) (c * n) S))
            (cong (_+ S) (sym (trans (*-distribˡ-+ c (k + m) n)
                                     (cong (_+ c * n) (*-distribˡ-+ c k m)))))
