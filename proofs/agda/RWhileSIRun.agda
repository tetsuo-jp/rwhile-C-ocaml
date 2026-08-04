{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Bounded runs: a derivation together with an upper bound on its cost.
--
-- Assembling the interpreter's dispatch body means composing dozens of
-- fragments and adding up their costs.  Raw cost arithmetic does not compute
-- (`k * 30 + 9` is stuck when k is a variable), so instead of tracking exact
-- costs we track BOUNDS, which compose definitionally:
--
--     Run c s t B   =   ∃ k. (c ⊢ s ⇒ t ∣ k)  ×  k ≤ B
--
-- with one combinator per R-WHILE construct.  `Realises.step-ok` asks for
-- exactly this shape, so the top-level obligation is discharged by a `Run`.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIRun where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime

record Run (c : Cmd) (s t : Store) (B : ℕ) : Set where
  constructor mkRun
  field
    cost : ℕ
    run  : c ⊢ s ⇒ t ∣ cost
    bnd  : cost ≤ B

open Run public

-- an exact derivation is a run bounded by its own cost
rOf : ∀ {c s t k} → c ⊢ s ⇒ t ∣ k → Run c s t k
rOf d = mkRun _ d ≤-refl

-- weakening the bound
rWeak : ∀ {c s t M N} → M ≤ N → Run c s t M → Run c s t N
rWeak le r = mkRun (cost r) (run r) (≤-trans (bnd r) le)

rSkip : ∀ {s} → Run skip s s 1
rSkip = rOf e-skip

rAss : ∀ {x e s v u} → evalE s e ≡ just v → rupd (get s x) v ≡ just u
     → Run (x ^= e) s (set s x u) 1
rAss ev ru = rOf (e-ass ev ru)

rSeq : ∀ {c d s t u M N} → Run c s t M → Run d t u N → Run (c ⨾ d) s u (suc (M + N))
rSeq r₁ r₂ = mkRun _ (e-seq (run r₁) (run r₂)) (s≤s (+-mono-≤ (bnd r₁) (bnd r₂)))

-- chaining sequences without parentheses (both `_⨾_` and `_»_` are infixr)
infixr 4 _»_
_»_ : ∀ {c d s t u M N} → Run c s t M → Run d t u N → Run (c ⨾ d) s u (suc (M + N))
_»_ = rSeq

rThen : ∀ {e c d f s t M}
      → evalT s e ≡ just true → Run c s t M → evalT t f ≡ just true
      → Run (cond e c d f) s t (suc M)
rThen et r ef = mkRun _ (e-then et (run r) ef) (s≤s (bnd r))

rElse : ∀ {e c d f s t M}
      → evalT s e ≡ just false → Run d s t M → evalT t f ≡ just false
      → Run (cond e c d f) s t (suc M)
rElse et r ef = mkRun _ (e-else et (run r) ef) (s≤s (bnd r))

-- the loop is assembled from a `Rest` chain in RWhileSIProg; here we only need
-- the entry rule for loops whose iteration chain is already bounded.
rLoop : ∀ {e D L f s t u M N}
      → evalT s e ≡ just true → Run D s t M
      → (n : ℕ) → Rest e D L f t u n → n ≤ N
      → Run (loop e D L f) s u (suc (M + N))
rLoop et rD n rest bn = mkRun _ (e-loop et (run rD) rest) (s≤s (+-mono-≤ (bnd rD) bn))
