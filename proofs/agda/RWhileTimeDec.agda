{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Deciding the static side conditions.
--
-- `Wf c` (no assignment mentions its own target) and `InR c σ` (every
-- variable is inside the store) are the hypotheses of every theorem about
-- the self-interpreter.  For a CONCRETE program -- in particular for the
-- interpreter `SI` itself -- they should not have to be proved by hand:
-- both are decidable, so the type checker can discharge them by evaluation.
--
-- This is the first step towards showing that `SI`, being an R-WHILE
-- program like any other, is itself reversible: with `Wf SI` and `InR SI`
-- in hand, `RWhileTimeInv.inv-sound` applies to the interpreter, so
-- `inv SI` undoes an interpretation in exactly the same number of steps.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileTimeDec where

open import Data.Nat using (ℕ; _≤?_; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime
open import RWhileSIWf

------------------------------------------------------------------------
-- `NotIn` is decidable.

notInO? : ∀ x a → Dec (NotInO x a)
notInO? x (var y) with x ≟ y
... | yes p  = no λ { (ni-var ne) → ne p }
... | no  ne = yes (ni-var ne)
notInO? x (cst v) = yes ni-cst

notIn? : ∀ x e → Dec (NotIn x e)
notIn? x (opd a) with notInO? x a
... | yes p = yes (ni-opd p)
... | no np = no λ { (ni-opd p) → np p }
notIn? x (cns a b) with notInO? x a | notInO? x b
... | yes p | yes q = yes (ni-cns p q)
... | no np | _     = no λ { (ni-cns p _) → np p }
... | _     | no nq = no λ { (ni-cns _ q) → nq q }
notIn? x (hdE a) with notInO? x a
... | yes p = yes (ni-hd p)
... | no np = no λ { (ni-hd p) → np p }
notIn? x (tlE a) with notInO? x a
... | yes p = yes (ni-tl p)
... | no np = no λ { (ni-tl p) → np p }
notIn? x (eqE a b) with notInO? x a | notInO? x b
... | yes p | yes q = yes (ni-eq p q)
... | no np | _     = no λ { (ni-eq p _) → np p }
... | _     | no nq = no λ { (ni-eq _ q) → nq q }
notIn? x (prE a) with notInO? x a
... | yes p = yes (ni-pr p)
... | no np = no λ { (ni-pr p) → np p }

------------------------------------------------------------------------
-- `Wf` is decidable, hence provable by evaluation for a concrete program.

wf? : ∀ c → Dec (Wf c)
wf? skip = yes wf-skip
wf? (x ^= e) with notIn? x e
... | yes p = yes (wf-ass p)
... | no np = no λ { (wf-ass p) → np p }
wf? (c ⨾ d) with wf? c | wf? d
... | yes p | yes q = yes (wf-seq p q)
... | no np | _     = no λ { (wf-seq p _) → np p }
... | _     | no nq = no λ { (wf-seq _ q) → nq q }
wf? (cond e c d f) with wf? c | wf? d
... | yes p | yes q = yes (wf-cond p q)
... | no np | _     = no λ { (wf-cond p _) → np p }
... | _     | no nq = no λ { (wf-cond _ q) → nq q }
wf? (loop e D L f) with wf? D | wf? L
... | yes p | yes q = yes (wf-loop p q)
... | no np | _     = no λ { (wf-loop p _) → np p }
... | _     | no nq = no λ { (wf-loop _ q) → nq q }

-- `InR` is already a decidable ≤, but give it a name for symmetry
inR? : ∀ c σ → Dec (InR c σ)
inR? c σ = vmax c ≤? length σ
  where open import RWhileSIEnc using (vmax)

------------------------------------------------------------------------
-- Discharging the conditions by evaluation.

Wf! : ∀ c {p : True (wf? c)} → Wf c
Wf! c {p} = toWitness p

InR! : ∀ c σ {p : True (inR? c σ)} → InR c σ
InR! c σ {p} = toWitness p

------------------------------------------------------------------------
-- Tests: the conditions really are decided by computation.

private
  prog : Cmd
  prog = (0 ^= opd (cst (atm 1))) ⨾ (1 ^= opd (var 0))

  test-wf : Wf prog
  test-wf = Wf! prog

  test-inR : InR prog (nil ∷ nil ∷ [])
  test-inR = InR! prog (nil ∷ nil ∷ [])

  -- an assignment that mentions its own target is rejected
  bad : Cmd
  bad = 0 ^= opd (var 0)

  test-bad : wf? bad ≡ no _
  test-bad = refl
