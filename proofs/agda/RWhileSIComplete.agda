{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE BACKWARD DIRECTION: what is proved, and what is not.
--
-- `si-linear` / `si-unique` say: if the object program terminates, then so
-- does `SI`, with the right answer and within the bound.  The converse --
-- "if SI terminates then the object program terminates" -- is a genuinely
-- different theorem, and this module says exactly how far it is proved.
--
-- PROVED HERE
--   * `rest-exit`, `si-halts→todo-empty`: if `SI` halts, its todo stack is
--     empty, i.e. every task really was processed (nothing is left behind).
--   * `si-answer`: if `SI` halts AND the object program terminates, the two
--     agree -- so `SI` can never halt with a WRONG answer.
--
-- NOT PROVED (`SiComplete` below states it precisely)
--   * "`SI` halts ⟹ the object program terminates".  The missing ingredient
--     is a DECODING INVARIANT: a map from an arbitrary reachable machine
--     state (todo stack of tasks and markers, done stack, object store) back
--     to an object-level continuation, together with the proof that one
--     `STEP` moves it exactly one object step.  `RWhileSIMach` builds traces
--     from derivations (the easy direction); the converse needs that map,
--     which is a development of its own.  Note this is not a soundness
--     hole: with `si-answer`, a halting `SI` cannot lie -- the open question
--     is only whether `SI` might halt where the object program does not.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIComplete where

open import Data.Nat using (ℕ; _+_; _*_; _≤_)
open import Data.List using (List; []; length)
open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime
open import RWhileSIEnc using (⌜_⌝)
open import RWhileSIWf
open import RWhileSIStep using (embM)
open import RWhileSISim using (SI; CC; emptyTodo; si-linear)
open import RWhileSIDet using (si-unique)

------------------------------------------------------------------------
-- 1.  A halting loop really did reach its exit condition.

rest-exit : ∀ {e D L f σ τ n} → Rest e D L f σ τ n → evalT τ f ≡ just true
rest-exit (r-exit tf)          = tf
rest-exit (r-iter _ _ _ _ rst) = rest-exit rst

-- so if the interpreter halts, its todo stack is empty: every task that was
-- pushed has been processed
si-halts→todo-empty : ∀ {s t j} → SI ⊢ s ⇒ t ∣ j → evalT t emptyTodo ≡ just true
si-halts→todo-empty (e-loop _ _ rst) = rest-exit rst

------------------------------------------------------------------------
-- 2.  A halting interpreter cannot give a wrong answer.

si-answer : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
          → ∀ {t j} → SI ⊢ embM (⌜ c ⌝ ∙ nil) nil σ ⇒ t ∣ j
          → t ≡ embM nil (⌜ c ⌝ ∙ nil) τ × j ≤ (CC (length σ) + 2) * k
si-answer wf ir d run = si-unique wf ir d run

------------------------------------------------------------------------
-- 3.  The open obligation, stated as a type (nothing is assumed: this is a
--     `Set`, not a postulate -- no one inhabits it in this development).

SiComplete : Set
SiComplete = ∀ {c σ t j} → Wf c → InR c σ
           → SI ⊢ embM (⌜ c ⌝ ∙ nil) nil σ ⇒ t ∣ j
           → Σ[ τ ∈ Store ] Σ[ k ∈ ℕ ]
               ((c ⊢ σ ⇒ τ ∣ k) × (t ≡ embM nil (⌜ c ⌝ ∙ nil) τ))

-- With it, termination of the two would be equivalent; without it we have
-- the implication that matters for using `SI` as an interpreter (below).
si-terminates : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
              → Σ[ t ∈ Store ] Σ[ j ∈ ℕ ] (SI ⊢ embM (⌜ c ⌝ ∙ nil) nil σ ⇒ t ∣ j)
si-terminates wf ir d = _ , proj₁ h , proj₁ (proj₂ h)
  where h = si-linear wf ir d
