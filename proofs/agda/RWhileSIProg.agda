{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The self-interpreter as an R-WHILE PROGRAM, and the linear-time theorem.
--
-- `RWhileSIMach` proved that the agenda machine simulates any terminating
-- R-WHILE run with at most 3 machine steps per object step.  Here the machine
-- is packaged as an actual R-WHILE program -- the main loop of
-- `examples/ri.rwhile`,
--
--     SI  =  from (=? Cd' nil) do skip loop STEP until (=? Cd nil)
--
-- (variable 0 = the todo stack `Cd`, variable 1 = the done stack `Cd'`) -- and
-- the machine-level step count is turned into an R-WHILE step count.
--
-- The one thing this module does NOT do is BUILD `STEP`: the dispatch body is
-- taken as a parameter together with its correctness-and-cost obligation
-- (`Realises` below).  Everything else -- that the loop's reversibility
-- assertions really hold, that the iteration chain is a legal `Rest`
-- derivation, and the arithmetic of the overhead constant -- is proved.
--
-- THEOREM `si-linear` (given `R : Realises`):
--
--     c ⊢ σ ⇒ τ ∣ k   ⟹   SI ⊢ ⟨⌜c⌝, σ⟩ ⇒ ⟨⌜c⌝, τ⟩ ∣ j   with  j ≤ a · k
--
-- for the FIXED program `SI` and the constant `a = 4·(C+1) + 2` depending only
-- on the per-step cost bound `C` of the dispatch body -- i.e. `SI` is a
-- self-interpreter whose overhead is a constant factor: LINEAR TIME.
-- It is also PROGRAM-PRESERVING: the final state carries ⌜c⌝ on the done stack.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIProg where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoˡ-≤; *-monoʳ-≤
        ; *-assoc; *-comm; *-distribʳ-+; *-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

open import RWhileTime
open import RWhileSIEnc
open import RWhileSIMach

------------------------------------------------------------------------
-- What an implementation of the dispatch body has to provide.

record Realises : Set where
  field
    -- the body of the interpreter's main loop
    STEP : Cmd
    -- how a machine state sits in the interpreter's own store
    emb  : MSt → Store
    -- the per-step cost bound (for a real STEP: a constant plus the
    -- object-store walk, so `C` depends on the store size, not on the input)
    C    : ℕ
    -- the two stacks are the interpreter's variables 0 and 1
    todo-at-0 : ∀ m → get (emb m) 0 ≡ MSt.td m
    done-at-1 : ∀ m → get (emb m) 1 ≡ MSt.dn m
    -- STEP realises one machine step, within the cost bound
    step-ok   : ∀ {m m′} → astep m ≡ just m′
              → Σ[ j ∈ ℕ ] ((STEP ⊢ emb m ⇒ emb m′ ∣ j) × j ≤ C)

module Interpreter (R : Realises) where
  open Realises R

  ------------------------------------------------------------------------
  -- The self-interpreter program.

  emptyDone emptyTodo : Exp
  emptyDone = eqE (var 1) (cst nil)      -- =? Cd' nil   (loop entry test)
  emptyTodo = eqE (var 0) (cst nil)      -- =? Cd  nil   (loop exit test)

  SI : Cmd
  SI = loop emptyDone skip STEP emptyTodo

  ------------------------------------------------------------------------
  -- The loop's tests, read off the machine state.

  done-nil : ∀ m → MSt.dn m ≡ nil → evalT (emb m) emptyDone ≡ just true
  done-nil m eq rewrite done-at-1 m | eq = refl

  done-cons : ∀ m {a b} → MSt.dn m ≡ a ∙ b → evalT (emb m) emptyDone ≡ just false
  done-cons m eq rewrite done-at-1 m | eq = refl

  todo-nil : ∀ m → MSt.td m ≡ nil → evalT (emb m) emptyTodo ≡ just true
  todo-nil m eq rewrite todo-at-0 m | eq = refl

  todo-cons : ∀ m {a b} → MSt.td m ≡ a ∙ b → evalT (emb m) emptyTodo ≡ just false
  todo-cons m eq rewrite todo-at-0 m | eq = refl

  ------------------------------------------------------------------------
  -- Arithmetic of the overhead constant.

  eq-iter : ∀ c n → c + 1 + (suc c * n) ≡ suc c * suc n
  eq-iter = solve 2 (λ c n → c :+ con 1 :+ ((con 1 :+ c) :* n)
                          := (con 1 :+ c) :* (con 1 :+ n)) refl

  eq-loop : ∀ j → suc (1 + j) ≡ j + 2
  eq-loop = solve 1 (λ j → con 1 :+ (con 1 :+ j) := j :+ con 2) refl

  eq-assoc : ∀ c k → suc c * (4 * k) ≡ (4 * suc c) * k
  eq-assoc = solve 2 (λ c k → (con 1 :+ c) :* (con 4 :* k) := (con 4 :* (con 1 :+ c)) :* k) refl

  ------------------------------------------------------------------------
  -- A machine run IS an iteration chain of the R-WHILE loop.  Each iteration
  -- is legal because a step needs a non-empty todo stack (so the exit test is
  -- false) and always pushes on the done stack (so the entry test is false
  -- afterwards -- R-WHILE's reversibility assertion for loops).

  chain : ∀ {m m′ n} → Steps m m′ n → MSt.td m′ ≡ nil
        → Σ[ j ∈ ℕ ] (Rest emptyDone skip STEP emptyTodo (emb m) (emb m′) j
                      × j ≤ suc C * n)
  chain {m} [] fin = 0 , r-exit (todo-nil m fin) , z≤n
  chain {m} (_∷_ {m′ = m₁} {n = n} aok rest) fin
    with astep-td {MSt.td m} {MSt.dn m} {MSt.st m} aok
       | astep-dn {m} {m₁} aok
       | step-ok aok
       | chain rest fin
  ... | h , r , tdc | a , b , dnc | j , run , bj | j′ , rst , bj′ =
        j + 1 + j′
      , r-iter (todo-cons m tdc) run (done-cons m₁ dnc) e-skip rst
      , ≤-trans (+-mono-≤ (+-monoˡ-≤ 1 bj) bj′) (≤-reflexive (eq-iter C n))

  ------------------------------------------------------------------------
  -- The whole interpreter run: the loop's entry assertion holds (the done
  -- stack starts empty), the chain runs, and the exit test fires when the
  -- todo stack is exhausted.

  si-run : ∀ {m m′ n} → Steps m m′ n → MSt.dn m ≡ nil → MSt.td m′ ≡ nil
         → Σ[ j ∈ ℕ ] (SI ⊢ emb m ⇒ emb m′ ∣ j × j ≤ suc C * n + 2)
  si-run {m} {m′} {n} st dnil fin with chain st fin
  ... | j , rst , b = suc (1 + j) , e-loop (done-nil m dnil) e-skip rst
                    , ≤-trans (≤-reflexive (eq-loop j)) (+-monoˡ-≤ 2 b)

  ------------------------------------------------------------------------
  -- THE THEOREM.  `SI` is a self-interpreter of R-WHILE with LINEAR overhead:
  -- it computes the object program's store transformation, keeps the program
  -- (⌜c⌝ ends up on the done stack), and its running time is at most a
  -- CONSTANT FACTOR times the object program's running time.

  si-linear : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k
            → Σ[ j ∈ ℕ ]
                (SI ⊢ emb ⟨ ⌜ c ⌝ ∙ nil , nil , σ ⟩ ⇒ emb ⟨ nil , ⌜ c ⌝ ∙ nil , τ ⟩ ∣ j
                 × j ≤ (4 * suc C + 2) * k)
  si-linear {c} {σ} {τ} {k} d with machine-linear d
  ... | n , st , nb with si-run st refl refl
  ... | j , run , jb = j , run , final
    where
      2≤2k : 2 ≤ 2 * k
      2≤2k = ≤-trans (≤-reflexive (sym (*-identityʳ 2))) (*-monoʳ-≤ 2 (cost-pos d))

      final : j ≤ (4 * suc C + 2) * k
      final = ≤-trans jb
              (≤-trans (+-monoˡ-≤ 2 (*-monoʳ-≤ (suc C) nb))
              (≤-trans (≤-reflexive (cong (_+ 2) (eq-assoc C k)))
              (≤-trans (+-mono-≤ (≤-refl {4 * suc C * k}) 2≤2k)
                       (≤-reflexive (sym (*-distribʳ-+ k (4 * suc C) 2))))))
