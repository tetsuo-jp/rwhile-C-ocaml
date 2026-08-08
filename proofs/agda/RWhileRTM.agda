{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- R-WHILE IS r-TURING COMPLETE — the machine-checked version of
--
--   青木利晃・横山哲郎, 「可逆プログラミング言語 R-WHILE の可逆チューリング
--   完全性」, 電子情報通信学会論文誌 D, J101-D(9), pp.1372-1375, 2018.
--
-- That letter builds, for every reversible Turing machine T, an R-WHILE
-- program T̲ with ⟦T⟧^TM r = r′ ⟹ ⟦T̲⟧ r̄ = r̄′ (its Theorem 2), via a
-- rule-by-rule simulation (its Lemma 1).  This module carries the
-- construction out inside Agda, on top of the already verified R-WHILE
-- semantics of `RWhileTime`.
--
-- WHY `RWhileTime` AND NOT `RWhileRevFull`.  The abstract core
-- `RWhileRevFull.Core` takes atomic commands to be arbitrary RELATIONS on
-- stores.  Simulating a Turing machine there would be vacuous: one could
-- put the machine's whole step relation into a single atom.  `RWhileTime`
-- is a first-order deep embedding — `Cmd` is skip / `^=` / `⨾` / if-fi /
-- from-until and `Exp` is a flat expression grammar over variables and
-- constants, with no function space anywhere — so a program built here is
-- a genuine piece of R-WHILE text and the theorem has content.
--
-- WHAT REPLACES THE PAPER'S `rewrite` MACRO.  Fig. 2 of the letter writes
-- PUSH, POP and STEP with R-WHILE's pattern replacement `q <= r` and its
-- `rewrite … by …` multi-way case.  `RWhileTime` has neither: its commands
-- are the five reversible core constructs, and its expressions carry ONE
-- operator with variable-or-constant operands, so a guard like
-- `S = b̄ ∧ STK = nil` is not expressible as one test.  Both are recovered
-- without leaving the core:
--
--   * `q <= r` for a linear pattern is the local/delocal idiom — build the
--     value with `^=`, then clear the source with a `^=` that names it
--     (`rupd` case 2).  See `unpack3` / `pack3`, which are inverse.
--   * a conjunctive guard becomes ONE equality against a CONSTANT VALUE,
--     because `Opd` has `cst : V → Opd`.  `pushC` tests
--     `STK =? (b̄ . nil)`; `stepC` will test the dispatch key `(Q . S)`
--     against `(q̄ . s̄)`.
--
-- STATUS (milestone 1).  Definitions and the statements of Lemma 1 and of
-- r-Turing completeness are here and typecheck; `pushC` is proved to
-- realise the paper's PUSH in both of its cases.  The dispatch chain
-- `stepC` and the loop induction of Theorem 2 are milestone 2.  No
-- postulates, no holes — an unproved statement appears as a `Set`, never
-- as an assumed inhabitant.
------------------------------------------------------------------------

module RWhileRTM where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileTimeInv using (inv)
open import RWhileSIWf using (get-set-≡; get-set-≢)

------------------------------------------------------------------------
-- 1.  Reversible Turing machines (§2 of the letter).
--
-- States and tape symbols are ℕ.  A machine's rules are TRIPLES, as in the
-- letter: either a symbol rewrite (q,(s,s'),q') or a head move (q,a,q').

data Move : Set where
  mvL : Move          -- ←
  mvS : Move          -- ↓
  mvR : Move          -- →

data Rule : Set where
  rsym : ℕ → ℕ → ℕ → ℕ → Rule      -- (q , (s , s') , q')
  rmov : ℕ → Move → ℕ → Rule       -- (q , a , q')

src : Rule → ℕ
src (rsym q _ _ _) = q
src (rmov q _ _)   = q

tgt : Rule → ℕ
tgt (rsym _ _ _ q') = q'
tgt (rmov _ _ q')   = q'

record RTM : Set where
  field
    rules : List Rule
    blank : ℕ            -- b
    q-s   : ℕ            -- initial state
    q-f   : ℕ            -- final state

open RTM public

------------------------------------------------------------------------
-- Configurations.  A tape is (l , s , r): the symbol s under the head, the
-- half-tapes l (nearest symbol FIRST) and r.  Both are blank-free, which is
-- what `consNB` maintains.

Tape : Set
Tape = List ℕ × ℕ × List ℕ

Conf : Set
Conf = ℕ × Tape

-- push s onto the half-tape r, dropping it if it is a blank at the very end.
-- This is the third clause of the letter's `movel`, which is what keeps the
-- representation canonical.
consNB : ℕ → ℕ → List ℕ → List ℕ
consNB b s []      = if eqℕ s b then [] else s ∷ []
consNB b s (x ∷ r) = s ∷ x ∷ r

-- movel, all three clauses of the letter at once.
movel : ℕ → Tape → Tape
movel b ([]     , s , r) = []  , b  , consNB b s r
movel b (s' ∷ l , s , r) = l   , s' , consNB b s r

-- One computation step (Fig. 1 of the letter).  Note that the → case is
-- given by the CONVERSE of movel, exactly as in the letter — that is what
-- makes ← and → each other's inverse.
data Step (M : RTM) : Conf → Conf → Set where
  st-sym : ∀ {q s s' q' l r}
         → rsym q s s' q' ∈ rules M
         → Step M (q , (l , s , r)) (q' , (l , s' , r))
  st-lft : ∀ {q q' t}
         → rmov q mvL q' ∈ rules M
         → Step M (q , t) (q' , movel (blank M) t)
  st-sty : ∀ {q q' t}
         → rmov q mvS q' ∈ rules M
         → Step M (q , t) (q' , t)
  st-rgt : ∀ {q q' t t'}
         → rmov q mvR q' ∈ rules M
         → movel (blank M) t' ≡ t
         → Step M (q , t) (q' , t')

data Step* (M : RTM) : Conf → Conf → Set where
  done : ∀ {c} → Step* M c c
  more : ∀ {c c₁ c₂} → Step M c c₁ → Step* M c₁ c₂ → Step* M c c₂

------------------------------------------------------------------------
-- 2.  The reversibility conditions (§2.2 of the letter).
--
-- Local forward determinism: two DISTINCT rules leaving the same state must
-- both be symbol rules, and must read different symbols.  (So a state has
-- either one move rule or a set of symbol rules with distinct inputs — this
-- is precisely what lets `stepC` dispatch with mutually exclusive guards.)

LFD : RTM → Set
LFD M = ∀ d₁ d₂ → d₁ ∈ rules M → d₂ ∈ rules M → ¬ (d₁ ≡ d₂) → src d₁ ≡ src d₂
      → Σ[ q ∈ ℕ ] Σ[ s₁ ∈ ℕ ] Σ[ t₁ ∈ ℕ ] Σ[ p₁ ∈ ℕ ]
        Σ[ s₂ ∈ ℕ ] Σ[ t₂ ∈ ℕ ] Σ[ p₂ ∈ ℕ ]
        ( (d₁ ≡ rsym q s₁ t₁ p₁) × (d₂ ≡ rsym q s₂ t₂ p₂) × ¬ (s₁ ≡ s₂) )

-- Local backward determinism: the mirror image, on the WRITTEN symbol.
-- This is what makes the exit assertions of `stepC` mutually exclusive.
LBD : RTM → Set
LBD M = ∀ d₁ d₂ → d₁ ∈ rules M → d₂ ∈ rules M → ¬ (d₁ ≡ d₂) → tgt d₁ ≡ tgt d₂
      → Σ[ q ∈ ℕ ] Σ[ s₁ ∈ ℕ ] Σ[ t₁ ∈ ℕ ] Σ[ p₁ ∈ ℕ ]
        Σ[ s₂ ∈ ℕ ] Σ[ t₂ ∈ ℕ ] Σ[ p₂ ∈ ℕ ]
        ( (d₁ ≡ rsym p₁ s₁ t₁ q) × (d₂ ≡ rsym p₂ s₂ t₂ q) × ¬ (t₁ ≡ t₂) )

NoFromFinal : RTM → Set
NoFromFinal M = ∀ d → d ∈ rules M → ¬ (src d ≡ q-f M)

NoIntoStart : RTM → Set
NoIntoStart M = ∀ d → d ∈ rules M → ¬ (tgt d ≡ q-s M)

-- An RTM is a machine satisfying all four.
record IsRTM (M : RTM) : Set where
  field
    lfd : LFD M
    lbd : LBD M
    nff : NoFromFinal M
    nis : NoIntoStart M

------------------------------------------------------------------------
-- 3.  The encoding  x ↦ x̄  (§4 of the letter).
--
-- Symbols and states become atoms; half-tapes become cons lists; the tape
-- triple (l,s,r) becomes (l̄ . (s̄ . r̄)), which is the letter's `(L S R)`.

encL : List ℕ → V
encL []      = nil
encL (x ∷ l) = atm x ∙ encL l

encT : Tape → V
encT (l , s , r) = encL l ∙ (atm s ∙ encL r)

------------------------------------------------------------------------
-- 4.  Variables of the generated program.

vQ vT vL vS vR vTmp vW vIn vOut : ℕ
vQ   = 0        -- current state
vT   = 1        -- the tape triple
vL   = 2        -- scratch: left half-tape
vS   = 3        -- scratch: symbol under the head
vR   = 4        -- scratch: right half-tape
vTmp = 5        -- scratch: the suffix (s̄ . r̄), used while splitting T
vW   = 6        -- scratch: PUSH/POP's working cell
vIn  = 7        -- the program's input  R
vOut = 8        -- the program's output R'

------------------------------------------------------------------------
-- 5.  `q <= r` for the tape triple, as the local/delocal idiom.
--
--   unpack3 :  (L . (S . R)) <= T
--   pack3   :  T <= (L . (S . R))
--
-- Each `^=` either SETS a nil variable (rupd case 1) or CLEARS a variable
-- that already holds exactly the named value (rupd case 2); nothing else is
-- needed, and the two commands are each other's inverse.

-- `hd (tl T)` is not a single flat expression, so the split goes through the
-- intermediate Tmp = (s̄ . r̄) — which is also how a compiler would flatten it.
-- Each line is a `^=` that either SETS a nil variable or CLEARS a variable
-- holding exactly the value named on the right; T is cleared while Tmp still
-- holds its tail, and Tmp is cleared last.
unpackT : Cmd
unpackT =   vL   ^= hdE (var vT)               -- L   := hd T           = l̄
          ⨾ vTmp ^= tlE (var vT)               -- Tmp := tl T           = (s̄ . r̄)
          ⨾ vT   ^= cns (var vL) (var vTmp)    -- T holds (L . Tmp)     → clear T
          ⨾ vS   ^= hdE (var vTmp)             -- S   := hd Tmp         = s̄
          ⨾ vR   ^= tlE (var vTmp)             -- R   := tl Tmp         = r̄
          ⨾ vTmp ^= cns (var vS) (var vR)      -- Tmp holds (S . R)     → clear Tmp

packT : Cmd
packT = inv unpackT

------------------------------------------------------------------------
-- 5b.  unpackT AND packT ARE CORRECT.
--
-- These are the two halves of the letter's `(L S R) <= T` and `T <= (L S R)`.
-- Each is six assignments; each assignment either SETS a nil variable or
-- CLEARS one holding exactly the value named on the right, and in none of
-- them does the target occur in the expression.  The variables are concrete
-- numerals, so every distinctness side condition closes by `λ ()`.

unpack-sound : ∀ σ l x r
  → get σ vT ≡ encT (l , x , r)
  → get σ vL ≡ nil → get σ vS ≡ nil → get σ vR ≡ nil → get σ vTmp ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (unpackT ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vL ≡ encL l) × (get σ′ vS ≡ atm x) × (get σ′ vR ≡ encL r)
      × (get σ′ vT ≡ nil) × (get σ′ vTmp ≡ nil)
      × (∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
             → get σ′ y ≡ get σ y) )
unpack-sound σ l x r hT hL hS hR hTmp =
    υ6 , _
  , e-seq d1 (e-seq d2 (e-seq d3 (e-seq d4 (e-seq d5 d6))))
  , g6L , g6S , g6R , g6T , get-set-≡ υ5 vTmp nil , frame
  where
  A B : V
  A = encL l
  B = atm x ∙ encL r

  υ1 υ2 υ3 υ4 υ5 υ6 : Store
  υ1 = set σ  vL   A
  υ2 = set υ1 vTmp B
  υ3 = set υ2 vT   nil
  υ4 = set υ3 vS   (atm x)
  υ5 = set υ4 vR   (encL r)
  υ6 = set υ5 vTmp nil

  g1T : get υ1 vT ≡ A ∙ B
  g1T = trans (get-set-≢ σ vL vT A (λ ())) hT
  g1Tmp : get υ1 vTmp ≡ nil
  g1Tmp = trans (get-set-≢ σ vL vTmp A (λ ())) hTmp
  g1L : get υ1 vL ≡ A
  g1L = get-set-≡ σ vL A

  g2T : get υ2 vT ≡ A ∙ B
  g2T = trans (get-set-≢ υ1 vTmp vT B (λ ())) g1T
  g2L : get υ2 vL ≡ A
  g2L = trans (get-set-≢ υ1 vTmp vL B (λ ())) g1L
  g2Tmp : get υ2 vTmp ≡ B
  g2Tmp = get-set-≡ υ1 vTmp B

  g3Tmp : get υ3 vTmp ≡ B
  g3Tmp = trans (get-set-≢ υ2 vT vTmp nil (λ ())) g2Tmp
  g3S : get υ3 vS ≡ nil
  g3S = trans (get-set-≢ υ2 vT vS nil (λ ()))
        (trans (get-set-≢ υ1 vTmp vS B (λ ()))
               (trans (get-set-≢ σ vL vS A (λ ())) hS))
  g3L : get υ3 vL ≡ A
  g3L = trans (get-set-≢ υ2 vT vL nil (λ ())) g2L

  g4Tmp : get υ4 vTmp ≡ B
  g4Tmp = trans (get-set-≢ υ3 vS vTmp (atm x) (λ ())) g3Tmp
  g4R : get υ4 vR ≡ nil
  g4R = trans (get-set-≢ υ3 vS vR (atm x) (λ ()))
        (trans (get-set-≢ υ2 vT vR nil (λ ()))
        (trans (get-set-≢ υ1 vTmp vR B (λ ()))
               (trans (get-set-≢ σ vL vR A (λ ())) hR)))

  g5Tmp : get υ5 vTmp ≡ B
  g5Tmp = trans (get-set-≢ υ4 vR vTmp (encL r) (λ ())) g4Tmp
  g5S : get υ5 vS ≡ atm x
  g5S = trans (get-set-≢ υ4 vR vS (encL r) (λ ())) (get-set-≡ υ3 vS (atm x))
  g5R : get υ5 vR ≡ encL r
  g5R = get-set-≡ υ4 vR (encL r)

  g6L : get υ6 vL ≡ A
  g6L = trans (get-set-≢ υ5 vTmp vL nil (λ ()))
        (trans (get-set-≢ υ4 vR vL (encL r) (λ ()))
               (trans (get-set-≢ υ3 vS vL (atm x) (λ ())) g3L))
  g6S : get υ6 vS ≡ atm x
  g6S = trans (get-set-≢ υ5 vTmp vS nil (λ ())) g5S
  g6R : get υ6 vR ≡ encL r
  g6R = trans (get-set-≢ υ5 vTmp vR nil (λ ())) g5R
  g6T : get υ6 vT ≡ nil
  g6T = trans (get-set-≢ υ5 vTmp vT nil (λ ()))
        (trans (get-set-≢ υ4 vR vT (encL r) (λ ()))
        (trans (get-set-≢ υ3 vS vT (atm x) (λ ())) (get-set-≡ υ2 vT nil)))

  frame : ∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
        → get υ6 y ≡ get σ y
  frame y yT yL yS yR yTmp =
    trans (get-set-≢ υ5 vTmp y nil (λ e → yTmp (sym e)))
    (trans (get-set-≢ υ4 vR y (encL r) (λ e → yR (sym e)))
    (trans (get-set-≢ υ3 vS y (atm x) (λ e → yS (sym e)))
    (trans (get-set-≢ υ2 vT y nil (λ e → yT (sym e)))
    (trans (get-set-≢ υ1 vTmp y B (λ e → yTmp (sym e)))
           (get-set-≢ σ vL y A (λ e → yL (sym e)))))))

  d1 : (vL ^= hdE (var vT)) ⊢ σ ⇒ υ1 ∣ 1
  d1 = e-ass (subst (λ z → hdM z ≡ just A) (sym hT) refl)
             (subst (λ z → rupd z A ≡ just A) (sym hL) refl)
  d2 : (vTmp ^= tlE (var vT)) ⊢ υ1 ⇒ υ2 ∣ 1
  d2 = e-ass (subst (λ z → tlM z ≡ just B) (sym g1T) refl)
             (subst (λ z → rupd z B ≡ just B) (sym g1Tmp) refl)
  d3 : (vT ^= cns (var vL) (var vTmp)) ⊢ υ2 ⇒ υ3 ∣ 1
  d3 = e-ass (cong just (cong₂ _∙_ g2L g2Tmp))
             (subst (λ z → rupd z (A ∙ B) ≡ just nil) (sym g2T) (rupd-self (A ∙ B)))
  d4 : (vS ^= hdE (var vTmp)) ⊢ υ3 ⇒ υ4 ∣ 1
  d4 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g3Tmp) refl)
             (subst (λ z → rupd z (atm x) ≡ just (atm x)) (sym g3S) refl)
  d5 : (vR ^= tlE (var vTmp)) ⊢ υ4 ⇒ υ5 ∣ 1
  d5 = e-ass (subst (λ z → tlM z ≡ just (encL r)) (sym g4Tmp) refl)
             (subst (λ z → rupd z (encL r) ≡ just (encL r)) (sym g4R) refl)
  d6 : (vTmp ^= cns (var vS) (var vR)) ⊢ υ5 ⇒ υ6 ∣ 1
  d6 = e-ass (cong just (cong₂ _∙_ g5S g5R))
             (subst (λ z → rupd z B ≡ just nil) (sym g5Tmp) (rupd-self B))

-- packT is `inv unpackT`, so it is the same six assignments in the opposite
-- order (left-nested, as `inv (c ⨾ d) = inv d ⨾ inv c` builds it).
pack-sound : ∀ σ l x r
  → get σ vL ≡ encL l → get σ vS ≡ atm x → get σ vR ≡ encL r
  → get σ vT ≡ nil → get σ vTmp ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (packT ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vT ≡ encT (l , x , r))
      × (get σ′ vL ≡ nil) × (get σ′ vS ≡ nil) × (get σ′ vR ≡ nil)
      × (get σ′ vTmp ≡ nil)
      × (∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
             → get σ′ y ≡ get σ y) )
pack-sound σ l x r hL hS hR hT hTmp =
    ω6 , _
  , e-seq (e-seq (e-seq (e-seq (e-seq b1 b2) b3) b4) b5) b6
  , g6T , get-set-≡ ω5 vL nil , g6S , g6R , g6Tmp , frame
  where
  A B : V
  A = encL l
  B = atm x ∙ encL r

  ω1 ω2 ω3 ω4 ω5 ω6 : Store
  ω1 = set σ  vTmp B
  ω2 = set ω1 vR   nil
  ω3 = set ω2 vS   nil
  ω4 = set ω3 vT   (A ∙ B)
  ω5 = set ω4 vTmp nil
  ω6 = set ω5 vL   nil

  g1Tmp : get ω1 vTmp ≡ B
  g1Tmp = get-set-≡ σ vTmp B
  g1R : get ω1 vR ≡ encL r
  g1R = trans (get-set-≢ σ vTmp vR B (λ ())) hR
  g2Tmp : get ω2 vTmp ≡ B
  g2Tmp = trans (get-set-≢ ω1 vR vTmp nil (λ ())) g1Tmp
  g2S : get ω2 vS ≡ atm x
  g2S = trans (get-set-≢ ω1 vR vS nil (λ ())) (trans (get-set-≢ σ vTmp vS B (λ ())) hS)
  g3Tmp : get ω3 vTmp ≡ B
  g3Tmp = trans (get-set-≢ ω2 vS vTmp nil (λ ())) g2Tmp
  g3L : get ω3 vL ≡ A
  g3L = trans (get-set-≢ ω2 vS vL nil (λ ()))
        (trans (get-set-≢ ω1 vR vL nil (λ ()))
               (trans (get-set-≢ σ vTmp vL B (λ ())) hL))
  g3T : get ω3 vT ≡ nil
  g3T = trans (get-set-≢ ω2 vS vT nil (λ ()))
        (trans (get-set-≢ ω1 vR vT nil (λ ()))
               (trans (get-set-≢ σ vTmp vT B (λ ())) hT))
  g4T : get ω4 vT ≡ A ∙ B
  g4T = get-set-≡ ω3 vT (A ∙ B)
  g4Tmp : get ω4 vTmp ≡ B
  g4Tmp = trans (get-set-≢ ω3 vT vTmp (A ∙ B) (λ ())) g3Tmp
  g5T : get ω5 vT ≡ A ∙ B
  g5T = trans (get-set-≢ ω4 vTmp vT nil (λ ())) g4T
  g5L : get ω5 vL ≡ A
  g5L = trans (get-set-≢ ω4 vTmp vL nil (λ ()))
        (trans (get-set-≢ ω3 vT vL (A ∙ B) (λ ())) g3L)

  g6T : get ω6 vT ≡ A ∙ B
  g6T = trans (get-set-≢ ω5 vL vT nil (λ ())) g5T
  g6S : get ω6 vS ≡ nil
  g6S = trans (get-set-≢ ω5 vL vS nil (λ ()))
        (trans (get-set-≢ ω4 vTmp vS nil (λ ()))
               (trans (get-set-≢ ω3 vT vS (A ∙ B) (λ ())) (get-set-≡ ω2 vS nil)))
  g6R : get ω6 vR ≡ nil
  g6R = trans (get-set-≢ ω5 vL vR nil (λ ()))
        (trans (get-set-≢ ω4 vTmp vR nil (λ ()))
        (trans (get-set-≢ ω3 vT vR (A ∙ B) (λ ()))
               (trans (get-set-≢ ω2 vS vR nil (λ ())) (get-set-≡ ω1 vR nil))))
  g6Tmp : get ω6 vTmp ≡ nil
  g6Tmp = trans (get-set-≢ ω5 vL vTmp nil (λ ())) (get-set-≡ ω4 vTmp nil)

  frame : ∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
        → get ω6 y ≡ get σ y
  frame y yT yL yS yR yTmp =
    trans (get-set-≢ ω5 vL y nil (λ e → yL (sym e)))
    (trans (get-set-≢ ω4 vTmp y nil (λ e → yTmp (sym e)))
    (trans (get-set-≢ ω3 vT y (A ∙ B) (λ e → yT (sym e)))
    (trans (get-set-≢ ω2 vS y nil (λ e → yS (sym e)))
    (trans (get-set-≢ ω1 vR y nil (λ e → yR (sym e)))
           (get-set-≢ σ vTmp y B (λ e → yTmp (sym e)))))))

  b1 : (vTmp ^= cns (var vS) (var vR)) ⊢ σ ⇒ ω1 ∣ 1
  b1 = e-ass (cong just (cong₂ _∙_ hS hR))
             (subst (λ z → rupd z B ≡ just B) (sym hTmp) refl)
  b2 : (vR ^= tlE (var vTmp)) ⊢ ω1 ⇒ ω2 ∣ 1
  b2 = e-ass (subst (λ z → tlM z ≡ just (encL r)) (sym g1Tmp) refl)
             (subst (λ z → rupd z (encL r) ≡ just nil) (sym g1R) (rupd-self (encL r)))
  b3 : (vS ^= hdE (var vTmp)) ⊢ ω2 ⇒ ω3 ∣ 1
  b3 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g2Tmp) refl)
             (subst (λ z → rupd z (atm x) ≡ just nil) (sym g2S) (rupd-self (atm x)))
  b4 : (vT ^= cns (var vL) (var vTmp)) ⊢ ω3 ⇒ ω4 ∣ 1
  b4 = e-ass (cong just (cong₂ _∙_ g3L g3Tmp))
             (subst (λ z → rupd z (A ∙ B) ≡ just (A ∙ B)) (sym g3T) refl)
  b5 : (vTmp ^= tlE (var vT)) ⊢ ω4 ⇒ ω5 ∣ 1
  b5 = e-ass (subst (λ z → tlM z ≡ just B) (sym g4T) refl)
             (subst (λ z → rupd z B ≡ just nil) (sym g4Tmp) (rupd-self B))
  b6 : (vL ^= hdE (var vT)) ⊢ ω5 ⇒ ω6 ∣ 1
  b6 = e-ass (subst (λ z → hdM z ≡ just A) (sym g5T) refl)
             (subst (λ z → rupd z A ≡ just nil) (sym g5L) (rupd-self A))

------------------------------------------------------------------------
-- 6.  PUSH and POP (Fig. 2c, 2d).
--
-- The letter writes
--     PUSH(S,STK) ≡ rewrite [S,STK] by [b̄,nil] => [nil,nil]
--                                    | [S,STK] => [nil,(S.STK)]
-- i.e. "push S onto STK, except that a blank pushed onto the empty stack
-- disappears".  Pushing UNCONDITIONALLY and then normalising is the same
-- function, and its guard is a single equality against a constant:
--
--     STK ^= cons S STK ;  S ^= hd STK ;
--     if STK =? (b̄ . nil) then STK ^= (b̄ . nil) else skip fi STK =? nil
--
-- The exit assertion separates the branches: after the then-branch STK is
-- nil, after the else-branch it is a cons.
--
-- CAUTION (a real trap, found while checking this).  The obvious first
-- attempt
--        STK ^= cons S STK ;  S ^= hd STK ;  …
-- is NOT R-WHILE: the assigned variable occurs in the expression, which the
-- language forbids, and the semantics agrees — `rupd` sends a non-nil STK
-- and the value (S . STK) to `nothing`, so the command is simply stuck.
-- That linearity side condition is exactly why the letter builds PUSH from
-- the pattern replacement `<=` and not from `^=`.  Going through a scratch
-- variable W restores it: every assignment below either sets a nil variable
-- or clears one holding precisely the value named on the right, and in none
-- of them does the target occur in the expression.

pushC : ℕ → ℕ → ℕ → ℕ → Cmd
pushC b s stk w =
    w   ^= cns (var s) (var stk)          -- W   := (S . STK)   [W was nil]
  ⨾ s   ^= hdE (var w)                    -- S   = hd W         → clear S
  ⨾ stk ^= tlE (var w)                    -- STK = tl W         → clear STK
  ⨾ stk ^= opd (var w)                    -- STK := W           [STK now nil]
  ⨾ w   ^= opd (var stk)                  -- W   = STK          → clear W
  ⨾ cond (eqE (var stk) (cst (atm b ∙ nil)))
         (stk ^= opd (cst (atm b ∙ nil))) -- drop the blank: STK := nil
         skip
         (eqE (var stk) (cst nil))

popC : ℕ → ℕ → ℕ → ℕ → Cmd
popC b s stk w = inv (pushC b s stk w)


------------------------------------------------------------------------
-- 6b.  PUSH IS CORRECT.
--
-- `pushC` realises the letter's PUSH: from S = s̄ and STK = r̄ it reaches
-- S = nil and STK = encL (consNB b s r) — that is, it pushes s onto r
-- unless s is the blank and r is empty, in which case the blank vanishes.
-- Both of the letter's `rewrite` clauses are therefore accounted for, and
-- the scratch cell W comes back nil, so PUSH can be used again.

module Push (b s stk w : ℕ)
            (w≢s : ¬ (w ≡ s)) (w≢stk : ¬ (w ≡ stk)) (s≢stk : ¬ (s ≡ stk)) where

  private
    s≢w : ¬ (s ≡ w)
    s≢w e = w≢s (sym e)
    stk≢w : ¬ (stk ≡ w)
    stk≢w e = w≢stk (sym e)
    stk≢s : ¬ (stk ≡ s)
    stk≢s e = s≢stk (sym e)

  -- The straight-line part: the five assignments, their intermediate stores
  -- and the facts about them.  Shared by every case of the normalisation.
  module Run (σ : Store) (x : ℕ) (r : List ℕ)
             (hs : get σ s ≡ atm x) (hstk : get σ stk ≡ encL r)
             (hw : get σ w ≡ nil) where

    v : V
    v = atm x ∙ encL r

    τ1 τ2 τ3 τ4 τ5 : Store
    τ1 = set σ  w   v
    τ2 = set τ1 s   nil
    τ3 = set τ2 stk nil
    τ4 = set τ3 stk v
    τ5 = set τ4 w   nil

    g1s : get τ1 s ≡ atm x
    g1s = trans (get-set-≢ σ w s v w≢s) hs
    g1w : get τ1 w ≡ v
    g1w = get-set-≡ σ w v
    g1stk : get τ1 stk ≡ encL r
    g1stk = trans (get-set-≢ σ w stk v w≢stk) hstk

    g2w : get τ2 w ≡ v
    g2w = trans (get-set-≢ τ1 s w nil s≢w) g1w
    g2stk : get τ2 stk ≡ encL r
    g2stk = trans (get-set-≢ τ1 s stk nil s≢stk) g1stk
    g2s : get τ2 s ≡ nil
    g2s = get-set-≡ τ1 s nil

    g3w : get τ3 w ≡ v
    g3w = trans (get-set-≢ τ2 stk w nil stk≢w) g2w
    g3stk : get τ3 stk ≡ nil
    g3stk = get-set-≡ τ2 stk nil
    g3s : get τ3 s ≡ nil
    g3s = trans (get-set-≢ τ2 stk s nil stk≢s) g2s

    g4stk : get τ4 stk ≡ v
    g4stk = get-set-≡ τ3 stk v
    g4w : get τ4 w ≡ v
    g4w = trans (get-set-≢ τ3 stk w v stk≢w) g3w
    g4s : get τ4 s ≡ nil
    g4s = trans (get-set-≢ τ3 stk s v stk≢s) g3s

    g5stk : get τ5 stk ≡ v
    g5stk = trans (get-set-≢ τ4 w stk nil w≢stk) g4stk
    g5s : get τ5 s ≡ nil
    g5s = trans (get-set-≢ τ4 w s nil w≢s) g4s
    g5w : get τ5 w ≡ nil
    g5w = get-set-≡ τ4 w nil

    -- nothing but s, stk and w moves
    frame5 : ∀ y → ¬ (y ≡ s) → ¬ (y ≡ stk) → ¬ (y ≡ w) → get τ5 y ≡ get σ y
    frame5 y ys ystk yw =
      trans (get-set-≢ τ4 w y nil (λ e → yw (sym e)))
      (trans (get-set-≢ τ3 stk y v (λ e → ystk (sym e)))
      (trans (get-set-≢ τ2 stk y nil (λ e → ystk (sym e)))
      (trans (get-set-≢ τ1 s y nil (λ e → ys (sym e)))
             (get-set-≢ σ w y v (λ e → yw (sym e))))))

    -- `STK =? c` reads whatever STK holds
    testEq : ∀ (τ : Store) (u c : V) → get τ stk ≡ u
           → evalT τ (eqE (var stk) (cst c)) ≡ just (eqV u c)
    testEq τ u c h rewrite h = cong just (isTrue-boolV (eqV u c))

    d1 : (w ^= cns (var s) (var stk)) ⊢ σ ⇒ τ1 ∣ 1
    d1 = e-ass (cong just (cong₂ _∙_ hs hstk))
               (subst (λ z → rupd z v ≡ just v) (sym hw) refl)

    d2 : (s ^= hdE (var w)) ⊢ τ1 ⇒ τ2 ∣ 1
    d2 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g1w) refl)
               (subst (λ z → rupd z (atm x) ≡ just nil) (sym g1s) (rupd-self (atm x)))

    d3 : (stk ^= tlE (var w)) ⊢ τ2 ⇒ τ3 ∣ 1
    d3 = e-ass (subst (λ z → tlM z ≡ just (encL r)) (sym g2w) refl)
               (subst (λ z → rupd z (encL r) ≡ just nil) (sym g2stk) (rupd-self (encL r)))

    d4 : (stk ^= opd (var w)) ⊢ τ3 ⇒ τ4 ∣ 1
    d4 = e-ass (cong just g3w)
               (subst (λ z → rupd z v ≡ just v) (sym g3stk) refl)

    d5 : (w ^= opd (var stk)) ⊢ τ4 ⇒ τ5 ∣ 1
    d5 = e-ass (cong just g4stk)
               (subst (λ z → rupd z v ≡ just nil) (sym g4w) (rupd-self v))

    pre : ∀ {τ k} → cond (eqE (var stk) (cst (atm b ∙ nil)))
                         (stk ^= opd (cst (atm b ∙ nil))) skip
                         (eqE (var stk) (cst nil)) ⊢ τ5 ⇒ τ ∣ k
        → pushC b s stk w ⊢ σ ⇒ τ ∣ suc (1 + suc (1 + suc (1 + suc (1 + suc (1 + k)))))
    pre dc = e-seq d1 (e-seq d2 (e-seq d3 (e-seq d4 (e-seq d5 dc))))

  -- The statement: PUSH turns (S,STK) = (s̄, r̄) into (nil, consNB b s r).
  PushSpec : Store → ℕ → List ℕ → Set
  PushSpec σ x r =
    Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (pushC b s stk w ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ s ≡ nil)
      × (get σ′ stk ≡ encL (consNB b x r))
      × (get σ′ w ≡ nil)
      × (∀ y → ¬ (y ≡ s) → ¬ (y ≡ stk) → ¬ (y ≡ w) → get σ′ y ≡ get σ y) )

  push-sound : ∀ σ x r
    → get σ s ≡ atm x → get σ stk ≡ encL r → get σ w ≡ nil → PushSpec σ x r

  -- (a) empty half-tape: the blank disappears, any other symbol is pushed.
  push-sound σ x [] hs hstk hw = go (eqℕ x b) refl
    where
    open Run σ x [] hs hstk hw

    go : ∀ t → eqℕ x b ≡ t → PushSpec σ x []
    go true e =
        set τ5 stk nil , _
      , pre (e-then entry (e-ass refl clear) exit)
      , trans (get-set-≢ τ5 stk s nil stk≢s) g5s
      , trans (get-set-≡ τ5 stk nil) (sym encNil)
      , trans (get-set-≢ τ5 stk w nil stk≢w) g5w
      , (λ y ys ystk yw → trans (get-set-≢ τ5 stk y nil (λ q → ystk (sym q)))
                                (frame5 y ys ystk yw))
      where
      eqTrue : eqV v (atm b ∙ nil) ≡ true
      eqTrue rewrite e = refl
      encNil : encL (consNB b x []) ≡ nil
      encNil rewrite e = refl
      entry : evalT τ5 (eqE (var stk) (cst (atm b ∙ nil))) ≡ just true
      entry = trans (testEq τ5 v (atm b ∙ nil) g5stk) (cong just eqTrue)
      clearV : rupd v (atm b ∙ nil) ≡ just nil
      clearV rewrite eqTrue = refl
      clear : rupd (get τ5 stk) (atm b ∙ nil) ≡ just nil
      clear = subst (λ z → rupd z (atm b ∙ nil) ≡ just nil) (sym g5stk) clearV
      exit : evalT (set τ5 stk nil) (eqE (var stk) (cst nil)) ≡ just true
      exit = testEq (set τ5 stk nil) nil nil (get-set-≡ τ5 stk nil)

    go false e =
        τ5 , _ , pre (e-else entry e-skip exit)
      , g5s , trans g5stk (sym encCons) , g5w , frame5
      where
      eqFalse : eqV v (atm b ∙ nil) ≡ false
      eqFalse rewrite e = refl
      encCons : encL (consNB b x []) ≡ v
      encCons rewrite e = refl
      entry : evalT τ5 (eqE (var stk) (cst (atm b ∙ nil))) ≡ just false
      entry = trans (testEq τ5 v (atm b ∙ nil) g5stk) (cong just eqFalse)
      exit : evalT τ5 (eqE (var stk) (cst nil)) ≡ just false
      exit = testEq τ5 v nil g5stk

  -- (b) non-empty half-tape: always an ordinary push, whatever the symbol.
  push-sound σ x (y ∷ r′) hs hstk hw =
      τ5 , _ , pre (e-else entry e-skip exit)
    , g5s , g5stk , g5w , frame5
    where
    open Run σ x (y ∷ r′) hs hstk hw
    -- STK now holds (x̄ . (ȳ . r̄′)), whose tail is a cons, so it cannot be
    -- (b̄ . nil) no matter what x is: both branches of the test collapse.
    ifF : ∀ (u : Bool) → (if u then false else false) ≡ false
    ifF true  = refl
    ifF false = refl
    eqFalse : eqV v (atm b ∙ nil) ≡ false
    eqFalse = ifF (eqℕ x b)
    entry : evalT τ5 (eqE (var stk) (cst (atm b ∙ nil))) ≡ just false
    entry = trans (testEq τ5 v (atm b ∙ nil) g5stk) (cong just eqFalse)
    exit : evalT τ5 (eqE (var stk) (cst nil)) ≡ just false
    exit = testEq τ5 v nil g5stk

------------------------------------------------------------------------
-- 7.  MOVEL and MOVER (Fig. 2c).
--
--     MOVEL((L S R)) ≡ PUSH(S,R) ; POP(S,L)
--     MOVER         ≡ I⟦MOVEL⟧

movelC : ℕ → Cmd
movelC b = unpackT ⨾ pushC b vS vR vW ⨾ popC b vS vL vW ⨾ packT

moverC : ℕ → Cmd
moverC b = inv (movelC b)

------------------------------------------------------------------------
-- 8.  The translation of one rule (Fig. 3).
--
--   (q₁,(s₁,s₂),q₂)  ↦  [q̄₁,(L s̄₁ R)] => [q̄₂,(L s̄₂ R)]
--   (q₁,←,q₂)        ↦  [q̄₁,T] => { MOVEL(T) ; Q ^= q̄₁ ; Q ^= q̄₂ }
--   (q₁,↓,q₂)        ↦  [q̄₁,T] => [q̄₂,T]
--   (q₁,→,q₂)        ↦  [q̄₁,T] => { MOVER(T) ; Q ^= q̄₁ ; Q ^= q̄₂ }
--
-- Here only the BODY of each branch is built; the dispatch that selects it
-- is `stepC` (milestone 2).  A state change is always the pair of
-- assignments `Q ^= q̄₁ ; Q ^= q̄₂`: the first clears (rupd case 2), the
-- second sets (rupd case 1).

setState : ℕ → ℕ → Cmd
setState q₁ q₂ = vQ ^= opd (cst (atm q₁)) ⨾ vQ ^= opd (cst (atm q₂))

ruleC : ℕ → Rule → Cmd
ruleC b (rsym q₁ s₁ s₂ q₂) =
    unpackT
  ⨾ vS ^= opd (cst (atm s₁))
  ⨾ vS ^= opd (cst (atm s₂))
  ⨾ packT
  ⨾ setState q₁ q₂
ruleC b (rmov q₁ mvL q₂) = movelC b ⨾ setState q₁ q₂
ruleC b (rmov q₁ mvS q₂) = setState q₁ q₂
ruleC b (rmov q₁ mvR q₂) = moverC b ⨾ setState q₁ q₂

------------------------------------------------------------------------
-- 9.  What it means for a store to hold a configuration.

HoldsConf : Conf → Store → Set
HoldsConf (q , t) σ = (get σ vQ ≡ atm q) × (get σ vT ≡ encT t)

Scratch-nil : Store → Set
Scratch-nil σ = (get σ vL ≡ nil) × (get σ vS ≡ nil) × (get σ vR ≡ nil)
              × (get σ vTmp ≡ nil) × (get σ vW ≡ nil)

------------------------------------------------------------------------
-- 9b.  LEMMA 1, for the rules that do not move the head.
--
-- The two easy shapes of Fig. 3 are discharged here: the symbol rewrite
--     (q₁,(s₁,s₂),q₂)  ↦  [q̄₁,(L s̄₁ R)] => [q̄₂,(L s̄₂ R)]
-- and the stay rule
--     (q₁,↓,q₂)        ↦  [q̄₁,T] => [q̄₂,T].
-- The two head-moving shapes need POP, and follow in the next step.

setState-sound : ∀ q₁ q₂ σ → get σ vQ ≡ atm q₁
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (setState q₁ q₂ ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂)
      × (∀ y → ¬ (y ≡ vQ) → get σ′ y ≡ get σ y) )
setState-sound q₁ q₂ σ hQ =
    set (set σ vQ nil) vQ (atm q₂) , _
  , e-seq s1 s2
  , get-set-≡ (set σ vQ nil) vQ (atm q₂)
  , (λ y yq → trans (get-set-≢ (set σ vQ nil) vQ y (atm q₂) (λ e → yq (sym e)))
                    (get-set-≢ σ vQ y nil (λ e → yq (sym e))))
  where
  s1 : (vQ ^= opd (cst (atm q₁))) ⊢ σ ⇒ set σ vQ nil ∣ 1
  s1 = e-ass refl (subst (λ z → rupd z (atm q₁) ≡ just nil) (sym hQ)
                         (rupd-self (atm q₁)))
  s2 : (vQ ^= opd (cst (atm q₂))) ⊢ set σ vQ nil
                                 ⇒ set (set σ vQ nil) vQ (atm q₂) ∣ 1
  s2 = e-ass refl (subst (λ z → rupd z (atm q₂) ≡ just (atm q₂))
                         (sym (get-set-≡ σ vQ nil)) refl)

-- (q₁,↓,q₂): only the state changes.
rule-stay-sound : ∀ b q₁ q₂ σ t
  → get σ vQ ≡ atm q₁ → get σ vT ≡ encT t → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b (rmov q₁ mvS q₂) ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂) × (get σ′ vT ≡ encT t) × Scratch-nil σ′ )
rule-stay-sound b q₁ q₂ σ t hQ hT (hL , hS , hR , hTmp , hW)
  with setState-sound q₁ q₂ σ hQ
... | σ′ , k , d , gQ , fr =
    σ′ , k , d , gQ
  , trans (fr vT (λ ())) hT
  , trans (fr vL (λ ())) hL , trans (fr vS (λ ())) hS
  , trans (fr vR (λ ())) hR , trans (fr vTmp (λ ())) hTmp
  , trans (fr vW (λ ())) hW

-- (q₁,(s₁,s₂),q₂): unpack the tape, exchange the symbol under the head by a
-- pair of reversible assignments (the first CLEARS, the second SETS), pack it
-- back, and change the state.
rule-sym-sound : ∀ b q₁ s₁ s₂ q₂ σ l r
  → get σ vQ ≡ atm q₁ → get σ vT ≡ encT (l , s₁ , r) → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b (rsym q₁ s₁ s₂ q₂) ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂) × (get σ′ vT ≡ encT (l , s₂ , r)) × Scratch-nil σ′ )
rule-sym-sound b q₁ s₁ s₂ q₂ σ l r hQ hT (hL , hS , hR , hTmp , hW)
  with unpack-sound σ l s₁ r hT hL hS hR hTmp
... | σ₁ , _ , dU , g1L , g1S , g1R , g1T , g1Tmp , f1
  with pack-sound (set (set σ₁ vS nil) vS (atm s₂)) l s₂ r
         (trans (get-set-≢ (set σ₁ vS nil) vS vL (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vL nil (λ ())) g1L))
         (get-set-≡ (set σ₁ vS nil) vS (atm s₂))
         (trans (get-set-≢ (set σ₁ vS nil) vS vR (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vR nil (λ ())) g1R))
         (trans (get-set-≢ (set σ₁ vS nil) vS vT (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vT nil (λ ())) g1T))
         (trans (get-set-≢ (set σ₁ vS nil) vS vTmp (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vTmp nil (λ ())) g1Tmp))
... | σ₄ , _ , dP , g4T , g4L , g4S , g4R , g4Tmp , f4
  with setState-sound q₁ q₂ σ₄ q1-at-σ₄
  where
  σ₂ σ₃ : Store
  σ₂ = set σ₁ vS nil
  σ₃ = set σ₂ vS (atm s₂)
  q1-at-σ₄ : get σ₄ vQ ≡ atm q₁
  q1-at-σ₄ = trans (f4 vQ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
             (trans (get-set-≢ σ₂ vS vQ (atm s₂) (λ ()))
             (trans (get-set-≢ σ₁ vS vQ nil (λ ()))
                    (trans (f1 vQ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hQ)))
... | σ₅ , _ , dS , g5Q , f5 =
    σ₅ , _
  , e-seq dU (e-seq e1 (e-seq e2 (e-seq dP dS)))
  , g5Q
  , trans (f5 vT (λ ())) g4T
  , trans (f5 vL (λ ())) g4L , trans (f5 vS (λ ())) g4S
  , trans (f5 vR (λ ())) g4R , trans (f5 vTmp (λ ())) g4Tmp
  , trans (f5 vW (λ ())) vW-at-σ₄
  where
  σ₂ σ₃ : Store
  σ₂ = set σ₁ vS nil
  σ₃ = set σ₂ vS (atm s₂)
  e1 : (vS ^= opd (cst (atm s₁))) ⊢ σ₁ ⇒ σ₂ ∣ 1
  e1 = e-ass refl (subst (λ z → rupd z (atm s₁) ≡ just nil) (sym g1S)
                         (rupd-self (atm s₁)))
  e2 : (vS ^= opd (cst (atm s₂))) ⊢ σ₂ ⇒ σ₃ ∣ 1
  e2 = e-ass refl (subst (λ z → rupd z (atm s₂) ≡ just (atm s₂))
                         (sym (get-set-≡ σ₁ vS nil)) refl)
  vW-at-σ₄ : get σ₄ vW ≡ nil
  vW-at-σ₄ = trans (f4 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
             (trans (get-set-≢ σ₂ vS vW (atm s₂) (λ ()))
             (trans (get-set-≢ σ₁ vS vW nil (λ ()))
                    (trans (f1 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hW)))

------------------------------------------------------------------------
-- 10.  LEMMA 1 of the letter, as a statement.
--
--   c ⇒_d c′  ⟹  C⟦d̲⟧ c̄ = c̄′
--
-- i.e. the translated rule, run on a store holding c, terminates on a store
-- holding c′ with the scratch variables clear again.  (Milestone 2 proves
-- this; it is stated here so that the milestone is a type, not prose.)

Lemma1 : RTM → Set
Lemma1 M = ∀ d c c′ σ
         → d ∈ rules M
         → Step M c c′
         → HoldsConf c σ → Scratch-nil σ
         → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
             ( (ruleC (blank M) d ⊢ σ ⇒ σ′ ∣ k) × HoldsConf c′ σ′ × Scratch-nil σ′ )

------------------------------------------------------------------------
-- 11.  THEOREM 2 of the letter, as a statement: R-WHILE is r-Turing
-- complete.
--
--   r′ = ⟦T⟧^TM r  ⟹  r̄′ = ⟦T̲⟧^R-WHILE r̄
--
-- Stated existentially over the program, so that it does not presuppose any
-- particular translation: for every RTM there IS an R-WHILE program (a
-- first-order `Cmd`) that simulates it.  The output condition asks that R′
-- hold the encoded result and every other variable be nil — the letter's
-- "the rest of main only initialises, swaps and clears to nil".

AllNilBut : ℕ → Store → Set
AllNilBut x σ = ∀ y → ¬ (y ≡ x) → get σ y ≡ nil

inStore : List ℕ → Store
inStore r = set [] vIn (encL r)

rTuringComplete : Set
rTuringComplete =
  ∀ (M : RTM) → IsRTM M
  → Σ[ C ∈ Cmd ] ( ∀ r r′
      → Step* M (q-s M , ([] , blank M , r)) (q-f M , ([] , blank M , r′))
      → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
          ( (C ⊢ inStore r ⇒ σ′ ∣ k) × (get σ′ vOut ≡ encL r′) × AllNilBut vOut σ′ ) )
