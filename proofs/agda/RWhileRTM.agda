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
-- STATUS.  R-TURING COMPLETENESS IS PROVED (`rTuringComplete`), together
-- with the letter's Lemma 1 (`ubody-sound`) and Theorem 2 (`Main.theorem2`).
-- The chain is:
--
--   push-sound / pop-sound        PUSH and POP (Fig. 2d), both cases
--   unpack-sound / pack-sound     the pattern replacement `q <= r`
--   moveL-sound / moveR-sound     the head moves (Fig. 2c)
--   movel-mover / mover-movel     movel and mover are mutually inverse on
--                                 canonical tapes — what the letter's
--                                 converse-stated right move needs
--   usym/umvS/umvL/umvR-sound     the four rule shapes of Fig. 3
--   ubody-sound                   = the letter's Lemma 1
--   lfd-fires / lbd-fires         the RTM conditions in the form the
--                                 dispatch consumes
--   dispatch-sound / step-sound   STEP (Fig. 2b) as a chain of binary
--                                 conditionals
--   loop-sound                    the induction on the number of steps
--   theorem2                      r̄′ = ⟦T̲⟧ r̄, with nothing else left behind
--   wf-mainC                      and the program is legal R-WHILE
--
-- Section 12 exhibits a machine satisfying the hypotheses and runs the
-- theorem on it, so none of this is vacuous.
--
-- No postulates, no holes.
------------------------------------------------------------------------

module RWhileRTM where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileTimeInv using (inv)
open import RWhileSIWf
  using (get-set-≡; get-set-≢; Wf; wf-skip; wf-ass; wf-seq; wf-cond; wf-loop;
         NotIn; ni-opd; ni-cns; ni-hd; ni-tl; ni-eq; ni-pr; ni-var; ni-cst)

open import RWhileRTM4 public

------------------------------------------------------------------------
-- 11.  THE MAIN PROGRAM (Fig. 2a) AND THEOREM 2.
--
--   read R;
--     Q ^= q̄_s ; T <= (nil b̄ R) ;
--     from (=? Q q̄_s) loop STEP(Q,T) until (=? Q q̄_f) ;
--     (nil b̄ R') <= T ; Q ^= q̄_f ;
--   write R'
--
-- Here the tape is unpacked (§7c), so `T <= (nil b̄ R)` becomes: set S to
-- the blank, move the input into R, leave L empty, and establish the key.
-- The letter's "the rest of main only initialises, swaps values and clears
-- to nil" is exactly what `initC` and `finalC` do.

stepBy-src : ∀ b d q t c′ → StepBy b d (q , t) c′ → src d ≡ q
stepBy-src b (rsym _ _ _ _) _ _ _ sb-sym     = refl
stepBy-src b (rmov _ _ _)   _ _ _ sb-lft     = refl
stepBy-src b (rmov _ _ _)   _ _ _ sb-sty     = refl
stepBy-src b (rmov _ _ _)   _ _ _ (sb-rgt _) = refl

stepBy-tgt : ∀ b d q t q′ t′ → StepBy b d (q , t) (q′ , t′) → tgt d ≡ q′
stepBy-tgt b (rsym _ _ _ _) _ _ _ _ sb-sym     = refl
stepBy-tgt b (rmov _ _ _)   _ _ _ _ sb-lft     = refl
stepBy-tgt b (rmov _ _ _)   _ _ _ _ sb-sty     = refl
stepBy-tgt b (rmov _ _ _)   _ _ _ _ (sb-rgt _) = refl

qTest : ∀ σ q p → get σ vQ ≡ atm q
      → evalT σ (eqE (var vQ) (cst (atm p))) ≡ just (eqℕ q p)
qTest σ q p h rewrite h = cong just (isTrue-boolV _)

-- A run of the machine, carrying the canonicity of every configuration it
-- passes through.  The letter's configurations are canonical BY DEFINITION
-- (it writes them in Q × (Σ∖{b})* × Σ × (Σ∖{b})*), and a right move is
-- stated by the converse of movel, so the successor's left half-tape is not
-- determined by the predecessor's — the invariant has to travel with the
-- derivation rather than be recomputed from its first configuration.
data StepsOK (M : RTM) : Conf → Conf → Set where
  sdone : ∀ {c} → TapeOK (blank M) (tpOf c) → StepsOK M c c
  sstep : ∀ {c c₁ c₂} → TapeOK (blank M) (tpOf c) → Step M c c₁
        → StepsOK M c₁ c₂ → StepsOK M c c₂

stepsOK-tape : ∀ {M c c′} → StepsOK M c c′ → TapeOK (blank M) (tpOf c)
stepsOK-tape (sdone tk)     = tk
stepsOK-tape (sstep tk _ _) = tk

initC : ℕ → ℕ → Cmd
initC qs b =
    vQ  ^= opd (cst (atm qs))     -- Q := q̄_s
  ⨾ vS  ^= opd (cst (atm b))      -- S := b̄   (the scanned cell is blank)
  ⨾ vR  ^= opd (var vIn)          -- R := In
  ⨾ vIn ^= opd (var vR)           -- clear In
  ⨾ setKey                        -- K := (Q . S)

finalC : ℕ → ℕ → Cmd
finalC qf b =
    setKey                        -- clear K
  ⨾ vQ   ^= opd (cst (atm qf))    -- clear Q
  ⨾ vS   ^= opd (cst (atm b))     -- clear S
  ⨾ vOut ^= opd (var vR)          -- Out := R
  ⨾ vR   ^= opd (var vOut)        -- clear R

mainC : RTM → Cmd
mainC M =
    initC (q-s M) (blank M)
  ⨾ loop (eqE (var vQ) (cst (atm (q-s M)))) skip (stepC (blank M) (rules M))
         (eqE (var vQ) (cst (atm (q-f M))))
  ⨾ finalC (q-f M) (blank M)

wf-mainC : ∀ M → Wf (mainC M)
wf-mainC M =
  wf-seq (wf-seq (wf-ass (ni-opd ni-cst))
         (wf-seq (wf-ass (ni-opd ni-cst))
         (wf-seq (wf-ass (ni-opd (ni-var (λ ()))))
         (wf-seq (wf-ass (ni-opd (ni-var (λ ())))) wf-setKey))))
  (wf-seq (wf-loop wf-skip (wf-stepC (blank M) (rules M)))
          (wf-seq wf-setKey
          (wf-seq (wf-ass (ni-opd ni-cst))
          (wf-seq (wf-ass (ni-opd ni-cst))
          (wf-seq (wf-ass (ni-opd (ni-var (λ ()))))
                  (wf-ass (ni-opd (ni-var (λ ())))))))))

AllNilBut : ℕ → Store → Set
AllNilBut x σ = ∀ y → ¬ (y ≡ x) → get σ y ≡ nil

inStore : List ℕ → Store
inStore r = set [] vIn (encL r)

-- everything above the ten variables the program uses
HiNil : Store → Set
HiNil σ = ∀ y → get σ (10 + y) ≡ nil

init-sound : ∀ qs b r
  → Σ[ σ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (initC qs b ⊢ inStore r ⇒ σ ∣ k)
      × HoldsU (qs , ([] , b , r)) σ
      × (get σ vW ≡ nil) × (get σ vT ≡ nil) × (get σ vTmp ≡ nil)
      × (get σ vIn ≡ nil) × (get σ vOut ≡ nil) × HiNil σ )
init-sound qs b r =
    ι5 , _
  , e-seq c1 (e-seq c2 (e-seq c3 (e-seq c4 c5)))
  , (g5Q , g5S , g5L , g5R , get-set-≡ ι4 vK (atm qs ∙ atm b))
  , dn vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())
  , dn vT (λ ()) (λ ()) (λ ()) (λ ()) (λ ())
  , dn vTmp (λ ()) (λ ()) (λ ()) (λ ()) (λ ())
  , g5In
  , dn vOut (λ ()) (λ ()) (λ ()) (λ ()) (λ ())
  , (λ y → dn (10 + y) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
  where
  σ0 : Store
  σ0 = inStore r
  ι1 ι2 ι3 ι4 ι5 : Store
  ι1 = set σ0 vQ  (atm qs)
  ι2 = set ι1 vS  (atm b)
  ι3 = set ι2 vR  (encL r)
  ι4 = set ι3 vIn nil
  ι5 = set ι4 vK  (atm qs ∙ atm b)

  z : ∀ y → ¬ (vIn ≡ y) → get σ0 y ≡ nil
  z y ne = get-set-≢ [] vIn y (encL r) ne
  gIn : get σ0 vIn ≡ encL r
  gIn = get-set-≡ [] vIn (encL r)

  c1 = constSet vQ (atm qs) σ0 (z vQ (λ ()))
  c2 = constSet vS (atm b)  ι1 (trans (get-set-≢ σ0 vQ vS (atm qs) (λ ())) (z vS (λ ())))
  g2In : get ι2 vIn ≡ encL r
  g2In = trans (get-set-≢ ι1 vS vIn (atm b) (λ ()))
               (trans (get-set-≢ σ0 vQ vIn (atm qs) (λ ())) gIn)
  g2R : get ι2 vR ≡ nil
  g2R = trans (get-set-≢ ι1 vS vR (atm b) (λ ()))
              (trans (get-set-≢ σ0 vQ vR (atm qs) (λ ())) (z vR (λ ())))
  c3 : (vR ^= opd (var vIn)) ⊢ ι2 ⇒ ι3 ∣ 1
  c3 = e-ass (cong just g2In)
             (subst (λ w → rupd w (encL r) ≡ just (encL r)) (sym g2R) refl)
  g3R : get ι3 vR ≡ encL r
  g3R = get-set-≡ ι2 vR (encL r)
  g3In : get ι3 vIn ≡ encL r
  g3In = trans (get-set-≢ ι2 vR vIn (encL r) (λ ())) g2In
  c4 : (vIn ^= opd (var vR)) ⊢ ι3 ⇒ ι4 ∣ 1
  c4 = e-ass (cong just g3R)
             (subst (λ w → rupd w (encL r) ≡ just nil) (sym g3In) (rupd-self (encL r)))
  g4Q : get ι4 vQ ≡ atm qs
  g4Q = trans (get-set-≢ ι3 vIn vQ nil (λ ()))
              (trans (get-set-≢ ι2 vR vQ (encL r) (λ ()))
              (trans (get-set-≢ ι1 vS vQ (atm b) (λ ())) (get-set-≡ σ0 vQ (atm qs))))
  g4S : get ι4 vS ≡ atm b
  g4S = trans (get-set-≢ ι3 vIn vS nil (λ ()))
              (trans (get-set-≢ ι2 vR vS (encL r) (λ ())) (get-set-≡ ι1 vS (atm b)))
  g4K : get ι4 vK ≡ nil
  g4K = trans (get-set-≢ ι3 vIn vK nil (λ ()))
        (trans (get-set-≢ ι2 vR vK (encL r) (λ ()))
        (trans (get-set-≢ ι1 vS vK (atm b) (λ ()))
        (trans (get-set-≢ σ0 vQ vK (atm qs) (λ ())) (z vK (λ ())))))
  c5 = setKey-set ι4 qs b g4Q g4S g4K

  g5Q : get ι5 vQ ≡ atm qs
  g5Q = trans (get-set-≢ ι4 vK vQ (atm qs ∙ atm b) (λ ())) g4Q
  g5S : get ι5 vS ≡ atm b
  g5S = trans (get-set-≢ ι4 vK vS (atm qs ∙ atm b) (λ ())) g4S
  g5R : get ι5 vR ≡ encL r
  g5R = trans (get-set-≢ ι4 vK vR (atm qs ∙ atm b) (λ ()))
              (trans (get-set-≢ ι3 vIn vR nil (λ ())) g3R)
  g5In : get ι5 vIn ≡ nil
  g5In = trans (get-set-≢ ι4 vK vIn (atm qs ∙ atm b) (λ ())) (get-set-≡ ι3 vIn nil)
  -- untouched variables come straight from the input store
  dn : ∀ y → ¬ (vQ ≡ y) → ¬ (vS ≡ y) → ¬ (vR ≡ y) → ¬ (vIn ≡ y) → ¬ (vK ≡ y)
     → get ι5 y ≡ nil
  dn y nQ nS nR nIn nK =
    trans (get-set-≢ ι4 vK y (atm qs ∙ atm b) nK)
    (trans (get-set-≢ ι3 vIn y nil nIn)
    (trans (get-set-≢ ι2 vR y (encL r) nR)
    (trans (get-set-≢ ι1 vS y (atm b) nS)
    (trans (get-set-≢ σ0 vQ y (atm qs) nQ) (z y nIn)))))
  g5L : get ι5 vL ≡ encL []
  g5L = dn vL (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

final-sound : ∀ qf b r′ σ
  → HoldsU (qf , ([] , b , r′)) σ
  → get σ vW ≡ nil → get σ vT ≡ nil → get σ vTmp ≡ nil
  → get σ vIn ≡ nil → get σ vOut ≡ nil → HiNil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (finalC qf b ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vOut ≡ encL r′) × AllNilBut vOut σ′ )
final-sound qf b r′ σ (hQ , hS , hL , hR , hK) hW hT hTmp hIn hOut hHi =
    φ5 , _
  , e-seq b1 (e-seq b2 (e-seq b3 (e-seq b4 b5)))
  , g5Out , allNil
  where
  φ1 φ2 φ3 φ4 φ5 : Store
  φ1 = set σ  vK   nil
  φ2 = set φ1 vQ   nil
  φ3 = set φ2 vS   nil
  φ4 = set φ3 vOut (encL r′)
  φ5 = set φ4 vR   nil

  b1 = setKey-clr σ qf b hQ hS hK
  g1Q : get φ1 vQ ≡ atm qf
  g1Q = trans (get-set-≢ σ vK vQ nil (λ ())) hQ
  b2 = constClr vQ (atm qf) φ1 g1Q
  g2S : get φ2 vS ≡ atm b
  g2S = trans (get-set-≢ φ1 vQ vS nil (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS)
  b3 = constClr vS (atm b) φ2 g2S
  g3R : get φ3 vR ≡ encL r′
  g3R = trans (get-set-≢ φ2 vS vR nil (λ ()))
        (trans (get-set-≢ φ1 vQ vR nil (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR))
  g3Out : get φ3 vOut ≡ nil
  g3Out = trans (get-set-≢ φ2 vS vOut nil (λ ()))
          (trans (get-set-≢ φ1 vQ vOut nil (λ ()))
                 (trans (get-set-≢ σ vK vOut nil (λ ())) hOut))
  b4 : (vOut ^= opd (var vR)) ⊢ φ3 ⇒ φ4 ∣ 1
  b4 = e-ass (cong just g3R)
             (subst (λ w → rupd w (encL r′) ≡ just (encL r′)) (sym g3Out) refl)
  g4Out : get φ4 vOut ≡ encL r′
  g4Out = get-set-≡ φ3 vOut (encL r′)
  g4R : get φ4 vR ≡ encL r′
  g4R = trans (get-set-≢ φ3 vOut vR (encL r′) (λ ())) g3R
  b5 : (vR ^= opd (var vOut)) ⊢ φ4 ⇒ φ5 ∣ 1
  b5 = e-ass (cong just g4Out)
             (subst (λ w → rupd w (encL r′) ≡ just nil) (sym g4R) (rupd-self (encL r′)))

  g5Out : get φ5 vOut ≡ encL r′
  g5Out = trans (get-set-≢ φ4 vR vOut nil (λ ())) g4Out
  -- what the five assignments left nil
  g5K : get φ5 vK ≡ nil
  g5K = trans (get-set-≢ φ4 vR vK nil (λ ()))
        (trans (get-set-≢ φ3 vOut vK (encL r′) (λ ()))
        (trans (get-set-≢ φ2 vS vK nil (λ ()))
        (trans (get-set-≢ φ1 vQ vK nil (λ ())) (get-set-≡ σ vK nil))))
  g5Q : get φ5 vQ ≡ nil
  g5Q = trans (get-set-≢ φ4 vR vQ nil (λ ()))
        (trans (get-set-≢ φ3 vOut vQ (encL r′) (λ ()))
        (trans (get-set-≢ φ2 vS vQ nil (λ ())) (get-set-≡ φ1 vQ nil)))
  g5S : get φ5 vS ≡ nil
  g5S = trans (get-set-≢ φ4 vR vS nil (λ ()))
        (trans (get-set-≢ φ3 vOut vS (encL r′) (λ ())) (get-set-≡ φ2 vS nil))
  g5R : get φ5 vR ≡ nil
  g5R = get-set-≡ φ4 vR nil
  -- and what it never touched
  keep : ∀ y → ¬ (y ≡ vK) → ¬ (y ≡ vQ) → ¬ (y ≡ vS) → ¬ (y ≡ vOut) → ¬ (y ≡ vR)
       → get φ5 y ≡ get σ y
  keep y yK yQ yS yOut yR =
    trans (get-set-≢ φ4 vR y nil (λ e → yR (sym e)))
    (trans (get-set-≢ φ3 vOut y (encL r′) (λ e → yOut (sym e)))
    (trans (get-set-≢ φ2 vS y nil (λ e → yS (sym e)))
    (trans (get-set-≢ φ1 vQ y nil (λ e → yQ (sym e)))
           (get-set-≢ σ vK y nil (λ e → yK (sym e))))))

  allNil : AllNilBut vOut φ5
  allNil 0 _ = g5Q
  allNil 1 _ = trans (keep vT (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hT
  allNil 2 _ = trans (keep vL (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hL
  allNil 3 _ = g5S
  allNil 4 _ = g5R
  allNil 5 _ = trans (keep vTmp (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hTmp
  allNil 6 _ = trans (keep vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hW
  allNil 7 _ = trans (keep vIn (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hIn
  allNil 8 ne = ⊥-elim (ne refl)
  allNil 9 _ = g5K
  allNil (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc y)))))))))) _ =
    trans (keep (10 + y) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) (hHi y)

------------------------------------------------------------------------
-- THE LOOP, AND THEOREM 2.

module Main (M : RTM) (ok : IsRTM M) where
  open IsRTM ok
  open Dispatch M ok

  -- The letter proves Theorem 2 "by induction on the number of occurrences
  -- of ⇒".  Here that is an induction on the StepsOK derivation, building
  -- the core's `Rest` chain.  Two of the four RTM conditions are used here:
  -- NO RULE LEAVES q_f (so the until-test is false while steps remain) and
  -- NO RULE ENTERS q_s (so the from-test is false after each step, which is
  -- what a reversible loop asserts).
  loop-sound : ∀ q l x r σ r′
    → StepsOK M (q , (l , x , r)) (q-f M , ([] , blank M , r′))
    → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
    → Σ[ σ′ ∈ Store ] Σ[ n ∈ ℕ ]
        ( Rest (eqE (var vQ) (cst (atm (q-s M)))) skip (stepC (blank M) (rules M))
               (eqE (var vQ) (cst (atm (q-f M)))) σ σ′ n
        × HoldsU (q-f M , ([] , blank M , r′)) σ′
        × (get σ′ vW ≡ nil) × UFrame σ′ σ )
  loop-sound q l x r σ r′ (sdone tk) (hQ , hS , hL , hR , hK) hW =
      σ , _
    , r-exit (trans (qTest σ q (q-f M) hQ) (cong just (eqℕ-refl q)))
    , (hQ , hS , hL , hR , hK) , hW , (λ _ _ _ _ _ _ _ → refl)
  loop-sound q l x r σ r′ (sstep {c₁ = c₁} tk stp rest)
             (hQ , hS , hL , hR , hK) hW
    with step-splits stp
  ... | d , md , sb
    with step-sound q l x r (stOf c₁) (tpOf c₁) σ stp tk (stepsOK-tape rest)
                    (hQ , hS , hL , hR , hK) hW
  ...  | σ₁ , _ , dStep , (h1Q , h1S , h1L , h1R , h1K) , hW₁ , fr₁
    with loop-sound (stOf c₁) (lefts (tpOf c₁)) (symOf (tpOf c₁)) (rights (tpOf c₁))
                    σ₁ r′ rest (h1Q , h1S , h1L , h1R , h1K) hW₁
  ...   | σ′ , _ , dRest , hu′ , hW′ , fr₂ =
          σ′ , _
        , r-iter fFalse dStep eFalse e-skip dRest
        , hu′ , hW′ , (λ y a b′ c d e f → trans (fr₂ y a b′ c d e f) (fr₁ y a b′ c d e f))
        where
        qNotF : ¬ (q ≡ q-f M)
        qNotF p = nff d md (trans (stepBy-src (blank M) d q (l , x , r) c₁ sb) p)
        fFalse : evalT σ (eqE (var vQ) (cst (atm (q-f M)))) ≡ just false
        fFalse = trans (qTest σ q (q-f M) hQ)
                       (cong just (eqℕ-false q (q-f M) qNotF))
        notS : ¬ (stOf c₁ ≡ q-s M)
        notS p = nis d md
          (trans (stepBy-tgt (blank M) d q (l , x , r) (stOf c₁) (tpOf c₁) sb) p)
        eFalse : evalT σ₁ (eqE (var vQ) (cst (atm (q-s M)))) ≡ just false
        eFalse = trans (qTest σ₁ (stOf c₁) (q-s M) h1Q)
                       (cong just (eqℕ-false (stOf c₁) (q-s M) notS))

  -- THEOREM 2 (青木・横山 2018).  If the machine takes the input tape r to
  -- the output tape r′, the generated R-WHILE program takes r̄ to r̄′ — and
  -- leaves nothing else behind.
  theorem2 : ∀ r r′
    → StepsOK M (q-s M , ([] , blank M , r)) (q-f M , ([] , blank M , r′))
    → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
        ( (mainC M ⊢ inStore r ⇒ σ′ ∣ k)
        × (get σ′ vOut ≡ encL r′) × AllNilBut vOut σ′ )
  theorem2 r r′ steps
    with init-sound (q-s M) (blank M) r
  ... | σ₀ , _ , dInit , hu₀ , hW₀ , hT₀ , hTmp₀ , hIn₀ , hOut₀ , hHi₀
    with loop-sound (q-s M) [] (blank M) r σ₀ r′ steps hu₀ hW₀
  ...  | σ₁ , _ , dRest , hu₁ , hW₁ , fr
    with final-sound (q-f M) (blank M) r′ σ₁ hu₁ hW₁
           (trans (fr vT (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hT₀)
           (trans (fr vTmp (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hTmp₀)
           (trans (fr vIn (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hIn₀)
           (trans (fr vOut (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hOut₀)
           (λ y → trans (fr (10 + y) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) (hHi₀ y))
  ...   | σ′ , _ , dFin , gOut , anb =
          σ′ , _
        , e-seq dInit (e-seq (e-loop entryT e-skip dRest) dFin)
        , gOut , anb
    where
    entryT : evalT σ₀ (eqE (var vQ) (cst (atm (q-s M)))) ≡ just true
    entryT = trans (qTest σ₀ (q-s M) (q-s M) (proj₁ hu₀))
                   (cong just (eqℕ-refl (q-s M)))

------------------------------------------------------------------------
-- R-TURING COMPLETENESS.
--
-- For every reversible Turing machine there IS an R-WHILE program — a
-- first-order `Cmd`, satisfying R-WHILE's linearity condition — that
-- simulates it.

rTuringComplete :
  ∀ (M : RTM) → IsRTM M
  → Σ[ C ∈ Cmd ]
      ( Wf C
      × ( ∀ r r′
        → StepsOK M (q-s M , ([] , blank M , r)) (q-f M , ([] , blank M , r′))
        → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
            ( (C ⊢ inStore r ⇒ σ′ ∣ k)
            × (get σ′ vOut ≡ encL r′) × AllNilBut vOut σ′ ) ) )
rTuringComplete M ok = mainC M , wf-mainC M , Main.theorem2 M ok

------------------------------------------------------------------------
-- 12.  NON-VACUITY.
--
-- The theorem above is only worth having if its hypotheses can be met, so
-- here is a machine that meets them: one state change, no tape motion.  Its
-- four RTM conditions are discharged and a run is exhibited, which forces
-- `theorem2` to actually produce a derivation of the generated program.

module Example where

  Mid : RTM
  Mid = record { rules = rmov 0 mvS 1 ∷ [] ; blank = 0 ; q-s = 0 ; q-f = 1 }

  mem-one : ∀ {d : Rule} {e : Rule} → d ∈ (e ∷ []) → d ≡ e
  mem-one (here p)  = p
  mem-one (there ())

  0≢1 : ¬ (0 ≡ 1)
  0≢1 ()
  1≢0 : ¬ (1 ≡ 0)
  1≢0 ()

  MidOK : IsRTM Mid
  MidOK = record { lfd = lfd′ ; lbd = lbd′ ; nff = nff′ ; nis = nis′ }
    where
    lfd′ : LFD Mid
    lfd′ d₁ d₂ m₁ m₂ ne _ =
      ⊥-elim (ne (trans (mem-one m₁) (sym (mem-one m₂))))
    lbd′ : LBD Mid
    lbd′ d₁ d₂ m₁ m₂ ne _ =
      ⊥-elim (ne (trans (mem-one m₁) (sym (mem-one m₂))))
    nff′ : NoFromFinal Mid
    nff′ d m p = 0≢1 (subst (λ z → src z ≡ 1) (mem-one m) p)
    nis′ : NoIntoStart Mid
    nis′ d m p = 1≢0 (subst (λ z → tgt z ≡ 0) (mem-one m) p)

  -- the one-step run  (q_s,(λ,b,r)) ⇒ (q_f,(λ,b,r))
  MidRun : ∀ r → NoTrailB 0 r
         → StepsOK Mid (0 , ([] , 0 , r)) (1 , ([] , 0 , r))
  MidRun r nt = sstep (nt-[] , nt) (st-sty (here refl)) (sdone (nt-[] , nt))

  -- so the generated program really runs, on a real input store
  MidSim : ∀ r → NoTrailB 0 r
         → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
             ( (mainC Mid ⊢ inStore r ⇒ σ′ ∣ k)
             × (get σ′ vOut ≡ encL r) × AllNilBut vOut σ′ )
  MidSim r nt = Main.theorem2 Mid MidOK r r (MidRun r nt)

  -- and the same through the headline statement
  MidComplete : Σ[ C ∈ Cmd ]
      ( Wf C
      × ( ∀ r r′
        → StepsOK Mid (0 , ([] , 0 , r)) (1 , ([] , 0 , r′))
        → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
            ( (C ⊢ inStore r ⇒ σ′ ∣ k)
            × (get σ′ vOut ≡ encL r′) × AllNilBut vOut σ′ ) ) )
  MidComplete = rTuringComplete Mid MidOK
