{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick P3 (part 1): OPERAND evaluation.
--
-- `opdC r` evaluates an encoded operand (`El` holds ('var . num j) or
-- ('cst . v)) into the register `r`:
--
--     Ot ^= hd El ;
--     if =? Ot 'var then Kk ^= tl El ; lkTo r ; Kk ^= tl El
--                   else r ^= tl El
--     fi =? Ot 'var ;
--     Ot ^= hd El
--
-- Two things to note.  (i) The dispatch is a legal R-WHILE conditional
-- because the branches leave `Ot` alone, so the ENTRY TEST doubles as the
-- EXIT ASSERTION -- the discipline every dispatch in this development
-- follows.  (ii) The net effect is a single `r ^= value`, with every scratch
-- register restored, so `opdC r` is a PARTIAL INVOLUTION: running it twice
-- clears `r` again.  That is how the interpreter uncomputes without any
-- extra code (`ri.rwhile`'s `INV-` macros).
--
-- Costs are tracked as BOUNDS via RWhileSIRun: reading variable k costs
-- `60k + 27` (the walk), so an operand costs at most `60k + 36`.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIEval where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoˡ-≤; *-monoˡ-≤; m≤n+m; ≤-step
        ; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

open import RWhileTime
open import RWhileSIEnc using (num; encS; t-var; t-cst; t-opd; t-cns; t-hd; t-tl; t-eq; t-pr
                             ; ⌜_⌝ᵒ; ⌜_⌝ᵉ; vmaxᵒ; vmaxᵉ; dummyOpd)
open import RWhileSIMac
open import RWhileSIWalk
open import RWhileSILookup
open import RWhileSIRun

------------------------------------------------------------------------
-- Copying the head register into the operand registers.

cpy-hd-a1 : ∀ cd dn vl tg ag t1 t2 h vv kk cn rv el ww a2 t3 etg ot
  → cpy iHd iA1
      ⊢ emb (mkI cd dn vl tg ag t1 t2 h vv kk cn rv el ww nil a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag t1 t2 h vv kk cn rv el ww h   a2 t3 etg ot) ∣ 1
cpy-hd-a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = e-ass refl refl

cpy-hd-a2 : ∀ cd dn vl tg ag t1 t2 h vv kk cn rv el ww a1 t3 etg ot
  → cpy iHd iA2
      ⊢ emb (mkI cd dn vl tg ag t1 t2 h vv kk cn rv el ww a1 nil t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag t1 t2 h vv kk cn rv el ww a1 h   t3 etg ot) ∣ 1
cpy-hd-a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = e-ass refl refl

------------------------------------------------------------------------
-- LOOKUP into an arbitrary target register.

lkTo : ℕ → Cmd
lkTo r = walk ⨾ pop iT1 iHd iVl ⨾ cpy iHd r ⨾ push iT1 iHd iVl ⨾ back

lkB : ℕ → ℕ
lkB k = k * 56 + 27

lk-run-a1 : ∀ (pre post : List V) (v w u : V) → rupd w v ≡ just u
  → ∀ cd dn tg ag t2 vv el ww a2 t3 etg ot
  → Run (lkTo iA1)
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  (num (length pre)) (num 0) nil el ww w a2 t3 etg ot))
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  (num (length pre)) (num 0) nil el ww u a2 t3 etg ot))
        (lkB (length pre))
lk-run-a1 pre post v w u ru cd dn tg ag t2 vv el ww a2 t3 etg ot =
  rWeak (≤-reflexive (lk-cost (length pre))) (rOf
    (e-seq (walk-run0 pre (v ∷ post) cd dn tg ag t2 vv el ww w a2 t3 etg ot)
     (e-seq (pop-hd-vl cd dn v (encS post) tg ag t2 vv (num (length pre))
                       (num (length pre)) (encS (revApp pre [])) el ww w a2 t3 etg ot)
      (e-seq (e-ass refl ru)
       (e-seq (push-hd-vl cd dn (encS post) tg ag t2 v vv (num (length pre))
                          (num (length pre)) (encS (revApp pre [])) el ww u a2 t3 etg ot)
              (back-run0 pre (v ∷ post) cd dn tg ag t2 vv el ww u a2 t3 etg ot))))))

lk-run-a2 : ∀ (pre post : List V) (v w u : V) → rupd w v ≡ just u
  → ∀ cd dn tg ag t2 vv el ww a1 t3 etg ot
  → Run (lkTo iA2)
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  (num (length pre)) (num 0) nil el ww a1 w t3 etg ot))
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  (num (length pre)) (num 0) nil el ww a1 u t3 etg ot))
        (lkB (length pre))
lk-run-a2 pre post v w u ru cd dn tg ag t2 vv el ww a1 t3 etg ot =
  rWeak (≤-reflexive (lk-cost (length pre))) (rOf
    (e-seq (walk-run0 pre (v ∷ post) cd dn tg ag t2 vv el ww a1 w t3 etg ot)
     (e-seq (pop-hd-vl cd dn v (encS post) tg ag t2 vv (num (length pre))
                       (num (length pre)) (encS (revApp pre [])) el ww a1 w t3 etg ot)
      (e-seq (e-ass refl ru)
       (e-seq (push-hd-vl cd dn (encS post) tg ag t2 v vv (num (length pre))
                          (num (length pre)) (encS (revApp pre [])) el ww a1 u t3 etg ot)
              (back-run0 pre (v ∷ post) cd dn tg ag t2 vv el ww a1 u t3 etg ot))))))

------------------------------------------------------------------------
-- Operand evaluation.

opdC : ℕ → Cmd
opdC r = (iOt ^= hdE (var iEl))
       ⨾ cond (eqE (var iOt) (cst (atm t-var)))
              ((iKk ^= tlE (var iEl)) ⨾ lkTo r ⨾ (iKk ^= tlE (var iEl)))
              (r ^= tlE (var iEl))
              (eqE (var iOt) (cst (atm t-var)))
       ⨾ (iOt ^= hdE (var iEl))

-- The bound is kept in the shape the combinators produce (cost arithmetic on
-- stuck terms does not compute); `lkB` is the only closed form we need.
opdB : ℕ → ℕ
opdB k = suc (1 + suc (suc (suc (1 + suc (lkB k + 1))) + 1))   -- = 56k + 36

-- a VARIABLE operand: walk the store and copy the cell
opd-var-a1 : ∀ (pre post : List V) (v w u : V) → rupd w v ≡ just u
  → ∀ cd dn tg ag t2 vv ww a2 t3 etg
  → Run (opdC iA1)
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  nil (num 0) nil (atm t-var ∙ num (length pre)) ww w a2 t3 etg nil))
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  nil (num 0) nil (atm t-var ∙ num (length pre)) ww u a2 t3 etg nil))
        (opdB (length pre))
opd-var-a1 pre post v w u ru cd dn tg ag t2 vv ww a2 t3 etg =
  (rSeq (rAss refl refl)
      (rSeq (rThen refl
               (rSeq (rAss refl refl)
                 (rSeq (lk-run-a1 pre post v w u ru cd dn tg ag t2 vv
                                  (atm t-var ∙ num (length pre)) ww a2 t3 etg (atm t-var))
                       (rAss refl (rupd-self (num (length pre))))))
               refl)
            (rAss refl (rupd-self (atm t-var)))))

-- a CONSTANT operand: just read it out of the code
opd-cst-a1 : ∀ (σ : List V) (v w u : V) → rupd w v ≡ just u
  → ∀ cd dn tg ag t2 vv ww a2 t3 etg
  → Run (opdC iA1)
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil (num 0) nil
                  (atm t-cst ∙ v) ww w a2 t3 etg nil))
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil (num 0) nil
                  (atm t-cst ∙ v) ww u a2 t3 etg nil))
        6
opd-cst-a1 σ v w u ru cd dn tg ag t2 vv ww a2 t3 etg =
  rSeq (rAss refl refl)
    (rSeq (rElse refl (rAss refl ru) refl)
          (rAss refl (rupd-self (atm t-cst))))

------------------------------------------------------------------------
-- The operand bound in closed form, and its monotonicity.

opdB-closed : ∀ k → opdB k ≡ k * 56 + 36
opdB-closed = solve 1 (λ k → con 7 :+ ((k :* con 56 :+ con 27 :+ con 1) :+ con 1)
                          := k :* con 56 :+ con 36) refl

opdB-mono : ∀ {j k} → j ≤ k → j * 56 + 36 ≤ k * 56 + 36
opdB-mono le = +-monoˡ-≤ 36 (*-monoˡ-≤ 56 le)

length-≤-app : ∀ (pre : List V) (v : V) (post : List V) → length pre ≤ length (pre ++ v ∷ post)
length-≤-app []        v post = z≤n
length-≤-app (x ∷ pre) v post = s≤s (length-≤-app pre v post)

------------------------------------------------------------------------
-- The GENERIC operand lemma: one statement covering both operand forms,
-- with the cost bounded uniformly by the store size (`60·M + 36`).

opd-run-a1 : ∀ (σ : Store) (a : Opd) → vmaxᵒ a ≤ length σ
  → ∀ (w u : V) → rupd w (evalO σ a) ≡ just u
  → ∀ cd dn tg ag t2 vv ww a2 t3 etg
  → Run (opdC iA1)
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil nil nil ⌜ a ⌝ᵒ ww w a2 t3 etg nil))
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil nil nil ⌜ a ⌝ᵒ ww u a2 t3 etg nil))
        (length σ * 56 + 36)
opd-run-a1 σ (cst v) _ w u ru cd dn tg ag t2 vv ww a2 t3 etg =
  rWeak (≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (m≤n+m 36 (length σ * 56)))
        (opd-cst-a1 σ v w u ru cd dn tg ag t2 vv ww a2 t3 etg)
opd-run-a1 σ (var x) lt w u ru cd dn tg ag t2 vv ww a2 t3 etg
  with split σ x lt
... | pre , v , post , refl , refl
  rewrite get-split pre v post =
  rWeak (≤-trans (≤-reflexive (opdB-closed (length pre)))
                 (opdB-mono (length-≤-app pre v post)))
        (opd-var-a1 pre post v w u ru cd dn tg ag t2 vv ww a2 t3 etg)

------------------------------------------------------------------------
-- The same, for the second operand register.

opd-var-a2 : ∀ (pre post : List V) (v w u : V) → rupd w v ≡ just u
  → ∀ cd dn tg ag t2 vv ww a1 t3 etg
  → Run (opdC iA2)
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  nil (num 0) nil (atm t-var ∙ num (length pre)) ww a1 w t3 etg nil))
        (emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil vv
                  nil (num 0) nil (atm t-var ∙ num (length pre)) ww a1 u t3 etg nil))
        (opdB (length pre))
opd-var-a2 pre post v w u ru cd dn tg ag t2 vv ww a1 t3 etg =
  rSeq (rAss refl refl)
    (rSeq (rThen refl
             (rSeq (rAss refl refl)
               (rSeq (lk-run-a2 pre post v w u ru cd dn tg ag t2 vv
                                (atm t-var ∙ num (length pre)) ww a1 t3 etg (atm t-var))
                     (rAss refl (rupd-self (num (length pre))))))
             refl)
          (rAss refl (rupd-self (atm t-var))))

opd-cst-a2 : ∀ (σ : List V) (v w u : V) → rupd w v ≡ just u
  → ∀ cd dn tg ag t2 vv ww a1 t3 etg
  → Run (opdC iA2)
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil (num 0) nil
                  (atm t-cst ∙ v) ww a1 w t3 etg nil))
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil (num 0) nil
                  (atm t-cst ∙ v) ww a1 u t3 etg nil))
        6
opd-cst-a2 σ v w u ru cd dn tg ag t2 vv ww a1 t3 etg =
  rSeq (rAss refl refl)
    (rSeq (rElse refl (rAss refl ru) refl)
          (rAss refl (rupd-self (atm t-cst))))

opd-run-a2 : ∀ (σ : Store) (a : Opd) → vmaxᵒ a ≤ length σ
  → ∀ (w u : V) → rupd w (evalO σ a) ≡ just u
  → ∀ cd dn tg ag t2 vv ww a1 t3 etg
  → Run (opdC iA2)
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil nil nil ⌜ a ⌝ᵒ ww a1 w t3 etg nil))
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil vv nil nil nil ⌜ a ⌝ᵒ ww a1 u t3 etg nil))
        (length σ * 56 + 36)
opd-run-a2 σ (cst v) _ w u ru cd dn tg ag t2 vv ww a1 t3 etg =
  rWeak (≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (m≤n+m 36 (length σ * 56)))
        (opd-cst-a2 σ v w u ru cd dn tg ag t2 vv ww a1 t3 etg)
opd-run-a2 σ (var x) lt w u ru cd dn tg ag t2 vv ww a1 t3 etg
  with split σ x lt
... | pre , v , post , refl , refl
  rewrite get-split pre v post =
  rWeak (≤-trans (≤-reflexive (opdB-closed (length pre)))
                 (opdB-mono (length-≤-app pre v post)))
        (opd-var-a2 pre post v w u ru cd dn tg ag t2 vv ww a1 t3 etg)

------------------------------------------------------------------------
-- EXPRESSION evaluation.  Because expressions are encoded uniformly as
-- (tag . (operand1 . operand2)) (RWhileSIEnc), `evalC` can evaluate BOTH
-- operand slots before dispatching, so every dispatch branch is a single
-- assignment to `Vv`.  The whole thing is compute-use-uncompute, so its net
-- effect is `Vv ^= value` with every scratch register restored -- a partial
-- involution, which is exactly what the `ass` case needs in order to clear
-- the value register after the store update (`ri.rwhile`'s INV-EVAL-EXP).

etIs : ℕ → Exp
etIs t = eqE (var iEt) (cst (atm t))

EDISP : Cmd
EDISP =
  cond (etIs t-opd) (iVv ^= opd (var iA1))
   (cond (etIs t-cns) (iVv ^= cns (var iA1) (var iA2))
    (cond (etIs t-hd) (iVv ^= hdE (var iA1))
     (cond (etIs t-tl) (iVv ^= tlE (var iA1))
      (cond (etIs t-eq) (iVv ^= eqE (var iA1) (var iA2))
       (cond (etIs t-pr) (iVv ^= prE (var iA1)) skip (etIs t-pr))
       (etIs t-eq))
      (etIs t-tl))
     (etIs t-hd))
    (etIs t-cns))
   (etIs t-opd)

evalC : Cmd
evalC = (iEt ^= hdE (var iT2))
      ⨾ (iT3 ^= tlE (var iT2))
      ⨾ (iEl ^= hdE (var iT3)) ⨾ opdC iA1 ⨾ (iEl ^= hdE (var iT3))
      ⨾ (iEl ^= tlE (var iT3)) ⨾ opdC iA2 ⨾ (iEl ^= tlE (var iT3))
      ⨾ EDISP
      ⨾ (iEl ^= tlE (var iT3)) ⨾ opdC iA2 ⨾ (iEl ^= tlE (var iT3))
      ⨾ (iEl ^= hdE (var iT3)) ⨾ opdC iA1 ⨾ (iEl ^= hdE (var iT3))
      ⨾ (iT3 ^= tlE (var iT2))
      ⨾ (iEt ^= hdE (var iT2))

-- the cost bound, in the shape the `Run` combinators produce (`stp a b` is
-- one `;` node).  P M = 56·M + 36 is the operand bound, 7 the dispatch
-- (six conditional levels, then one assignment).
private
  stp : ℕ → ℕ → ℕ
  stp a b = suc (a + b)

P : ℕ → ℕ
P M = M * 56 + 36

evalB : ℕ → ℕ
evalB M =
  stp 1 (stp 1 (stp 1 (stp (P M) (stp 1 (stp 1 (stp (P M) (stp 1
  (stp 7 (stp 1 (stp (P M) (stp 1 (stp 1 (stp (P M) (stp 1 (stp 1 1)))))))))))))))

------------------------------------------------------------------------
-- The dispatch, per expression form: each branch is one assignment, so all
-- six weaken to the same bound 7.

eval-run : ∀ (σ : Store) (e : Exp) → vmaxᵉ e ≤ length σ
  → ∀ (v w u : V) → evalE σ e ≡ just v → rupd w v ≡ just u
  → ∀ cd dn tg ag ww
  → Run evalC
        (emb (mkI cd dn (encS σ) tg ag nil ⌜ e ⌝ᵉ nil w nil nil nil nil ww nil nil nil nil nil))
        (emb (mkI cd dn (encS σ) tg ag nil ⌜ e ⌝ᵉ nil u nil nil nil nil ww nil nil nil nil nil))
        (evalB (length σ))
eval-run σ (opd a) lt v w u refl ru cd dn tg ag ww =
    rAss refl refl
  » rAss refl refl
  » rAss refl refl
  » opd-run-a1 σ a lt nil (evalO σ a) refl cd dn tg ag ⌜ opd a ⌝ᵉ w ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-opd)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ opd a ⌝ᵉ w ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-opd)
  » rAss refl (rupd-self dummyOpd)
  » disp
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ opd a ⌝ᵉ u ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-opd)
  » rAss refl (rupd-self dummyOpd)
  » rAss refl refl
  » opd-run-a1 σ a lt (evalO σ a) nil (rupd-self (evalO σ a)) cd dn tg ag ⌜ opd a ⌝ᵉ u ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-opd)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl (rupd-self (⌜ a ⌝ᵒ ∙ dummyOpd))
  » rAss refl (rupd-self (atm t-opd))
  where
    disp : Run EDISP _ _ 7
    disp = rWeak (s≤s (s≤s z≤n)) (rThen refl (rAss refl ru) refl)
eval-run σ (cns a b) lt v w u refl ru cd dn tg ag ww =
    rAss refl refl
  » rAss refl refl
  » rAss refl refl
  » opd-run-a1 σ a lta nil (evalO σ a) refl cd dn tg ag ⌜ cns a b ⌝ᵉ w ww nil
               (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-cns)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl refl
  » opd-run-a2 σ b ltb nil (evalO σ b) refl cd dn tg ag ⌜ cns a b ⌝ᵉ w ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-cns)
  » rAss refl (rupd-self ⌜ b ⌝ᵒ)
  » disp
  » rAss refl refl
  » opd-run-a2 σ b ltb (evalO σ b) nil (rupd-self (evalO σ b)) cd dn tg ag ⌜ cns a b ⌝ᵉ u ww
               (evalO σ a) (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-cns)
  » rAss refl (rupd-self ⌜ b ⌝ᵒ)
  » rAss refl refl
  » opd-run-a1 σ a lta (evalO σ a) nil (rupd-self (evalO σ a)) cd dn tg ag ⌜ cns a b ⌝ᵉ u ww nil
               (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-cns)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl (rupd-self (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ))
  » rAss refl (rupd-self (atm t-cns))
  where
    lta : vmaxᵒ a ≤ length σ
    lta = ≤-trans (m≤m⊔n (vmaxᵒ a) (vmaxᵒ b)) lt
    ltb : vmaxᵒ b ≤ length σ
    ltb = ≤-trans (m≤n⊔m (vmaxᵒ a) (vmaxᵒ b)) lt
    disp : Run EDISP _ _ 7
    disp = rWeak (s≤s (s≤s (s≤s z≤n)))
                 (rElse refl (rThen refl (rAss refl ru) refl) refl)
eval-run σ (hdE a) lt v w u ev ru cd dn tg ag ww =
    rAss refl refl
  » rAss refl refl
  » rAss refl refl
  » opd-run-a1 σ a lt nil (evalO σ a) refl cd dn tg ag ⌜ hdE a ⌝ᵉ w ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-hd)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ hdE a ⌝ᵉ w ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-hd)
  » rAss refl (rupd-self dummyOpd)
  » disp
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ hdE a ⌝ᵉ u ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-hd)
  » rAss refl (rupd-self dummyOpd)
  » rAss refl refl
  » opd-run-a1 σ a lt (evalO σ a) nil (rupd-self (evalO σ a)) cd dn tg ag ⌜ hdE a ⌝ᵉ u ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-hd)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl (rupd-self (⌜ a ⌝ᵒ ∙ dummyOpd))
  » rAss refl (rupd-self (atm t-hd))
  where
    disp : Run EDISP _ _ 7
    disp = rWeak (s≤s (s≤s (s≤s (s≤s z≤n))))
                 (rElse refl (rElse refl (rThen refl (rAss ev ru) refl) refl) refl)
eval-run σ (tlE a) lt v w u ev ru cd dn tg ag ww =
    rAss refl refl
  » rAss refl refl
  » rAss refl refl
  » opd-run-a1 σ a lt nil (evalO σ a) refl cd dn tg ag ⌜ tlE a ⌝ᵉ w ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-tl)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ tlE a ⌝ᵉ w ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-tl)
  » rAss refl (rupd-self dummyOpd)
  » disp
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ tlE a ⌝ᵉ u ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-tl)
  » rAss refl (rupd-self dummyOpd)
  » rAss refl refl
  » opd-run-a1 σ a lt (evalO σ a) nil (rupd-self (evalO σ a)) cd dn tg ag ⌜ tlE a ⌝ᵉ u ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-tl)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl (rupd-self (⌜ a ⌝ᵒ ∙ dummyOpd))
  » rAss refl (rupd-self (atm t-tl))
  where
    disp : Run EDISP _ _ 7
    disp = rWeak (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
                 (rElse refl (rElse refl (rElse refl (rThen refl (rAss ev ru) refl) refl)
                              refl) refl)
eval-run σ (eqE a b) lt v w u refl ru cd dn tg ag ww =
    rAss refl refl
  » rAss refl refl
  » rAss refl refl
  » opd-run-a1 σ a lta nil (evalO σ a) refl cd dn tg ag ⌜ eqE a b ⌝ᵉ w ww nil
               (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-eq)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl refl
  » opd-run-a2 σ b ltb nil (evalO σ b) refl cd dn tg ag ⌜ eqE a b ⌝ᵉ w ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-eq)
  » rAss refl (rupd-self ⌜ b ⌝ᵒ)
  » disp
  » rAss refl refl
  » opd-run-a2 σ b ltb (evalO σ b) nil (rupd-self (evalO σ b)) cd dn tg ag ⌜ eqE a b ⌝ᵉ u ww
               (evalO σ a) (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-eq)
  » rAss refl (rupd-self ⌜ b ⌝ᵒ)
  » rAss refl refl
  » opd-run-a1 σ a lta (evalO σ a) nil (rupd-self (evalO σ a)) cd dn tg ag ⌜ eqE a b ⌝ᵉ u ww nil
               (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ) (atm t-eq)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl (rupd-self (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ))
  » rAss refl (rupd-self (atm t-eq))
  where
    lta : vmaxᵒ a ≤ length σ
    lta = ≤-trans (m≤m⊔n (vmaxᵒ a) (vmaxᵒ b)) lt
    ltb : vmaxᵒ b ≤ length σ
    ltb = ≤-trans (m≤n⊔m (vmaxᵒ a) (vmaxᵒ b)) lt
    disp : Run EDISP _ _ 7
    disp = rWeak (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
                 (rElse refl (rElse refl (rElse refl (rElse refl
                   (rThen refl (rAss refl ru) refl) refl) refl) refl) refl)

eval-run σ (prE a) lt v w u refl ru cd dn tg ag ww =
    rAss refl refl
  » rAss refl refl
  » rAss refl refl
  » opd-run-a1 σ a lt nil (evalO σ a) refl cd dn tg ag ⌜ prE a ⌝ᵉ w ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-pr)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ prE a ⌝ᵉ w ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-pr)
  » rAss refl (rupd-self dummyOpd)
  » disp
  » rAss refl refl
  » opd-run-a2 σ (cst nil) z≤n nil nil refl cd dn tg ag ⌜ prE a ⌝ᵉ u ww (evalO σ a)
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-pr)
  » rAss refl (rupd-self dummyOpd)
  » rAss refl refl
  » opd-run-a1 σ a lt (evalO σ a) nil (rupd-self (evalO σ a)) cd dn tg ag ⌜ prE a ⌝ᵉ u ww nil
               (⌜ a ⌝ᵒ ∙ dummyOpd) (atm t-pr)
  » rAss refl (rupd-self ⌜ a ⌝ᵒ)
  » rAss refl (rupd-self (⌜ a ⌝ᵒ ∙ dummyOpd))
  » rAss refl (rupd-self (atm t-pr))
  where
    disp : Run EDISP _ _ 7
    disp = rWeak ≤-refl
                 (rElse refl (rElse refl (rElse refl (rElse refl (rElse refl
                   (rThen refl (rAss refl ru) refl) refl) refl) refl) refl) refl)

------------------------------------------------------------------------
-- UPDATE, generic in the variable index: the object program's reversible
-- assignment, performed by the interpreter's own `^=` on the walked cell.

lkB-mono : ∀ {j k} → j ≤ k → j * 56 + 27 ≤ k * 56 + 27
lkB-mono le = +-monoˡ-≤ 27 (*-monoˡ-≤ 56 le)

upd-run-gen : ∀ (σ : Store) (x : ℕ) (w u : V) → suc x ≤ length σ
  → rupd (get σ x) w ≡ just u
  → ∀ cd dn tg ag t2 el ww a1 a2 t3 etg ot
  → Run updE
        (emb (mkI cd dn (encS σ) tg ag nil t2 nil w
                  (num x) (num 0) nil el ww a1 a2 t3 etg ot))
        (emb (mkI cd dn (encS (set σ x u)) tg ag nil t2 nil w
                  (num x) (num 0) nil el ww a1 a2 t3 etg ot))
        (length σ * 56 + 27)
upd-run-gen σ x w u lt ru cd dn tg ag t2 el ww a1 a2 t3 etg ot
  with split σ x lt
... | pre , v , post , refl , refl
  rewrite get-split pre v post | set-split pre v post u =
  rWeak (≤-trans (≤-reflexive (lk-cost (length pre))) (lkB-mono (length-≤-app pre v post)))
        (rOf (upd-run pre post v w u cd dn tg ag t2 el ww a1 a2 t3 etg ot ru))
