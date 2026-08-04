{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick P4: the dispatch body `STEP`, as an R-WHILE program.
--
-- Shape (exactly `ri.rwhile`'s `STEP` macro):
--
--     STEP = pop Cd→Hd ; split Hd into (Tg,Ag) ; DISPATCH ; build Hd ; push Hd→Dn
--
-- DISPATCH is a nest of conditionals on `Tg`, one level per machine tag.
-- The nest is a legal R-WHILE program because **every case leaves a DIFFERENT
-- tag in Tg** (skip 7, ass 8, seq→seqB 12, seqE→seq 9, cond→condB 14,
-- condE→cond 10, loop→loopB 16, lpA 17, lpB 18, lpZ→loop 11, lpC 20), so each
-- level's exit assertion `=? Tg <its final tag>` is true after its own branch
-- and false after every branch below it.  That the machine's own tag algebra
-- (RWhileSIMach.step1) already has this property is what makes the interpreter
-- reversible -- the same trick `ri.rwhile` plays with its `'seqB`/`'condB` tags.
--
-- The case bodies are separate definitions, filled in one brick at a time;
-- a not-yet-implemented case is a stub that only performs its tag flip, so
-- the nest -- and every already-proved case -- stays well-formed meanwhile.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIStep where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime
open import RWhileSIEnc
open import RWhileSIMach using (MSt; ⟨_,_,_⟩; astep)
import RWhileSIMach
open import RWhileSIMac
open import RWhileSIRun
open import RWhileSILookup using (updE)
open import RWhileSIEval using (evalC; evalB; eval-run; upd-run-gen)
open import RWhileSIWf using (NotIn; evalE-frame; length-set)

------------------------------------------------------------------------
-- A machine state as an interpreter store: the two stacks and the encoded
-- object store, with every scratch register cleared.

embM : V → V → Store → Store
embM td dn σ =
  emb (mkI td dn (encS σ) nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil)

------------------------------------------------------------------------
-- Splitting a task into tag and argument, and putting it back.

tagIs : ℕ → Exp
tagIs t = eqE (var iTg) (cst (atm t))

splitT buildT : Cmd
splitT = (iTg ^= hdE (var iHd)) ⨾ (iAg ^= tlE (var iHd)) ⨾ (iHd ^= cns (var iTg) (var iAg))
buildT = (iHd ^= cns (var iTg) (var iAg)) ⨾ (iAg ^= tlE (var iHd)) ⨾ (iTg ^= hdE (var iHd))

-- flipping the tag (clear the old constant, set the new one)
flipT : ℕ → ℕ → Cmd
flipT a b = (iTg ^= opd (cst (atm a))) ⨾ (iTg ^= opd (cst (atm b)))

------------------------------------------------------------------------
-- The case bodies.  `stepSkip` is the first one implemented; the others are
-- stubs performing only their tag flip (filled in by the following bricks).

stepSkip stepAss stepSeq stepSeqE stepCond stepCondE
  stepLoop stepLpA stepLpD stepLpB stepLpZ stepLpC : Cmd
stepSkip  = skip
-- 'ass : evaluate e into Vv, reversibly UPDATE the object store's cell x with
-- it (the object's `^=` performed by the interpreter's own `^=`), then run the
-- evaluation again to clear Vv.  The second run gives the same value because
-- x does not occur in e (R-WHILE's condition on assignments) -- RWhileSIWf's
-- `evalE-frame`.  This is `ri.rwhile`'s EVAL-EXP / UPDATE / INV-EVAL-EXP.
stepAss   = (iT2 ^= tlE (var iAg))
          ⨾ evalC
          ⨾ (iKk ^= hdE (var iAg))
          ⨾ updE
          ⨾ (iKk ^= hdE (var iAg))
          ⨾ evalC
          ⨾ (iT2 ^= tlE (var iAg))
-- 'seq : push ⌜c⌝, ⌜d⌝ and the seqE marker on the todo stack, and turn the
-- task into the (seqB . nil) record the epilogue pushes on the done stack.
stepSeq   = (iHd ^= opd (cst (atm t-seqE ∙ nil)))
          ⨾ push iT1 iHd iCd
          ⨾ (iHd ^= tlE (var iAg))
          ⨾ (iT2 ^= hdE (var iAg))
          ⨾ (iAg ^= cns (var iT2) (var iHd))
          ⨾ push iT1 iHd iCd
          ⨾ (iHd ^= opd (var iT2))
          ⨾ (iT2 ^= opd (var iHd))
          ⨾ push iT1 iHd iCd
          ⨾ flipT t-seq t-seqB
-- 'seqE : pop ⌜d⌝, ⌜c⌝ and the seqB record off the done stack and REASSEMBLE
-- the node ('seq . (c . d)) -- this is what makes the interpreter
-- program-preserving.
stepSeqE  = pop iT1 iHd iDn
          ⨾ (iT2 ^= opd (var iHd))
          ⨾ (iHd ^= opd (var iT2))
          ⨾ pop iT1 iHd iDn
          ⨾ (iAg ^= cns (var iHd) (var iT2))
          ⨾ (iHd ^= hdE (var iAg))
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ pop iT1 iHd iDn
          ⨾ (iHd ^= opd (cst (atm t-seqB ∙ nil)))
          ⨾ flipT t-seqE t-seq
-- 'cond : evaluate the test, canonicalise its truth into T3 (ri.rwhile's CANON),
-- push the taken branch and the (condE . b) marker, then UNCOMPUTE both the
-- canonicalisation and the test evaluation (each is an involution).
stepCond  = (iT2 ^= hdE (var iAg))
          ⨾ evalC
          ⨾ (iWw ^= eqE (var iVv) (cst nil))
          ⨾ (iT3 ^= eqE (var iWw) (cst nil))
          ⨾ (iHd ^= cns (cst (atm t-condE)) (var iT3))
          ⨾ push iT1 iHd iCd
          ⨾ (iKk ^= tlE (var iAg))
          ⨾ cond (opd (var iVv))
                 (iA1 ^= hdE (var iKk))
                 ((iEl ^= tlE (var iKk)) ⨾ (iA1 ^= hdE (var iEl)) ⨾ (iEl ^= tlE (var iKk)))
                 (opd (var iVv))
          ⨾ push iT1 iA1 iCd
          ⨾ (iKk ^= tlE (var iAg))
          ⨾ (iT3 ^= eqE (var iWw) (cst nil))
          ⨾ (iWw ^= eqE (var iVv) (cst nil))
          ⨾ evalC
          ⨾ (iT2 ^= hdE (var iAg))
          ⨾ flipT t-cond t-condB
-- 'condE : the taken branch has run.  Pop it and the (condB . A) record off
-- the done stack, EVALUATE THE EXIT ASSERTION and clear the recorded entry
-- test against it (that XOR *is* R-WHILE's assertion check: it succeeds
-- exactly when the two truth values agree), then reassemble ('cond . A).
-- `A` is kept in `Ww`, the only scratch register `evalC` does not touch.
stepCondE = pop iT1 iHd iDn
          ⨾ (iT2 ^= hdE (var iDn))
          ⨾ (iWw ^= tlE (var iT2))
          ⨾ (iKk ^= tlE (var iWw))
          ⨾ cond (opd (var iAg))
                 (iHd ^= hdE (var iKk))
                 ((iEl ^= tlE (var iKk)) ⨾ (iHd ^= hdE (var iEl)) ⨾ (iEl ^= tlE (var iKk)))
                 (opd (var iAg))
          ⨾ (iKk ^= tlE (var iWw))
          ⨾ (iT2 ^= cns (cst (atm t-condB)) (var iWw))
          ⨾ pop iT1 iHd iDn
          ⨾ (iHd ^= cns (cst (atm t-condB)) (var iWw))
          ⨾ (iKk ^= tlE (var iWw)) ⨾ (iEl ^= tlE (var iKk)) ⨾ (iT2 ^= tlE (var iEl))
          ⨾ (iEl ^= tlE (var iKk)) ⨾ (iKk ^= tlE (var iWw))
          ⨾ evalC
          ⨾ (iT3 ^= eqE (var iVv) (cst nil))
          ⨾ (iAg ^= eqE (var iT3) (cst nil))
          ⨾ (iT3 ^= eqE (var iVv) (cst nil))
          ⨾ evalC
          ⨾ (iKk ^= tlE (var iWw)) ⨾ (iEl ^= tlE (var iKk)) ⨾ (iT2 ^= tlE (var iEl))
          ⨾ (iEl ^= tlE (var iKk)) ⨾ (iKk ^= tlE (var iWw))
          ⨾ (iAg ^= opd (var iWw))
          ⨾ (iWw ^= opd (var iAg))
          ⨾ flipT t-condE t-cond
-- 'loop : run ⌜D⌝ first, then go to the lpA marker with the "first" flag set
stepLoop  = (iHd ^= cns (cst (atm t-lpA)) (var iAg))
          ⨾ push iT1 iHd iCd
          ⨾ flipT t-loop t-loopB
-- 'lpA : the loop's ENTRY TEST is checked here, before D runs.  Its truth
-- also says which arrival this is, so the context record (loopB . A) or
-- (lpC . A) can be erased with a KNOWN tag inside the corresponding branch --
-- this is what makes the step injective, hence writable in R-WHILE.
stepLpA   = (iT2 ^= hdE (var iAg))
          ⨾ evalC
          ⨾ cond (opd (var iVv))
                 (pop iT1 iHd iDn ⨾ (iHd ^= cns (cst (atm t-loopB)) (var iAg)))
                 (pop iT1 iHd iDn ⨾ (iHd ^= cns (cst (atm t-lpC)) (var iAg)))
                 (opd (var iVv))
          ⨾ evalC
          ⨾ (iT2 ^= hdE (var iAg))
          ⨾ (iHd ^= cns (cst (atm t-lpD)) (var iAg))
          ⨾ push iT1 iHd iCd
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ (iHd ^= hdE (var iT2))
          ⨾ push iT1 iHd iCd
          ⨾ (iT2 ^= tlE (var iAg))
-- 'lpD : D has run -- pop it and the lpA record, test the EXIT condition and
-- push the lpZ (exit) or lpB (continue) marker.
stepLpD   = pop iT1 iHd iDn
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ (iHd ^= hdE (var iT2))
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ pop iT1 iHd iDn
          ⨾ (iHd ^= cns (cst (atm t-lpA)) (var iAg))
          ⨾ (iWw ^= tlE (var iAg)) ⨾ (iKk ^= tlE (var iWw)) ⨾ (iT2 ^= tlE (var iKk))
          ⨾ (iKk ^= tlE (var iWw)) ⨾ (iWw ^= tlE (var iAg))
          ⨾ evalC
          ⨾ cond (opd (var iVv))
                 (iHd ^= cns (cst (atm t-lpZ)) (var iAg))
                 (iHd ^= cns (cst (atm t-lpB)) (var iAg))
                 (opd (var iVv))
          ⨾ push iT1 iHd iCd
          ⨾ evalC
          ⨾ (iWw ^= tlE (var iAg)) ⨾ (iKk ^= tlE (var iWw)) ⨾ (iT2 ^= tlE (var iKk))
          ⨾ (iKk ^= tlE (var iWw)) ⨾ (iWw ^= tlE (var iAg))
-- 'lpB : one more iteration -- pop the lpA record, push ⌜L⌝ and the lpC marker
stepLpB   = pop iT1 iHd iDn
          ⨾ (iHd ^= cns (cst (atm t-lpD)) (var iAg))
          ⨾ (iHd ^= cns (cst (atm t-lpC)) (var iAg))
          ⨾ push iT1 iHd iCd
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ (iT3 ^= tlE (var iT2))
          ⨾ (iHd ^= hdE (var iT3))
          ⨾ push iT1 iHd iCd
          ⨾ (iT3 ^= tlE (var iT2))
          ⨾ (iT2 ^= tlE (var iAg))
-- 'lpZ : the loop is over -- pop the lpA record and reassemble ⌜from e D L f⌝
stepLpZ   = pop iT1 iHd iDn
          ⨾ (iHd ^= cns (cst (atm t-lpD)) (var iAg))
          ⨾ flipT t-lpZ t-loop
-- 'lpC : the body has run -- discard the processed ⌜L⌝ and the lpB record
-- (both recomputable from Ag), then push ⌜D⌝ and the lpA marker again
stepLpC   = pop iT1 iHd iDn
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ (iT3 ^= tlE (var iT2))
          ⨾ (iHd ^= hdE (var iT3))
          ⨾ (iT3 ^= tlE (var iT2))
          ⨾ (iT2 ^= tlE (var iAg))
          ⨾ pop iT1 iHd iDn
          ⨾ (iHd ^= cns (cst (atm t-lpB)) (var iAg))
          ⨾ (iHd ^= cns (cst (atm t-lpA)) (var iAg))
          ⨾ push iT1 iHd iCd

DISPATCH : Cmd
DISPATCH =
  cond (tagIs t-skip)  stepSkip
   (cond (tagIs t-ass)   stepAss
    (cond (tagIs t-seq)   stepSeq
     (cond (tagIs t-seqE)  stepSeqE
      (cond (tagIs t-cond)  stepCond
       (cond (tagIs t-condE) stepCondE
        (cond (tagIs t-loop)  stepLoop
         (cond (tagIs t-lpA)   stepLpA
          (cond (tagIs t-lpB)   stepLpB
           (cond (tagIs t-lpZ)   stepLpZ
            (cond (tagIs t-lpC)   stepLpC
             (cond (tagIs t-lpD)  stepLpD skip (tagIs t-lpD))
             (tagIs t-lpC))
            (tagIs t-loop))
           (tagIs t-lpB))
          (tagIs t-lpA))
         (tagIs t-loopB))
        (tagIs t-cond))
       (tagIs t-condB))
      (tagIs t-seq))
     (tagIs t-seqB))
    (tagIs t-ass))
   (tagIs t-skip)

STEP : Cmd
STEP = (pop iT1 iHd iCd ⨾ splitT) ⨾ (DISPATCH ⨾ (buildT ⨾ push iT1 iHd iDn))

------------------------------------------------------------------------
-- The prologue and epilogue.

prologue : ∀ t a cd dn vl
  → Run (pop iT1 iHd iCd ⨾ splitT)
        (emb (mkI ((atm t ∙ a) ∙ cd) dn vl nil nil nil nil nil nil nil nil nil nil nil
                  nil nil nil nil nil))
        (emb (mkI cd dn vl (atm t) a nil nil nil nil nil nil nil nil nil
                  nil nil nil nil nil))
        15
prologue t a cd dn vl =
  rSeq (rOf (pop-gen (emb (mkI ((atm t ∙ a) ∙ cd) dn vl nil nil nil nil nil nil nil nil
                               nil nil nil nil nil nil nil nil))
                     iT1 iHd iCd (atm t ∙ a) cd (λ ()) (λ ()) (λ ()) refl refl refl))
       (rSeq (rAss refl refl) (rSeq (rAss refl refl) (rAss refl (rupd-self (atm t ∙ a)))))

epilogue : ∀ t a cd dn vl
  → Run (buildT ⨾ push iT1 iHd iDn)
        (emb (mkI cd dn vl (atm t) a nil nil nil nil nil nil nil nil nil
                  nil nil nil nil nil))
        (emb (mkI cd ((atm t ∙ a) ∙ dn) vl nil nil nil nil nil nil nil nil nil nil nil
                  nil nil nil nil nil))
        15
epilogue t a cd dn vl =
  rSeq (rSeq (rAss refl refl)
             (rSeq (rAss refl (rupd-self a)) (rAss refl (rupd-self (atm t)))))
       (rOf (push-gen (emb (mkI cd dn vl nil nil nil nil (atm t ∙ a) nil nil nil nil nil
                                nil nil nil nil nil nil))
                      iT1 iHd iDn (atm t ∙ a) dn (λ ()) (λ ()) (λ ()) refl refl refl))

------------------------------------------------------------------------
-- Case 1: `skip`.  The machine step is
--     ⟨('skip . nil) ∷ cd , dn , σ⟩  →  ⟨cd , ('skip . nil) ∷ dn , σ⟩
-- and the program takes 34 steps for it.

step-skip : ∀ cd dn σ
  → Run STEP (embM ((atm t-skip ∙ nil) ∙ cd) dn σ)
             (embM cd ((atm t-skip ∙ nil) ∙ dn) σ)
             34
step-skip cd dn σ =
  rSeq (prologue t-skip nil cd dn (encS σ))
    (rSeq (rThen refl rSkip refl)
          (epilogue t-skip nil cd dn (encS σ)))

-- and it agrees with the machine
step-skip-agrees : ∀ cd dn σ
  → astep ⟨ (atm t-skip ∙ nil) ∙ cd , dn , σ ⟩ ≡ just ⟨ cd , (atm t-skip ∙ nil) ∙ dn , σ ⟩
step-skip-agrees cd dn σ = refl

-- executable check: the exact step count is 34
private
  test-step-skip :
    exec 100 STEP (embM ((atm t-skip ∙ nil) ∙ nil) nil (nil ∷ []))
    ≡ just (embM nil ((atm t-skip ∙ nil) ∙ nil) (nil ∷ []) , 34)
  test-step-skip = refl

------------------------------------------------------------------------
-- Case 2: `c ; d`.  The machine step pushes ⌜c⌝ ⌜d⌝ (seqE) on the todo
-- stack and the (seqB . nil) record on the done stack.

step-seq : ∀ cc dc cd dn σ
  → Run STEP (embM ((atm t-seq ∙ (cc ∙ dc)) ∙ cd) dn σ)
             (embM (cc ∙ (dc ∙ ((atm t-seqE ∙ nil) ∙ cd))) ((atm t-seqB ∙ nil) ∙ dn) σ)
             80
step-seq cc dc cd dn σ =
  rSeq (prologue t-seq (cc ∙ dc) cd dn (encS σ))
    (rSeq (rElse refl (rElse refl (rThen refl body refl) refl) refl)
          (epilogue t-seqB nil (cc ∙ (dc ∙ ((atm t-seqE ∙ nil) ∙ cd))) dn (encS σ)))
  where
    body : Run stepSeq _ _ 45
    body =
      rSeq (rAss refl refl)
       (rSeq (rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl))
        (rSeq (rAss refl refl)
         (rSeq (rAss refl refl)
          (rSeq (rAss refl (rupd-self (cc ∙ dc)))
           (rSeq (rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl))
            (rSeq (rAss refl refl)
             (rSeq (rAss refl (rupd-self cc))
              (rSeq (rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl))
                    (rSeq (rAss refl (rupd-self (atm t-seq))) (rAss refl refl))))))))))

step-seq-agrees : ∀ cc dc cd dn σ
  → astep ⟨ (atm t-seq ∙ (cc ∙ dc)) ∙ cd , dn , σ ⟩
  ≡ just ⟨ cc ∙ (dc ∙ ((atm t-seqE ∙ nil) ∙ cd)) , (atm t-seqB ∙ nil) ∙ dn , σ ⟩
step-seq-agrees cc dc cd dn σ = refl

------------------------------------------------------------------------
-- Case 3: the `seqE` marker.  Reassembles ⌜c ; d⌝ on the done stack.

step-seqE : ∀ cc dc cd dn σ
  → Run STEP (embM ((atm t-seqE ∙ nil) ∙ cd) (dc ∙ (cc ∙ ((atm t-seqB ∙ nil) ∙ dn))) σ)
             (embM cd ((atm t-seq ∙ (cc ∙ dc)) ∙ dn) σ)
             81
step-seqE cc dc cd dn σ =
  rSeq (prologue t-seqE nil cd (dc ∙ (cc ∙ ((atm t-seqB ∙ nil) ∙ dn))) (encS σ))
    (rSeq (rElse refl (rElse refl (rElse refl (rThen refl body refl) refl) refl) refl)
          (epilogue t-seq (cc ∙ dc) cd dn (encS σ)))
  where
    body : Run stepSeqE _ _ 45
    body =
      rSeq (rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl))
       (rSeq (rAss refl refl)
        (rSeq (rAss refl (rupd-self dc))
         (rSeq (rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl))
          (rSeq (rAss refl refl)
           (rSeq (rAss refl (rupd-self cc))
            (rSeq (rAss refl (rupd-self dc))
             (rSeq (rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl))
              (rSeq (rAss refl (rupd-self (atm t-seqB ∙ nil)))
                    (rSeq (rAss refl (rupd-self (atm t-seqE))) (rAss refl refl))))))))))

step-seqE-agrees : ∀ cc dc cd dn σ
  → astep ⟨ (atm t-seqE ∙ nil) ∙ cd , dc ∙ (cc ∙ ((atm t-seqB ∙ nil) ∙ dn)) , σ ⟩
  ≡ just ⟨ cd , (atm t-seq ∙ (cc ∙ dc)) ∙ dn , σ ⟩
step-seqE-agrees cc dc cd dn σ = refl

private
  test-step-seq :
    exec 200 STEP (embM ((atm t-seq ∙ (atm 1 ∙ atm 2)) ∙ nil) nil (nil ∷ []))
    ≡ just (embM (atm 1 ∙ (atm 2 ∙ ((atm t-seqE ∙ nil) ∙ nil))) ((atm t-seqB ∙ nil) ∙ nil)
                 (nil ∷ []) , 80)
  test-step-seq = refl

  test-step-seqE :
    exec 200 STEP (embM ((atm t-seqE ∙ nil) ∙ nil)
                        (atm 2 ∙ (atm 1 ∙ ((atm t-seqB ∙ nil) ∙ nil))) (nil ∷ []))
    ≡ just (embM nil ((atm t-seq ∙ (atm 1 ∙ atm 2)) ∙ nil) (nil ∷ []) , 81)
  test-step-seqE = refl


------------------------------------------------------------------------
-- Cases 4-6: the loop protocol's markers (pure stack surgery).

step-lpB : ∀ ec Dc Lc fc cd dn σ
  → Run STEP (embM ((atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   ((atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             (embM (Lc ∙ ((atm t-lpC ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd))
                   ((atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             84
step-lpB ec Dc Lc fc cd dn σ =
  prologue t-lpB A cd ((atm t-lpD ∙ A) ∙ dn) (encS σ)
  » disp
  » epilogue t-lpB A (Lc ∙ ((atm t-lpC ∙ A) ∙ cd)) dn (encS σ)
  where
    A : V
    A = ec ∙ (Dc ∙ (Lc ∙ fc))
    body : Run stepLpB _ _ 43
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-lpD ∙ A))
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (Lc ∙ fc))
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ fc)))
    disp : Run DISPATCH _ _ 52
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl) refl

step-lpB-agrees : ∀ ec Dc Lc fc cd dn σ
  → astep ⟨ (atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
          , (atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn , σ ⟩
  ≡ just ⟨ Lc ∙ ((atm t-lpC ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
         , (atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn , σ ⟩
step-lpB-agrees ec Dc Lc fc cd dn σ = refl

step-lpZ : ∀ ec Dc Lc fc cd dn σ
  → Run STEP (embM ((atm t-lpZ ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   ((atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             (embM cd ((atm t-loop ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             57
step-lpZ ec Dc Lc fc cd dn σ =
  prologue t-lpZ A cd ((atm t-lpD ∙ A) ∙ dn) (encS σ)
  » disp
  » epilogue t-loop A cd dn (encS σ)
  where
    A : V
    A = ec ∙ (Dc ∙ (Lc ∙ fc))
    body : Run stepLpZ _ _ 15
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-lpD ∙ A))
      » rAss refl (rupd-self (atm t-lpZ))
      » rAss refl refl
    disp : Run DISPATCH _ _ 25
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl

step-lpZ-agrees : ∀ ec Dc Lc fc cd dn σ
  → astep ⟨ (atm t-lpZ ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
          , (atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn , σ ⟩
  ≡ just ⟨ cd , (atm t-loop ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn , σ ⟩
step-lpZ-agrees ec Dc Lc fc cd dn σ = refl

step-lpC : ∀ ec Dc Lc fc cd dn σ
  → Run STEP (embM ((atm t-lpC ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   (Lc ∙ ((atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn)) σ)
             (embM ((atm t-lpA ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   ((atm t-lpC ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             86
step-lpC ec Dc Lc fc cd dn σ =
  prologue t-lpC A cd (Lc ∙ ((atm t-lpB ∙ A) ∙ dn)) (encS σ)
  » disp
  » epilogue t-lpC A ((atm t-lpA ∙ A) ∙ cd) dn (encS σ)
  where
    A : V
    A = ec ∙ (Dc ∙ (Lc ∙ fc))
    body : Run stepLpC _ _ 43
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl refl
      » rAss refl (rupd-self Lc)
      » rAss refl (rupd-self (Lc ∙ fc))
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ fc)))
      » rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-lpB ∙ A))
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
    disp : Run DISPATCH _ _ 54
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl) refl

step-lpC-agrees : ∀ ec Dc Lc fc cd dn σ
  → astep ⟨ (atm t-lpC ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
          , Lc ∙ ((atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) , σ ⟩
  ≡ just ⟨ (atm t-lpA ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
         , (atm t-lpC ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn , σ ⟩
step-lpC-agrees ec Dc Lc fc cd dn σ = refl

------------------------------------------------------------------------
-- Case 7: `from e do D loop L until f` (entry).

step-loop : ∀ ec Dc Lc fc cd dn σ
  → Run STEP (embM ((atm t-loop ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd) dn σ)
             (embM ((atm t-lpA ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   ((atm t-loopB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             54
step-loop ec Dc Lc fc cd dn σ =
  prologue t-loop A cd dn (encS σ)
  » disp
  » epilogue t-loopB A ((atm t-lpA ∙ A) ∙ cd) dn (encS σ)
  where
    A : V
    A = ec ∙ (Dc ∙ (Lc ∙ fc))
    body : Run stepLoop _ _ 15
    body =
        rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » (rAss refl (rupd-self (atm t-loop)) » rAss refl refl)
    disp : Run DISPATCH _ _ 22
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl

step-loop-agrees : ∀ ec Dc Lc fc cd dn σ
  → astep ⟨ (atm t-loop ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd , dn , σ ⟩
  ≡ just ⟨ (atm t-lpA ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
         , (atm t-loopB ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn , σ ⟩
step-loop-agrees ec Dc Lc fc cd dn σ = refl

private
  test-step-lpZ :
    exec 300 STEP (embM ((atm t-lpZ ∙ (nil ∙ (nil ∙ (nil ∙ nil)))) ∙ nil)
                        ((atm t-lpD ∙ (nil ∙ (nil ∙ (nil ∙ nil)))) ∙ nil) (nil ∷ []))
    ≡ just (embM nil ((atm t-loop ∙ (nil ∙ (nil ∙ (nil ∙ nil)))) ∙ nil) (nil ∷ []) , 57)
  test-step-lpZ = refl

  test-step-loop :
    exec 300 STEP (embM ((atm t-loop ∙ (atm 1 ∙ (atm 2 ∙ (atm 3 ∙ atm 4)))) ∙ nil) nil
                        (nil ∷ []))
    ≡ just (embM ((atm t-lpA ∙ (atm 1 ∙ (atm 2 ∙ (atm 3 ∙ atm 4)))) ∙ nil)
                 ((atm t-loopB ∙ (atm 1 ∙ (atm 2 ∙ (atm 3 ∙ atm 4)))) ∙ nil) (nil ∷ []) , 54)
  test-step-loop = refl

------------------------------------------------------------------------
-- Case 8: `if e then C else D fi f` (entry).  The test is evaluated by
-- `evalC`; its truth is canonicalised into the (condE . b) marker so that
-- the `condE` case can later check the exit assertion against it.  The
-- branch itself is taken on the RAW test value, whose truth is the
-- hypothesis -- so the interpreter's conditional mirrors the object's.

private
  stp : ℕ → ℕ → ℕ
  stp a b = suc (a + b)

  canon : ∀ v → eqV (boolV (eqV v nil)) nil ≡ isTrue v
  canon nil     = refl
  canon (atm _) = refl
  canon (_ ∙ _) = refl

condBody : ℕ → ℕ
condBody M =
  stp 1 (stp (evalB M) (stp 1 (stp 1 (stp 1 (stp 9 (stp 1 (stp 6 (stp 9
  (stp 1 (stp 1 (stp 1 (stp (evalB M) (stp 1 3)))))))))))))

condStep : ℕ → ℕ
condStep M = stp 15 (stp (5 + condBody M) 15)

step-cond-t : ∀ (σ : Store) (e : Exp) (v : V) → evalE σ e ≡ just v → isTrue v ≡ true
  → vmaxᵉ e ≤ length σ
  → ∀ cc dc fc cd dn
  → Run STEP (embM ((atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd) dn σ)
             (embM (cc ∙ ((atm t-condE ∙ boolV (eqV (boolV (eqV v nil)) nil)) ∙ cd))
                   ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn) σ)
             (condStep (length σ))
step-cond-t σ e v ev tv lt cc dc fc cd dn =
  prologue t-cond A cd dn (encS σ)
  » disp
  » epilogue t-condB A (cc ∙ ((atm t-condE ∙ boolV (eqV (boolV (eqV v nil)) nil)) ∙ cd))
             dn (encS σ)
  where
    A : V
    A = ⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc))
    inner : Run (cond (opd (var iVv)) (iA1 ^= hdE (var iKk))
                      ((iEl ^= tlE (var iKk)) ⨾ (iA1 ^= hdE (var iEl))
                       ⨾ (iEl ^= tlE (var iKk)))
                      (opd (var iVv))) _ _ 6
    inner = rWeak (s≤s (s≤s z≤n))
                  (rThen (cong just tv) (rAss refl refl) (cong just tv))
    body : Run stepCond _ _ (condBody (length σ))
    body =
        rAss refl refl
      » eval-run σ e lt v nil v ev refl _ _ _ _ _
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » inner
      » rOf (push-gen _ iT1 iA1 iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (cc ∙ (dc ∙ fc)))
      » rAss refl (rupd-self (boolV (eqV (boolV (eqV v nil)) nil)))
      » rAss refl (rupd-self (boolV (eqV v nil)))
      » eval-run σ e lt v v nil ev (rupd-self v) _ _ _ _ _
      » rAss refl (rupd-self ⌜ e ⌝ᵉ)
      » (rAss refl (rupd-self (atm t-cond)) » rAss refl refl)
    disp : Run DISPATCH _ _ (5 + condBody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl

-- the same, stated with the canonical boolean the machine records
step-cond-true : ∀ (σ : Store) (e : Exp) (v : V) → evalE σ e ≡ just v → isTrue v ≡ true
  → vmaxᵉ e ≤ length σ
  → ∀ cc dc fc cd dn
  → Run STEP (embM ((atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd) dn σ)
             (embM (cc ∙ ((atm t-condE ∙ boolV (isTrue v)) ∙ cd))
                   ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn) σ)
             (condStep (length σ))
step-cond-true σ e v ev tv lt cc dc fc cd dn =
  subst (λ b → Run STEP _ (embM (cc ∙ ((atm t-condE ∙ boolV b) ∙ cd)) _ _) _)
        (canon v) (step-cond-t σ e v ev tv lt cc dc fc cd dn)

step-cond-true-agrees : ∀ (σ : Store) (e : Exp) (v : V) → evalE σ e ≡ just v → isTrue v ≡ true
  → ∀ cc dc fc cd dn
  → astep ⟨ (atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd , dn , σ ⟩
  ≡ just ⟨ cc ∙ ((atm t-condE ∙ boolV true) ∙ cd)
         , (atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn , σ ⟩
step-cond-true-agrees σ e v ev tv cc dc fc cd dn
  rewrite RWhileSIMach.evalEV-ok σ e | ev | tv = refl

-- the FALSE branch (the test evaluates to nil)
step-cond-f : ∀ (σ : Store) (e : Exp) → evalE σ e ≡ just nil → vmaxᵉ e ≤ length σ
  → ∀ cc dc fc cd dn
  → Run STEP (embM ((atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd) dn σ)
             (embM (dc ∙ ((atm t-condE ∙ nil) ∙ cd))
                   ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn) σ)
             (condStep (length σ))
step-cond-f σ e ev lt cc dc fc cd dn =
  prologue t-cond A cd dn (encS σ)
  » disp
  » epilogue t-condB A (dc ∙ ((atm t-condE ∙ nil) ∙ cd)) dn (encS σ)
  where
    A : V
    A = ⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc))
    inner : Run (cond (opd (var iVv)) (iA1 ^= hdE (var iKk))
                      ((iEl ^= tlE (var iKk)) ⨾ (iA1 ^= hdE (var iEl))
                       ⨾ (iEl ^= tlE (var iKk)))
                      (opd (var iVv))) _ _ 6
    inner = rElse refl (rAss refl refl » rAss refl refl
                        » rAss refl (rupd-self (dc ∙ fc))) refl
    body : Run stepCond _ _ (condBody (length σ))
    body =
        rAss refl refl
      » eval-run σ e lt nil nil nil ev refl _ _ _ _ _
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » inner
      » rOf (push-gen _ iT1 iA1 iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (cc ∙ (dc ∙ fc)))
      » rAss refl refl
      » rAss refl (rupd-self (nil ∙ nil))
      » eval-run σ e lt nil nil nil ev refl _ _ _ _ _
      » rAss refl (rupd-self ⌜ e ⌝ᵉ)
      » (rAss refl (rupd-self (atm t-cond)) » rAss refl refl)
    disp : Run DISPATCH _ _ (5 + condBody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl

step-cond-f-agrees : ∀ (σ : Store) (e : Exp) → evalE σ e ≡ just nil
  → ∀ cc dc fc cd dn
  → astep ⟨ (atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd , dn , σ ⟩
  ≡ just ⟨ dc ∙ ((atm t-condE ∙ nil) ∙ cd)
         , (atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn , σ ⟩
step-cond-f-agrees σ e ev cc dc fc cd dn
  rewrite RWhileSIMach.evalEV-ok σ e | ev = refl

------------------------------------------------------------------------
-- Case 9: the `condE` marker.  Checks the exit assertion and reassembles
-- ⌜if e then C else D fi f⌝ on the done stack.

private
  assert-clear-t : ∀ v → isTrue v ≡ true
                 → rupd (nil ∙ nil) (boolV (eqV (boolV (eqV v nil)) nil)) ≡ just nil
  assert-clear-t v tv rewrite canon v | tv = refl

  assert-clear-f : ∀ v → isTrue v ≡ false
                 → rupd nil (boolV (eqV (boolV (eqV v nil)) nil)) ≡ just nil
  assert-clear-f v tv rewrite canon v | tv = refl

condEBody : ℕ → ℕ
condEBody M =
  stp 9 (stp 1 (stp 1 (stp 1 (stp 6 (stp 1 (stp 1 (stp 9 (stp 1
  (stp 1 (stp 1 (stp 1 (stp 1 (stp 1 (stp (evalB M) (stp 1 (stp 1 (stp 1
  (stp (evalB M) (stp 1 (stp 1 (stp 1 (stp 1 (stp 1 (stp 1 (stp 1 3)))))))))))))))))))))))))

condEStep : ℕ → ℕ
condEStep M = stp 15 (stp (6 + condEBody M) 15)

step-condE-t : ∀ (σ : Store) (f : Exp) (v : V) → evalE σ f ≡ just v → isTrue v ≡ true
  → vmaxᵉ f ≤ length σ
  → ∀ ec cc dc cd dn
  → Run STEP (embM ((atm t-condE ∙ (nil ∙ nil)) ∙ cd)
                   (cc ∙ ((atm t-condB ∙ (ec ∙ (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))) ∙ dn)) σ)
             (embM cd ((atm t-cond ∙ (ec ∙ (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))) ∙ dn) σ)
             (condEStep (length σ))
step-condE-t σ f v ev tv lt ec cc dc cd dn =
  prologue t-condE (nil ∙ nil) cd (cc ∙ ((atm t-condB ∙ A) ∙ dn)) (encS σ)
  » disp
  » epilogue t-cond A cd dn (encS σ)
  where
    A : V
    A = ec ∙ (cc ∙ (dc ∙ ⌜ f ⌝ᵉ))
    inner : Run (cond (opd (var iAg)) (iHd ^= hdE (var iKk))
                      ((iEl ^= tlE (var iKk)) ⨾ (iHd ^= hdE (var iEl))
                       ⨾ (iEl ^= tlE (var iKk)))
                      (opd (var iAg))) _ _ 6
    inner = rWeak (s≤s (s≤s z≤n)) (rThen refl (rAss refl (rupd-self cc)) refl)
    body : Run stepCondE _ _ (condEBody (length σ))
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » inner
      » rAss refl (rupd-self (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))
      » rAss refl (rupd-self (atm t-condB ∙ A))
      » rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-condB ∙ A))
      » rAss refl refl » rAss refl refl » rAss refl refl
      » rAss refl (rupd-self (dc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))
      » eval-run σ f lt v nil v ev refl _ _ _ _ _
      » rAss refl refl
      » rAss refl (assert-clear-t v tv)
      » rAss refl (rupd-self (boolV (eqV v nil)))
      » eval-run σ f lt v v nil ev (rupd-self v) _ _ _ _ _
      » rAss refl refl » rAss refl refl
      » rAss refl (rupd-self ⌜ f ⌝ᵉ)
      » rAss refl (rupd-self (dc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))
      » rAss refl refl
      » rAss refl (rupd-self A)
      » (rAss refl (rupd-self (atm t-condE)) » rAss refl refl)
    disp : Run DISPATCH _ _ (6 + condEBody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl

------------------------------------------------------------------------
-- Case 10: the `lpA` marker -- the loop's entry test.

lpABody : ℕ → ℕ
lpABody M =
  stp 1 (stp (evalB M) (stp 12 (stp (evalB M) (stp 1 (stp 1 (stp 9 (stp 1
  (stp 1 (stp 9 1)))))))))

lpAStep : ℕ → ℕ
lpAStep M = stp 15 (stp (8 + lpABody M) 15)

step-lpA-t : ∀ (σ : Store) (e : Exp) (v : V) → evalE σ e ≡ just v → isTrue v ≡ true
  → vmaxᵉ e ≤ length σ
  → ∀ Dc Lc fc cd dn
  → Run STEP (embM ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   ((atm t-loopB ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             (embM (Dc ∙ ((atm t-lpD ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd))
                   ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             (lpAStep (length σ))
step-lpA-t σ e v ev tv lt Dc Lc fc cd dn =
  prologue t-lpA A cd ((atm t-loopB ∙ A) ∙ dn) (encS σ)
  » disp
  » epilogue t-lpA A (Dc ∙ ((atm t-lpD ∙ A) ∙ cd)) dn (encS σ)
  where
    A : V
    A = ⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc))
    inner : Run (cond (opd (var iVv))
                      (pop iT1 iHd iDn ⨾ (iHd ^= cns (cst (atm t-loopB)) (var iAg)))
                      (pop iT1 iHd iDn ⨾ (iHd ^= cns (cst (atm t-lpC)) (var iAg)))
                      (opd (var iVv))) _ _ 12
    inner = rThen (cong just tv)
                  (rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
                   » rAss refl (rupd-self (atm t-loopB ∙ A)))
                  (cong just tv)
    body : Run stepLpA _ _ (lpABody (length σ))
    body =
        rAss refl refl
      » eval-run σ e lt v nil v ev refl _ _ _ _ _
      » inner
      » eval-run σ e lt v v nil ev (rupd-self v) _ _ _ _ _
      » rAss refl (rupd-self ⌜ e ⌝ᵉ)
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ fc)))
    disp : Run DISPATCH _ _ (8 + lpABody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl

step-lpA-f : ∀ (σ : Store) (e : Exp) → evalE σ e ≡ just nil → vmaxᵉ e ≤ length σ
  → ∀ Dc Lc fc cd dn
  → Run STEP (embM ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                   ((atm t-lpC ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             (embM (Dc ∙ ((atm t-lpD ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd))
                   ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc)))) ∙ dn) σ)
             (lpAStep (length σ))
step-lpA-f σ e ev lt Dc Lc fc cd dn =
  prologue t-lpA A cd ((atm t-lpC ∙ A) ∙ dn) (encS σ)
  » disp
  » epilogue t-lpA A (Dc ∙ ((atm t-lpD ∙ A) ∙ cd)) dn (encS σ)
  where
    A : V
    A = ⌜ e ⌝ᵉ ∙ (Dc ∙ (Lc ∙ fc))
    inner : Run (cond (opd (var iVv))
                      (pop iT1 iHd iDn ⨾ (iHd ^= cns (cst (atm t-loopB)) (var iAg)))
                      (pop iT1 iHd iDn ⨾ (iHd ^= cns (cst (atm t-lpC)) (var iAg)))
                      (opd (var iVv))) _ _ 12
    inner = rElse refl
                  (rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
                   » rAss refl (rupd-self (atm t-lpC ∙ A)))
                  refl
    body : Run stepLpA _ _ (lpABody (length σ))
    body =
        rAss refl refl
      » eval-run σ e lt nil nil nil ev refl _ _ _ _ _
      » inner
      » eval-run σ e lt nil nil nil ev refl _ _ _ _ _
      » rAss refl (rupd-self ⌜ e ⌝ᵉ)
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl refl
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ fc)))
    disp : Run DISPATCH _ _ (8 + lpABody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl

------------------------------------------------------------------------
-- Case 11: the `lpD` marker -- D has run, test the exit condition.

lpDBody : ℕ → ℕ
lpDBody M = foldr stp 1
  (9 ∷ 1 ∷ 1 ∷ 1 ∷ 9 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ evalB M ∷ 2 ∷ 9 ∷ evalB M
   ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])

lpDStep : ℕ → ℕ
lpDStep M = stp 15 (stp (12 + lpDBody M) 15)

step-lpD-t : ∀ (σ : Store) (f : Exp) (v : V) → evalE σ f ≡ just v → isTrue v ≡ true
  → vmaxᵉ f ≤ length σ
  → ∀ ec Dc Lc cd dn
  → Run STEP (embM ((atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
                   (Dc ∙ ((atm t-lpA ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ dn)) σ)
             (embM ((atm t-lpZ ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
                   ((atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ dn) σ)
             (lpDStep (length σ))
step-lpD-t σ f v ev tv lt ec Dc Lc cd dn =
  prologue t-lpD A cd (Dc ∙ ((atm t-lpA ∙ A) ∙ dn)) (encS σ)
  » disp
  » epilogue t-lpD A ((atm t-lpZ ∙ A) ∙ cd) dn (encS σ)
  where
    A : V
    A = ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ))
    inner : Run (cond (opd (var iVv))
                      (iHd ^= cns (cst (atm t-lpZ)) (var iAg))
                      (iHd ^= cns (cst (atm t-lpB)) (var iAg))
                      (opd (var iVv))) _ _ 2
    inner = rThen (cong just tv) (rAss refl refl) (cong just tv)
    body : Run stepLpD _ _ (lpDBody (length σ))
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl (rupd-self Dc)
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))
      » rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-lpA ∙ A))
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » rAss refl (rupd-self (Lc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))
      » eval-run σ f lt v nil v ev refl _ _ _ _ _
      » inner
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » eval-run σ f lt v v nil ev (rupd-self v) _ _ _ _ _
      » rAss refl refl
      » rAss refl refl
      » rAss refl (rupd-self ⌜ f ⌝ᵉ)
      » rAss refl (rupd-self (Lc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))
    disp : Run DISPATCH _ _ (12 + lpDBody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl

step-lpD-f : ∀ (σ : Store) (f : Exp) → evalE σ f ≡ just nil → vmaxᵉ f ≤ length σ
  → ∀ ec Dc Lc cd dn
  → Run STEP (embM ((atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
                   (Dc ∙ ((atm t-lpA ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ dn)) σ)
             (embM ((atm t-lpB ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
                   ((atm t-lpD ∙ (ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))) ∙ dn) σ)
             (lpDStep (length σ))
step-lpD-f σ f ev lt ec Dc Lc cd dn =
  prologue t-lpD A cd (Dc ∙ ((atm t-lpA ∙ A) ∙ dn)) (encS σ)
  » disp
  » epilogue t-lpD A ((atm t-lpB ∙ A) ∙ cd) dn (encS σ)
  where
    A : V
    A = ec ∙ (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ))
    inner : Run (cond (opd (var iVv))
                      (iHd ^= cns (cst (atm t-lpZ)) (var iAg))
                      (iHd ^= cns (cst (atm t-lpB)) (var iAg))
                      (opd (var iVv))) _ _ 2
    inner = rElse refl (rAss refl refl) refl
    body : Run stepLpD _ _ (lpDBody (length σ))
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl (rupd-self Dc)
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))
      » rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-lpA ∙ A))
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » rAss refl (rupd-self (Lc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))
      » eval-run σ f lt nil nil nil ev refl _ _ _ _ _
      » inner
      » rOf (push-gen _ iT1 iHd iCd _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » eval-run σ f lt nil nil nil ev refl _ _ _ _ _
      » rAss refl refl
      » rAss refl refl
      » rAss refl (rupd-self ⌜ f ⌝ᵉ)
      » rAss refl (rupd-self (Lc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (Dc ∙ (Lc ∙ ⌜ f ⌝ᵉ)))
    disp : Run DISPATCH _ _ (12 + lpDBody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl

------------------------------------------------------------------------
-- Case 12: `x ^= e` -- the object language's reversible assignment.

assBody : ℕ → ℕ
assBody M = foldr stp 1 (1 ∷ evalB M ∷ 1 ∷ (M * 60 + 27) ∷ 1 ∷ evalB M ∷ [])

assStep : ℕ → ℕ
assStep M = stp 15 (stp (2 + assBody M) 15)

step-ass : ∀ (σ : Store) (x : ℕ) (e : Exp) (v u : V)
  → evalE σ e ≡ just v → rupd (get σ x) v ≡ just u
  → suc x ≤ length σ → vmaxᵉ e ≤ length σ → NotIn x e
  → ∀ cd dn
  → Run STEP (embM ((atm t-ass ∙ (num x ∙ ⌜ e ⌝ᵉ)) ∙ cd) dn σ)
             (embM cd ((atm t-ass ∙ (num x ∙ ⌜ e ⌝ᵉ)) ∙ dn) (set σ x u))
             (assStep (length σ))
step-ass σ x e v u ev ru lt lte ni cd dn =
  prologue t-ass (num x ∙ ⌜ e ⌝ᵉ) cd dn (encS σ)
  » disp
  » epilogue t-ass (num x ∙ ⌜ e ⌝ᵉ) cd dn (encS (set σ x u))
  where
    lenEq : length (set σ x u) ≡ length σ
    lenEq = length-set σ x u lt
    ev′ : evalE (set σ x u) e ≡ just v
    ev′ = trans (evalE-frame σ x u e ni) ev
    lte′ : vmaxᵉ e ≤ length (set σ x u)
    lte′ = subst (λ n → vmaxᵉ e ≤ n) (sym lenEq) lte
    back : Run evalC
             (emb (mkI cd dn (encS (set σ x u)) (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) nil ⌜ e ⌝ᵉ nil v
                       nil nil nil nil nil nil nil nil nil nil))
             (emb (mkI cd dn (encS (set σ x u)) (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) nil ⌜ e ⌝ᵉ nil nil
                       nil nil nil nil nil nil nil nil nil nil))
             (evalB (length σ))
    back = subst (λ n → Run evalC
                          (emb (mkI cd dn (encS (set σ x u)) (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) nil
                                    ⌜ e ⌝ᵉ nil v nil nil nil nil nil nil nil nil nil nil))
                          (emb (mkI cd dn (encS (set σ x u)) (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) nil
                                    ⌜ e ⌝ᵉ nil nil nil nil nil nil nil nil nil nil nil nil))
                          (evalB n))
                 lenEq
                 (eval-run (set σ x u) e lte′ v v nil ev′ (rupd-self v)
                           cd dn (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) nil)
    body : Run stepAss _ _ (assBody (length σ))
    body =
        rAss refl refl
      » eval-run σ e lte v nil v ev refl cd dn (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) nil
      » rAss refl refl
      » upd-run-gen σ x v u lt ru cd dn (atm t-ass) (num x ∙ ⌜ e ⌝ᵉ) ⌜ e ⌝ᵉ nil nil
                    nil nil nil nil nil
      » rAss refl (rupd-self (num x))
      » back
      » rAss refl (rupd-self ⌜ e ⌝ᵉ)
    disp : Run DISPATCH _ _ (2 + assBody (length σ))
    disp = rElse refl (rThen refl body refl) refl

step-ass-agrees : ∀ (σ : Store) (x : ℕ) (e : Exp) (v u : V)
  → evalE σ e ≡ just v → rupd (get σ x) v ≡ just u
  → ∀ cd dn
  → astep ⟨ (atm t-ass ∙ (num x ∙ ⌜ e ⌝ᵉ)) ∙ cd , dn , σ ⟩
  ≡ just ⟨ cd , (atm t-ass ∙ (num x ∙ ⌜ e ⌝ᵉ)) ∙ dn , set σ x u ⟩
step-ass-agrees σ x e v u ev ru cd dn
  rewrite RWhileSIMach.unnum-num x | RWhileSIMach.evalEV-ok σ e | ev | ru = refl

-- the FALSE branch of `condE` (the else-branch ran; the exit assertion must fail)
step-condE-f : ∀ (σ : Store) (f : Exp) (v : V) → evalE σ f ≡ just v → isTrue v ≡ false
  → vmaxᵉ f ≤ length σ
  → ∀ ec cc dc cd dn
  → Run STEP (embM ((atm t-condE ∙ nil) ∙ cd)
                   (dc ∙ ((atm t-condB ∙ (ec ∙ (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))) ∙ dn)) σ)
             (embM cd ((atm t-cond ∙ (ec ∙ (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))) ∙ dn) σ)
             (condEStep (length σ))
step-condE-f σ f v ev tv lt ec cc dc cd dn =
  prologue t-condE nil cd (dc ∙ ((atm t-condB ∙ A) ∙ dn)) (encS σ)
  » disp
  » epilogue t-cond A cd dn (encS σ)
  where
    A : V
    A = ec ∙ (cc ∙ (dc ∙ ⌜ f ⌝ᵉ))
    inner : Run (cond (opd (var iAg)) (iHd ^= hdE (var iKk))
                      ((iEl ^= tlE (var iKk)) ⨾ (iHd ^= hdE (var iEl))
                       ⨾ (iEl ^= tlE (var iKk)))
                      (opd (var iAg))) _ _ 6
    inner = rElse refl (rAss refl refl » rAss refl (rupd-self dc)
                        » rAss refl (rupd-self (dc ∙ ⌜ f ⌝ᵉ))) refl
    body : Run stepCondE _ _ (condEBody (length σ))
    body =
        rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl refl
      » rAss refl refl
      » rAss refl refl
      » inner
      » rAss refl (rupd-self (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))
      » rAss refl (rupd-self (atm t-condB ∙ A))
      » rOf (pop-gen _ iT1 iHd iDn _ _ (λ ()) (λ ()) (λ ()) refl refl refl)
      » rAss refl (rupd-self (atm t-condB ∙ A))
      » rAss refl refl » rAss refl refl » rAss refl refl
      » rAss refl (rupd-self (dc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))
      » eval-run σ f lt v nil v ev refl _ _ _ _ _
      » rAss refl refl
      » rAss refl (assert-clear-f v tv)
      » rAss refl (rupd-self (boolV (eqV v nil)))
      » eval-run σ f lt v v nil ev (rupd-self v) _ _ _ _ _
      » rAss refl refl » rAss refl refl
      » rAss refl (rupd-self ⌜ f ⌝ᵉ)
      » rAss refl (rupd-self (dc ∙ ⌜ f ⌝ᵉ))
      » rAss refl (rupd-self (cc ∙ (dc ∙ ⌜ f ⌝ᵉ)))
      » rAss refl refl
      » rAss refl (rupd-self A)
      » (rAss refl (rupd-self (atm t-condE)) » rAss refl refl)
    disp : Run DISPATCH _ _ (6 + condEBody (length σ))
    disp =
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rElse refl (
      rThen refl body refl)
      refl) refl) refl) refl) refl
