{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE VERIFIED INTERPRETER, ACTUALLY RUN -- inside the type checker.
--
-- Everything else about `SI` is proved; this module CHECKS it by running.
-- `RWhileTime.exec` is the fuel-indexed evaluator (sound AND complete, see
-- RWhileTimeExec), so each `refl` below is the type checker executing the
-- interpreter on an encoded object program and comparing both the final
-- state and the step count.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIExecTest where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime
open import RWhileSIEnc using (⌜_⌝; encS)
open import RWhileSIStep using (embM)
open import RWhileSISim using (SI)

private
  -- interpreting `skip` on the empty object store
  si-skip : exec 200 SI (embM (⌜ skip ⌝ ∙ nil) nil [])
          ≡ just (embM nil (⌜ skip ⌝ ∙ nil) [] , 37)
  si-skip = refl

  -- interpreting `X0 ^= 'a` on a one-cell store: the store really changes,
  -- and ⌜c⌝ is reassembled on the done stack
  ass : Cmd
  ass = 0 ^= opd (cst (atm 1))

  si-ass : exec 300 SI (embM (⌜ ass ⌝ ∙ nil) nil (nil ∷ []))
         ≡ just (embM nil (⌜ ass ⌝ ∙ nil) (atm 1 ∷ []) , 182)
  si-ass = refl

  -- ... and running the INVERSE object program undoes it, in the same
  -- number of steps (the machine-checked instance of si-uncompute)
  si-ass-inv : exec 300 SI (embM (⌜ ass ⌝ ∙ nil) nil (atm 1 ∷ []))
             ≡ just (embM nil (⌜ ass ⌝ ∙ nil) (nil ∷ []) , 182)
  si-ass-inv = refl

  -- a sequence: two assignments that cancel (reversibility, end to end)
  sq : Cmd
  sq = ass ⨾ ass

  si-seq : exec 400 SI (embM (⌜ sq ⌝ ∙ nil) nil (nil ∷ []))
         ≡ just (embM nil (⌜ sq ⌝ ∙ nil) (nil ∷ []) , 525)
  si-seq = refl

  -- the loop protocol, end to end: from (=? X0 nil) do skip loop X0 ^= '7
  -- until (=? X0 '7) turns [nil] into ['7] (object cost 4)
  lp : Cmd
  lp = loop (eqE (var 0) (cst nil)) skip (0 ^= opd (cst (atm 7)))
            (eqE (var 0) (cst (atm 7)))

  si-loop : exec 400 SI (embM (⌜ lp ⌝ ∙ nil) nil (nil ∷ []))
          ≡ just (embM nil (⌜ lp ⌝ ∙ nil) (atm 7 ∷ []) , 1869)
  si-loop = refl

  ------------------------------------------------------------------------
  -- Each run above is inside its proved bound `(CC M + 2) · k`:
  --
  --   skip        M=0 k=1     37 ≤ 3198
  --   X0 ^= 'a    M=1 k=1    182 ≤ 5942
  --   two of them M=1 k=3    525 ≤ 17826
  --   the loop    M=1 k=4   1869 ≤ 23768
  --
  -- The counts are 3 higher per loop iteration than the extracted text's
  -- (`./ri -steps`): the model charges 1 for the `skip` in the main loop's
  -- do-branch and 1 for the loop node, where R-WHILE's grammar prints an
  -- EMPTY branch, which costs nothing.  The model is the conservative side,
  -- so the proved bounds cover the implementation as well.
