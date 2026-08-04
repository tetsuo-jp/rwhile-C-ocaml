{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Executable tests for the interpreter's building blocks (brick B5).
--
-- Every test below is checked by the TYPE CHECKER: `refl` forces Agda to run
-- the fuel-indexed evaluator `RWhileTime.exec` on a concrete interpreter
-- store and compare both the resulting store AND THE STEP COUNT with the
-- expected value.  So these are simultaneously
--
--   * regression tests for the macros (push/pop/walk/lookup/update), and
--   * a check of the cost formulas proved in RWhileSIWalk / RWhileSILookup
--     (`56k + 27` for a lookup of variable k, 9 for a push, ...).
--
-- They also exercise `exec`, which is otherwise only used through
-- `exec-sound`.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSITest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime
open import RWhileSIEnc using (num; encS)
open import RWhileSIMac
open import RWhileSIWalk
open import RWhileSILookup
open import RWhileSIEval
open import RWhileSIEnc using (⌜_⌝ᵉ)

private
  -- an object store of three variables: X0 = 'a, X1 = 'b, X2 = 'c
  σ₃ : Store
  σ₃ = atm 1 ∷ atm 2 ∷ atm 3 ∷ []

  -- the interpreter's store: only Vl, Kk (the index) and Cn are set
  ist : V → V → V → V → Store            -- vl, hd, vv, kk
  ist vl hd vv kk =
    emb (mkI nil nil vl nil nil nil nil hd vv kk (num 0) nil nil nil nil nil nil nil nil)

  ------------------------------------------------------------------------
  -- push / pop: 9 steps each, and pop undoes push.

  test-push : exec 20 (push iT1 iHd iCd) (ist (encS σ₃) (atm 9) nil (num 0))
            ≡ just (emb (mkI (atm 9 ∙ nil) nil (encS σ₃) nil nil nil nil nil nil
                             (num 0) (num 0) nil nil nil nil nil nil nil nil) , 9)
  test-push = refl

  test-pop : exec 20 (pop iT1 iHd iCd)
                     (emb (mkI (atm 9 ∙ nil) nil (encS σ₃) nil nil nil nil nil nil
                               (num 0) (num 0) nil nil nil nil nil nil nil nil))
           ≡ just (ist (encS σ₃) (atm 9) nil (num 0) , 9)
  test-pop = refl

  ------------------------------------------------------------------------
  -- the walk: two cells down and back, 28 steps per cell + 2.

  test-walk : exec 200 walk (ist (encS σ₃) nil nil (num 2))
            ≡ just (emb (mkI nil nil (encS (atm 3 ∷ [])) nil nil nil nil nil nil
                             (num 2) (num 2) (encS (atm 2 ∷ atm 1 ∷ [])) nil nil nil nil
                             nil nil nil)
                   , 58)
  test-walk = refl

  ------------------------------------------------------------------------
  -- LOOKUP: reading variable 1 yields 'b and costs 56·1 + 27 = 83,
  -- with the object store fully restored.

  test-lookup : exec 300 lkE (ist (encS σ₃) nil nil (num 1))
              ≡ just (ist (encS σ₃) nil (atm 2) (num 1) , 83)
  test-lookup = refl

  -- reading variable 0 costs 27
  test-lookup0 : exec 300 lkE (ist (encS σ₃) nil nil (num 0))
               ≡ just (ist (encS σ₃) nil (atm 1) (num 0) , 27)
  test-lookup0 = refl

  ------------------------------------------------------------------------
  -- UPDATE: the object-level reversible assignment.  Setting the (nil) cell
  -- X1 of [nil,nil,nil] to 'b, then doing it again CLEARS it -- the partial
  -- involution `rupdate` of src/EvalRwhile.ml, inherited by the interpreter.

  test-update : exec 300 updE (ist (encS (nil ∷ nil ∷ nil ∷ [])) nil (atm 2) (num 1))
              ≡ just (ist (encS (nil ∷ atm 2 ∷ nil ∷ [])) nil (atm 2) (num 1) , 83)
  test-update = refl

  test-update-clears : exec 300 updE (ist (encS (nil ∷ atm 2 ∷ nil ∷ [])) nil (atm 2) (num 1))
                     ≡ just (ist (encS (nil ∷ nil ∷ nil ∷ [])) nil (atm 2) (num 1) , 83)
  test-update-clears = refl

  ------------------------------------------------------------------------
  -- operand evaluation: a variable operand goes through the walk (60k + 36),
  -- a constant operand is read straight out of the code (6 steps).

  iste : V → V → Store                   -- El (the operand code), A1
  iste el a1 =
    emb (mkI nil nil (encS σ₃) nil nil nil nil nil nil nil (num 0) nil el nil a1 nil
             nil nil nil)

  test-opd-var : exec 300 (opdC iA1) (iste (atm 0 ∙ num 1) nil)
               ≡ just (iste (atm 0 ∙ num 1) (atm 2) , 92)
  test-opd-var = refl

  test-opd-cst : exec 300 (opdC iA1) (iste (atm 1 ∙ atm 7) nil)
               ≡ just (iste (atm 1 ∙ atm 7) (atm 7) , 6)
  test-opd-cst = refl

  -- running it twice clears the register again (the uncompute idiom)
  test-opd-invol : exec 300 (opdC iA1) (iste (atm 0 ∙ num 1) (atm 2))
                 ≡ just (iste (atm 0 ∙ num 1) nil , 92)
  test-opd-invol = refl

  ------------------------------------------------------------------------
  -- expression evaluation: `cons X1 '9` on the store ['a,'b,'c] yields
  -- ('b . '9).  Cost: two operand evaluations (96 for the variable, 6 for
  -- the constant) run twice (compute + uncompute) plus the dispatch.

  iste2 : V → V → Store                  -- T2 (the expression code), Vv
  iste2 t2 vv =
    emb (mkI nil nil (encS σ₃) nil nil nil t2 nil vv nil nil nil nil nil nil nil
             nil nil nil)

  test-eval-cns :
    exec 600 evalC (iste2 ⌜ cns (var 1) (cst (atm 9)) ⌝ᵉ nil)
    ≡ just (iste2 ⌜ cns (var 1) (cst (atm 9)) ⌝ᵉ (atm 2 ∙ atm 9) , 227)
  test-eval-cns = refl

  -- running it again clears the value register (the involution the `ass`
  -- case relies on)
  test-eval-invol :
    exec 600 evalC (iste2 ⌜ cns (var 1) (cst (atm 9)) ⌝ᵉ (atm 2 ∙ atm 9))
    ≡ just (iste2 ⌜ cns (var 1) (cst (atm 9)) ⌝ᵉ nil , 227)
  test-eval-invol = refl

  ------------------------------------------------------------------------
  -- pair? (the cons test): TRUE on a constant cons operand (no store walk),
  -- FALSE on the atom in X1.  Running it twice clears the register again.

  test-eval-pair-t :
    exec 600 evalC (iste2 ⌜ prE (cst (nil ∙ nil)) ⌝ᵉ nil)
    ≡ just (iste2 ⌜ prE (cst (nil ∙ nil)) ⌝ᵉ (nil ∙ nil) , 59)
  test-eval-pair-t = refl

  test-eval-pair-f :
    exec 600 evalC (iste2 ⌜ prE (var 1) ⌝ᵉ nil)
    ≡ just (iste2 ⌜ prE (var 1) ⌝ᵉ nil , 231)
  test-eval-pair-f = refl
