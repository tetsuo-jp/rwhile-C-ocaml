{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- C3: the Futamura hierarchy over a universe whose specialiser REALLY
-- RESIDUALISES — the partial-run refinement of RWhileFutamura3.Contract
-- with H1 PROVEN (not assumed) for object programs.
--
-- RWhileFutamura3.Contract derives fp2/fp3 from spec_av's basic equation
-- taken as a hypothesis, with a total `run`.  Here the hypothesis is
-- DISCHARGED for the wire programs of the static-control fragment: the
-- universe U contains
--
--   val v      R-WHILE values (data)
--   wp p       object programs (the wire AST of RWhileSpecAVWireCom)
--   code c     residuals (straight-line Code over one dynamic input)
--   papp p s   a specialised closure (partial application)
--   specP      THE SPECIALISER, as a program
--
-- and the fuel-indexed `run` sends
--
--   run (wp p)   (val v)                    ↦ evalProg p v      (C1)
--   run (code c) (val d)                    ↦ ⟦ c ⟧c d
--   run specP (pair (wp p) (tagS (val s)))  ↦ code (specProg p s)   ★
--   run specP (pair p (tagS s))             ↦ papp p s (otherwise)
--   run (papp p s) d                        ↦ run p (pair s d)
--
-- ★ is the point: specialising an OBJECT PROGRAM invokes the verified
-- residualising specialiser of RWhileSpecCom (C2), so fp1 for wire
-- programs is the PROVEN spec-contract, with genuine Futamura gain (the
-- witness below compiles swap to (cons cVar 'vtrue) — no interpretation
-- left).  Self-application (p not a wire program, e.g. specP itself)
-- resolves by the closure constructor, exactly RWhileFutamura2Inst's
-- `papp`/`mkpapp` realisation — honest scope: representing specProg
-- ITSELF as a wire program and specialising that is the remaining
-- research item (the OCaml artifact's fp2/fp3 tests exercise it on the
-- real spec_av).  Given that, the whole hierarchy holds here with
-- every step either DEFINITIONAL (refl) or discharged by spec-contract:
--
--   fp3-run : specProg k q s ≡ just cr → evalProg n q (s·d) ≡ just w →
--     run specP ⟨specP , 'S specP⟩   ⇓ comp3   (refl)
--     run comp3 ('S (wp q))          ⇓ comp2   (refl: the cogen emits the compiler)
--     run comp2 ('S (val s))         ⇓ code cr (computation + the fragment's commit)
--     run (code cr) (val d)          ⇓ val w   (spec-contract = C2's theorem)
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileSpecProg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)
open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; Code; cVar; cVal; cCons; ⟦_⟧c)
open import RWhileSpecAVWireCom using (Prog; prog; Com; cSeq; cRep; Pat; pVar; pCons)
open import RWhileWireSem using (evalProg)
open import RWhileSpecCom using (specProg; spec-contract; mapM)

------------------------------------------------------------------------
-- The universe and its fuel-indexed runner.

data U : Set where
  val   : Val → U          -- data
  wp    : Prog → U         -- object programs (wire AST)
  code  : Code → U         -- residual straight-line code
  pair  : U → U → U        -- ⟨ static , dynamic ⟩
  tagS  : U → U            -- the binding-time tag ('S . s)
  papp  : U → U → U        -- specialised closure
  specP : U                -- the specialiser, as a program

run : ℕ → U → U → Maybe U
run zero    _ _ = nothing
run (suc n) (wp p)   (val v) = mapM val (evalProg n p v)
run (suc n) (code c) (val d) = just (val (⟦ c ⟧c d))
run (suc n) specP (pair (wp p) (tagS (val s))) = mapM code (specProg n p s)
run (suc n) specP (pair p (tagS s)) = just (papp p s)
run (suc n) (papp p s) d = run n p (pair s d)
run (suc n) _ _ = nothing

------------------------------------------------------------------------
-- The three artefacts.  comp3 (the cogen) and comp2 (the compiler) are
-- concrete, inspectable values.

comp3 : U
comp3 = papp specP specP

comp2 : Prog → U
comp2 q = papp specP (wp q)

-- the cogen is produced by self-applying the specialiser (definitional):
comp3-def : run 1 specP (pair specP (tagS specP)) ≡ just comp3
comp3-def = refl

-- fp3 (cogen equation): the cogen maps ('S . interpreter) to the
-- compiler for that interpreter — for ANY object program q (refl).
fp3-cogen : ∀ q → run 2 comp3 (tagS (wp q)) ≡ just (comp2 q)
fp3-cogen q = refl

-- fp2 (compiler equation): the compiler maps ('S . source) to the REAL
-- residual of the verified specialiser (definitional, fuel-indexed).
fp2-compile : ∀ k q s →
  run (suc (suc k)) (comp2 q) (tagS (val s)) ≡ mapM code (specProg k q s)
fp2-compile k q s = refl

-- fp1 (target equation): the residual computes the source — C2's
-- spec-contract, lifted to the universe.
fp1-target : ∀ {k n} q s d {cr w} →
  specProg k q s ≡ just cr →
  evalProg n q (s · d) ≡ just w →
  run 1 (code cr) (val d) ≡ just (val w)
fp1-target q s d sp rt = cong (λ x → just (val x)) (spec-contract q s sp rt)

------------------------------------------------------------------------
-- HEADLINE: fp3, end to end.  For every object program q, static input
-- s and dynamic input d in the fragment: the cogen (built by self-
-- application) emits a compiler, the compiler emits the verified
-- residual, and the residual computes q's result on (s · d).

fp3-run : ∀ {k n} q s d {cr w} →
  specProg k q s ≡ just cr →                     -- the fragment commits
  evalProg n q (s · d) ≡ just w →                -- the source run succeeds
    (run 1 specP (pair specP (tagS specP)) ≡ just comp3)
  × (run 2 comp3 (tagS (wp q)) ≡ just (comp2 q))
  × (run (suc (suc k)) (comp2 q) (tagS (val s)) ≡ just (code cr))
  × (run 1 (code cr) (val d) ≡ just (val w))
fp3-run {k} q s d sp rt =
  refl , refl ,
  trans (fp2-compile k q s) (cong (mapM code) sp) ,
  fp1-target q s d sp rt

------------------------------------------------------------------------
-- Witness (test-first, all by refl): the swap program compiles through
-- the WHOLE hierarchy — cogen → compiler → residual → run — with the
-- static input vtrue baked into the residual (genuine Futamura gain).

module Witness where

  swapP : Prog
  swapP = prog 0 (cSeq (cRep (pCons (pVar 1) (pVar 2)) (pVar 0))
                       (cRep (pVar 0) (pCons (pVar 2) (pVar 1)))) 0

  -- cogen emits the compiler:
  _ : run 2 comp3 (tagS (wp swapP)) ≡ just (comp2 swapP)
  _ = refl

  -- the compiler emits the interpreter-free residual:
  _ : run 12 (comp2 swapP) (tagS (val vtrue)) ≡ just (code (cCons cVar (cVal vtrue)))
  _ = refl

  -- the residual computes swap's result, for every dynamic input:
  _ : ∀ d → run 1 (code (cCons cVar (cVal vtrue))) (val d) ≡ just (val (d · vtrue))
  _ = λ d → refl

  -- and it agrees with running the source program directly:
  _ : ∀ d → run 11 (wp swapP) (val (vtrue · d)) ≡ just (val (d · vtrue))
  _ = λ d → refl
