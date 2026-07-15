{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- C1: BIG-STEP OPERATIONAL SEMANTICS for the wire-format AST (Pat / Com /
-- Prog of RWhileSpecAVWireCom) — the semantic half of the implementation
-- bridge, mirroring src/EvalRwhile.ml clause by clause:
--
--   evalC (cAss)   ~ evalCom CAss  + rupdate       (EvalRwhile.ml:434,190)
--   evalC (cRep)   ~ evalCom CRep  = evalPat then inv_evalPat (:438,393,402)
--   evalC (cCond)  ~ evalCom CCond (entry test, exit ASSERTION:
--                    true after then, false after else)       (:446-470)
--   evalC (cLoop)  ~ evalCom CLoop + evalLoop (entry must be true; each
--                    round: exit f? else loop-body, entry must be FALSE,
--                    do-body, repeat)                          (:471-483,551-574)
--   evalProg       ~ evalProgram (store all-nil, read slot i, run, write
--                    slot j, WHOLE STORE must be cleared)      (:576-596)
--
-- Modelling choices (shared with the rest of the development):
--   * The store is a slot-indexed cons list (slot n = vNth n ρ), matching
--     the wire encoding's variable indices (program2data renames variables
--     to their index, Program2DataRwhile.ml:131-137).
--   * Val is nil/cons only (atoms are opaque non-nil leaves in the
--     implementation; the model does not need them).
--   * hd/tl are TOTAL with nil default (RWhileAVSound), whereas the
--     implementation raises on hd/tl of nil: the model is the total
--     completion of the implementation's expression layer.  Command-level
--     partiality (reversible-update conflicts, pattern-match failures,
--     assertion failures, divergence) IS modelled, via Maybe + fuel.
--   * evalC/evalL consume one fuel per nesting/iteration, so termination
--     is structural and `--safe`; fuel-monotonicity is proved
--     (evalC-mono / evalL-mono / evalProg-mono), so `just` results are
--     fuel-independent.
--
-- The OCaml side mirrors this file as w_com/w_loop/w_prog in
-- src/TestSuite.ml (`wire-sem` test group): the SAME wire tree is run by
-- the production interpreter (data2program + evalProgram) and by the
-- model mirror, and the results must agree whenever the implementation
-- succeeds.  `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileWireSem where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileAVSound using (Val; ⟨⟩; _·_; hd; tl; vtrue; vfalse)
open import RWhileH2WorklistAV using (Ex; varN; exVal; exCons; exHd; exTl; exEq; exPairp; ⟦_⟧; vNth)
open import RWhileSpecAVWireCom using
  (Pat; pVar; pVal; pCons; Com; cSeq; cAss; cRep; cCond; cLoop; Prog; prog)

------------------------------------------------------------------------
-- Truth, structural equality, store update.

isT : Val → Bool                      -- is_true: non-nil is true
isT ⟨⟩      = false
isT (_ · _) = true

beq : Val → Val → Bool                -- structural equality (OCaml `=`)
beq ⟨⟩      ⟨⟩      = true
beq ⟨⟩      (_ · _) = false
beq (_ · _) ⟨⟩      = false
beq (a · b) (c · d) = beq a c ∧ beq b d

vSet : ℕ → Val → Val → Val            -- write slot n (extends a nil spine)
vSet zero    v ρ = v · tl ρ
vSet (suc n) v ρ = hd ρ · vSet n v (tl ρ)

-- rupdate (EvalRwhile.ml:190): reversible XOR update of a slot.
--   current nil → new value; new = current → nil; new nil → keep; else error.
updR : Val → Val → Maybe Val
updR ⟨⟩        v         = just v
updR (c₁ · c₂) ⟨⟩        = just (c₁ · c₂)
updR (c₁ · c₂) (v₁ · v₂) = if beq (v₁ · v₂) (c₁ · c₂) then just ⟨⟩ else nothing

------------------------------------------------------------------------
-- Maybe plumbing (kept local and first-order so terms reduce in proofs).

_>>=_ : Maybe Val → (Val → Maybe Val) → Maybe Val
just v  >>= f = f v
nothing >>= f = nothing

assertB : Bool → Val → Maybe Val
assertB true  ρ = just ρ
assertB false ρ = nothing

nothing≢just : ∀ {A : Set} {x : A} {W : Set} →
               _≡_ {A = Maybe A} nothing (just x) → W
nothing≢just ()

------------------------------------------------------------------------
-- Patterns.  evalP = evalPat (read, CLEARING variables); invP = inv_evalPat
-- (write; a variable slot must be nil first, a literal must match exactly).

evalP : Pat → Val → Val × Val
evalP (pVar n)    ρ = vSet n ⟨⟩ ρ , vNth n ρ
evalP (pVal v)    ρ = ρ , v
evalP (pCons p q) ρ =
  let (ρ₁ , v₁) = evalP p ρ
      (ρ₂ , v₂) = evalP q ρ₁
  in ρ₂ , (v₁ · v₂)

invP : Pat → Val → Val → Maybe Val
invP (pCons p q) (v₁ · v₂) ρ = invP p v₁ ρ >>= invP q v₂
invP (pCons p q) ⟨⟩        ρ = nothing
invP (pVar n) v ρ with vNth n ρ
... | ⟨⟩    = just (vSet n v ρ)
... | _ · _ = nothing
invP (pVal w) v ρ = assertB (beq v w) ρ

------------------------------------------------------------------------
-- Commands (fuel-indexed; one fuel per nesting level / loop round).

evalC : ℕ → Com → Val → Maybe Val
evalL : ℕ → Ex → Com → Com → Ex → Val → Maybe Val

evalC zero    _ _ = nothing
evalC (suc n) (cSeq a b) ρ = evalC n a ρ >>= evalC n b
evalC (suc n) (cAss k e) ρ =
  updR (vNth k ρ) (⟦ e ⟧ ρ) >>= λ v → just (vSet k v ρ)
evalC (suc n) (cRep q r) ρ =
  invP q (proj₂ (evalP r ρ)) (proj₁ (evalP r ρ))
evalC (suc n) (cCond e t d f) ρ =
  if isT (⟦ e ⟧ ρ)
  then (evalC n t ρ >>= λ ρ₁ → assertB (isT (⟦ f ⟧ ρ₁)) ρ₁)
  else (evalC n d ρ >>= λ ρ₁ → assertB (not (isT (⟦ f ⟧ ρ₁))) ρ₁)
evalC (suc n) (cLoop e d l f) ρ =
  if isT (⟦ e ⟧ ρ) then (evalC n d ρ >>= evalL n e d l f) else nothing

evalL zero    _ _ _ _ _ = nothing
evalL (suc n) e d l f ρ =
  if isT (⟦ f ⟧ ρ) then just ρ
  else (evalC n l ρ >>= λ ρ₁ →
        if isT (⟦ e ⟧ ρ₁) then nothing
        else (evalC n d ρ₁ >>= evalL n e d l f))

-- Whole programs (evalProgram): all-nil store, input into slot i, run,
-- result from slot j, and the store CLEARED of everything else.
clearedB : Val → Bool
clearedB ⟨⟩            = true
clearedB (⟨⟩ · rest)    = clearedB rest
clearedB ((_ · _) · _)  = false

evalProg : ℕ → Prog → Val → Maybe Val
evalProg n (prog i c j) v =
  evalC n c (vSet i v ⟨⟩) >>= λ ρ →
  assertB (clearedB (vSet j ⟨⟩ ρ)) (vNth j ρ)

------------------------------------------------------------------------
-- Fuel monotonicity: a `just` result is stable under more fuel (so the
-- fuel is a totality device, not part of the meaning).

evalC-mono : ∀ {n m} → n ≤ m → ∀ c ρ {ρ'} →
             evalC n c ρ ≡ just ρ' → evalC m c ρ ≡ just ρ'
evalL-mono : ∀ {n m} → n ≤ m → ∀ e d l f ρ {ρ'} →
             evalL n e d l f ρ ≡ just ρ' → evalL m e d l f ρ ≡ just ρ'

evalC-mono {zero}  z≤n       c ρ eq = nothing≢just eq
evalC-mono {suc n} {suc m} (s≤s le) (cSeq a b) ρ eq with evalC n a ρ in eqa
... | just ρ₁ rewrite evalC-mono le a ρ eqa = evalC-mono le b ρ₁ eq
... | nothing = nothing≢just eq
evalC-mono {suc n} {suc m} (s≤s le) (cAss k e) ρ eq = eq
evalC-mono {suc n} {suc m} (s≤s le) (cRep q r) ρ eq = eq
evalC-mono {suc n} {suc m} (s≤s le) (cCond e t d f) ρ eq with isT (⟦ e ⟧ ρ)
... | true with evalC n t ρ in eqt
...   | just ρ₁ rewrite evalC-mono le t ρ eqt = eq
...   | nothing = nothing≢just eq
evalC-mono {suc n} {suc m} (s≤s le) (cCond e t d f) ρ eq | false
  with evalC n d ρ in eqd
... | just ρ₁ rewrite evalC-mono le d ρ eqd = eq
... | nothing = nothing≢just eq
evalC-mono {suc n} {suc m} (s≤s le) (cLoop e d l f) ρ eq with isT (⟦ e ⟧ ρ)
... | false = nothing≢just eq
... | true with evalC n d ρ in eqd
...   | just ρ₁ rewrite evalC-mono le d ρ eqd = evalL-mono le e d l f ρ₁ eq
...   | nothing = nothing≢just eq

evalL-mono {zero}  z≤n       e d l f ρ eq = nothing≢just eq
evalL-mono {suc n} {suc m} (s≤s le) e d l f ρ eq with isT (⟦ f ⟧ ρ)
... | true = eq
... | false with evalC n l ρ in eql
...   | nothing = nothing≢just eq
...   | just ρ₁ rewrite evalC-mono le l ρ eql with isT (⟦ e ⟧ ρ₁)
...     | true = nothing≢just eq
...     | false with evalC n d ρ₁ in eqd
...       | nothing = nothing≢just eq
...       | just ρ₂ rewrite evalC-mono le d ρ₁ eqd = evalL-mono le e d l f ρ₂ eq

evalProg-mono : ∀ {n m} → n ≤ m → ∀ p v {w} →
                evalProg n p v ≡ just w → evalProg m p v ≡ just w
evalProg-mono {n} {m} le (prog i c j) v eq with evalC n c (vSet i v ⟨⟩) in eqc
... | just ρ rewrite evalC-mono le c (vSet i v ⟨⟩) eqc = eq
... | nothing = nothing≢just eq

------------------------------------------------------------------------
-- Examples (test-first checks, by refl): a two-CRep SWAP program, the
-- reversible-XOR identity via a degenerate loop, and both faces of the
-- conditional's exit assertion.

module Examples where

  -- read 0; ⟨x1.x2⟩ <= x0 ; x0 <= ⟨x2.x1⟩ ; write 0   — swaps a pair.
  swapP : Prog
  swapP = prog 0 (cSeq (cRep (pCons (pVar 1) (pVar 2)) (pVar 0))
                       (cRep (pVar 0) (pCons (pVar 2) (pVar 1)))) 0

  _ : evalProg 10 swapP (vtrue · vfalse) ≡ just (vfalse · vtrue)
  _ = refl

  -- a loop that runs its do-branch once (entry true, exit immediately),
  -- then the reversible XOR clears the source slot: identity, garbage-free.
  idLoopP : Prog
  idLoopP = prog 0 (cSeq (cLoop (exVal vtrue)
                                (cAss 1 (varN 0))
                                (cRep (pVar 3) (pVar 3))
                                (exVal vtrue))
                         (cAss 0 (varN 1))) 1

  _ : evalProg 20 idLoopP vtrue ≡ just vtrue
  _ = refl

  -- conditional exit assertion: after the then-branch f must be TRUE …
  condC : Com
  condC = cCond (exPairp (varN 0)) (cAss 1 (exVal vtrue))
                                   (cAss 1 (exVal vtrue)) (varN 1)

  _ : evalC 5 condC (vtrue · ⟨⟩) ≡ just (vtrue · (vtrue · ⟨⟩))
  _ = refl

  -- … and after the else-branch f must be FALSE — here it is true, so the
  -- run FAILS (the reversibility assertion, not a crash of the model).
  _ : evalC 5 condC (⟨⟩ · ⟨⟩) ≡ nothing
  _ = refl

  -- reversible-update conflict: assigning a different non-nil value fails.
  _ : evalC 5 (cAss 0 (exVal vtrue)) ((vtrue · vtrue) · ⟨⟩) ≡ nothing
  _ = refl

  -- a program that leaves garbage is REJECTED (store-not-cleared).
  dirtyP : Prog
  dirtyP = prog 0 (cAss 1 (varN 0)) 1
  _ : evalProg 10 dirtyP vtrue ≡ nothing
  _ = refl
