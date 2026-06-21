{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Tier-2 #5 (engineering, step 2): the spec_av WORKLIST carrying the REAL AV
-- ALGEBRA.  RWhileH2Worklist modelled spec_av's SPEC-EXP-AV stack machine with
-- an abstract combine; here we load the actual annotated-value operations of
-- RWhileAVSound (avCons/avHd/avTl/avEq/avPairp, 'S static / 'D dynamic / 'C
-- partial-static cons) into the worklist, so it ASSEMBLES AV RESIDUALS exactly as
-- spec_av does, and prove the residual SOUND: concretising it (γ, filling the
-- dynamic input ρ) equals the source expression's concrete value.
--
-- Expression language Ex covers spec_av's SPEC-EXP-AV cases: a STORE-indexed
-- variable (`varN n` = the n-th slot, read by walking the store with tl then hd
-- -- exactly spec_av's AUX/LOOKUP), a static value, cons, hd, tl, EQ and PAIRP.
-- The worklist is a fuel-indexed stack machine (tasks doEx / kCons / kHd / kTl /
-- kEq / kPairp = begin/end markers), proven via a relation `_⟱_` to assemble
-- `avEval ex`, then γ-sound: γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ.  Partial-static
-- residuals are produced and shown correct -- the looping AV specialiser of
-- spec_av (loop machinery + AV algebra + store access + γ-soundness), verified.
--
-- Store model: ρ is the (cons-list) store; slot n = hd (tl^n ρ) = avNth n.  The
-- remaining step to the full spec_av is a partial-static MULTI-slot store (each
-- slot an independent AV), which needs multi-hole residual code.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2WorklistAV where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import RWhileAVSound using
  ( Val; ⟨⟩; _·_; vtrue; hd; tl; pairp; veq; Code; cVar; ⟦_⟧c
  ; AV; S; D; C; γ; avCons; avHd; avTl; avEq; avPairp
  ; avCons-sound; avHd-sound; avTl-sound; avEq-sound; avPairp-sound)

------------------------------------------------------------------------
-- Store indexing: slot n of a cons-list value = hd (tl^n ·).

vNth : ℕ → Val → Val
vNth zero    ρ = hd ρ
vNth (suc n) ρ = vNth n (tl ρ)

-- the AV-level walk (spec_av's AUX/LOOKUP): tl down n slots, then hd.
avNth : ℕ → AV → AV
avNth zero    a = avHd a
avNth (suc n) a = avNth n (avTl a)

avNth-sound : ∀ n a ρ → γ (avNth n a) ρ ≡ vNth n (γ a ρ)
avNth-sound zero    a ρ = avHd-sound a ρ
avNth-sound (suc n) a ρ = trans (avNth-sound n (avTl a) ρ) (cong (vNth n) (avTl-sound a ρ))

------------------------------------------------------------------------
-- Source expressions (spec_av's SPEC-EXP-AV cases) and concrete semantics.

data Ex : Set where
  varN   : ℕ → Ex          -- the n-th store slot
  exVal  : Val → Ex
  exCons : Ex → Ex → Ex
  exHd   : Ex → Ex
  exTl   : Ex → Ex
  exEq   : Ex → Ex → Ex
  exPairp : Ex → Ex

⟦_⟧ : Ex → Val → Val
⟦ varN n     ⟧ ρ = vNth n ρ
⟦ exVal v    ⟧ ρ = v
⟦ exCons a b ⟧ ρ = (⟦ a ⟧ ρ) · (⟦ b ⟧ ρ)
⟦ exHd e     ⟧ ρ = hd (⟦ e ⟧ ρ)
⟦ exTl e     ⟧ ρ = tl (⟦ e ⟧ ρ)
⟦ exEq a b   ⟧ ρ = veq (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)
⟦ exPairp e  ⟧ ρ = pairp (⟦ e ⟧ ρ)

------------------------------------------------------------------------
-- Meta-level AV evaluation (the residual spec_av builds) and its soundness.

avEval : Ex → AV
avEval (varN n)     = avNth n (D cVar)      -- LOOKUP: walk the (dynamic) store
avEval (exVal v)    = S v
avEval (exCons a b) = avCons (avEval a) (avEval b)
avEval (exHd e)     = avHd (avEval e)
avEval (exTl e)     = avTl (avEval e)
avEval (exEq a b)   = avEq (avEval a) (avEval b)
avEval (exPairp e)  = avPairp (avEval e)

avEval-sound : ∀ ex ρ → γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ
avEval-sound (varN n)     ρ = avNth-sound n (D cVar) ρ
avEval-sound (exVal v)    ρ = refl
avEval-sound (exCons a b) ρ =
  trans (avCons-sound (avEval a) (avEval b) ρ)
        (cong₂ _·_ (avEval-sound a ρ) (avEval-sound b ρ))
avEval-sound (exHd e)     ρ = trans (avHd-sound (avEval e) ρ) (cong hd (avEval-sound e ρ))
avEval-sound (exTl e)     ρ = trans (avTl-sound (avEval e) ρ) (cong tl (avEval-sound e ρ))
avEval-sound (exEq a b)   ρ =
  trans (avEq-sound (avEval a) (avEval b) ρ)
        (cong₂ veq (avEval-sound a ρ) (avEval-sound b ρ))
avEval-sound (exPairp e)  ρ = trans (avPairp-sound (avEval e) ρ) (cong pairp (avEval-sound e ρ))

------------------------------------------------------------------------
-- The worklist stack machine: tasks evaluate an expr or combine results with the
-- real AV operations.

data Task : Set where
  doEx   : Ex → Task
  kCons  : Task
  kHd    : Task
  kTl    : Task
  kEq    : Task
  kPairp : Task

infix 4 _⟱_
data _⟱_ : (List Task × List AV) → List AV → Set where
  ⟱nil   : ∀ rs → ([] , rs) ⟱ rs
  ⟱varN  : ∀ {n ts rs r}   → (ts , avNth n (D cVar) ∷ rs) ⟱ r → (doEx (varN n) ∷ ts , rs) ⟱ r
  ⟱val   : ∀ {v ts rs r}   → (ts , S v ∷ rs) ⟱ r     → (doEx (exVal v) ∷ ts , rs) ⟱ r
  ⟱cons  : ∀ {a b ts rs r} → (doEx a ∷ doEx b ∷ kCons ∷ ts , rs) ⟱ r → (doEx (exCons a b) ∷ ts , rs) ⟱ r
  ⟱hd    : ∀ {e ts rs r}   → (doEx e ∷ kHd ∷ ts , rs) ⟱ r → (doEx (exHd e) ∷ ts , rs) ⟱ r
  ⟱tl    : ∀ {e ts rs r}   → (doEx e ∷ kTl ∷ ts , rs) ⟱ r → (doEx (exTl e) ∷ ts , rs) ⟱ r
  ⟱eq    : ∀ {a b ts rs r} → (doEx a ∷ doEx b ∷ kEq ∷ ts , rs) ⟱ r → (doEx (exEq a b) ∷ ts , rs) ⟱ r
  ⟱pairp : ∀ {e ts rs r}   → (doEx e ∷ kPairp ∷ ts , rs) ⟱ r → (doEx (exPairp e) ∷ ts , rs) ⟱ r
  ⟱kCons : ∀ {x y ts rs r} → (ts , avCons x y ∷ rs) ⟱ r → (kCons ∷ ts , y ∷ x ∷ rs) ⟱ r
  ⟱kHd   : ∀ {x ts rs r}   → (ts , avHd x ∷ rs) ⟱ r → (kHd ∷ ts , x ∷ rs) ⟱ r
  ⟱kTl   : ∀ {x ts rs r}   → (ts , avTl x ∷ rs) ⟱ r → (kTl ∷ ts , x ∷ rs) ⟱ r
  ⟱kEq   : ∀ {x y ts rs r} → (ts , avEq x y ∷ rs) ⟱ r → (kEq ∷ ts , y ∷ x ∷ rs) ⟱ r
  ⟱kPairp : ∀ {x ts rs r}  → (ts , avPairp x ∷ rs) ⟱ r → (kPairp ∷ ts , x ∷ rs) ⟱ r

-- the worklist assembles `avEval ex` on top of any stacks (abstract-machine lemma).
machine-spec : ∀ ex ts rs {r} → (ts , avEval ex ∷ rs) ⟱ r → (doEx ex ∷ ts , rs) ⟱ r
machine-spec (varN n) ts rs h = ⟱varN h
machine-spec (exVal v) ts rs h = ⟱val h
machine-spec (exCons a b) ts rs h =
  ⟱cons (machine-spec a (doEx b ∷ kCons ∷ ts) rs
          (machine-spec b (kCons ∷ ts) (avEval a ∷ rs)
            (⟱kCons {x = avEval a} {y = avEval b} h)))
machine-spec (exHd e) ts rs h = ⟱hd (machine-spec e (kHd ∷ ts) rs (⟱kHd {x = avEval e} h))
machine-spec (exTl e) ts rs h = ⟱tl (machine-spec e (kTl ∷ ts) rs (⟱kTl {x = avEval e} h))
machine-spec (exEq a b) ts rs h =
  ⟱eq (machine-spec a (doEx b ∷ kEq ∷ ts) rs
        (machine-spec b (kEq ∷ ts) (avEval a ∷ rs)
          (⟱kEq {x = avEval a} {y = avEval b} h)))
machine-spec (exPairp e) ts rs h = ⟱pairp (machine-spec e (kPairp ∷ ts) rs (⟱kPairp {x = avEval e} h))

machine-correct : ∀ ex → (doEx ex ∷ [] , []) ⟱ (avEval ex ∷ [])
machine-correct ex = machine-spec ex [] [] (⟱nil (avEval ex ∷ []))

-- HEADLINE: the worklist specialiser is SOUND -- it assembles an AV residual
-- whose concretisation equals the source expression's concrete value.
worklist-spec-sound :
  ∀ ex ρ → ((doEx ex ∷ [] , []) ⟱ (avEval ex ∷ [])) × (γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ)
worklist-spec-sound ex ρ = machine-correct ex , avEval-sound ex ρ

------------------------------------------------------------------------
-- Fuel-indexed machine (total; one task per step).

machineF : ℕ → List Task → List AV → Maybe (List AV)
machineF zero    _                        _            = nothing
machineF (suc n) []                       rs           = just rs
machineF (suc n) (doEx (varN k) ∷ ts)     rs           = machineF n ts (avNth k (D cVar) ∷ rs)
machineF (suc n) (doEx (exVal v) ∷ ts)    rs           = machineF n ts (S v ∷ rs)
machineF (suc n) (doEx (exCons a b) ∷ ts) rs           = machineF n (doEx a ∷ doEx b ∷ kCons ∷ ts) rs
machineF (suc n) (doEx (exHd e) ∷ ts)     rs           = machineF n (doEx e ∷ kHd ∷ ts) rs
machineF (suc n) (doEx (exTl e) ∷ ts)     rs           = machineF n (doEx e ∷ kTl ∷ ts) rs
machineF (suc n) (doEx (exEq a b) ∷ ts)   rs           = machineF n (doEx a ∷ doEx b ∷ kEq ∷ ts) rs
machineF (suc n) (doEx (exPairp e) ∷ ts)  rs           = machineF n (doEx e ∷ kPairp ∷ ts) rs
machineF (suc n) (kCons ∷ ts)             (y ∷ x ∷ rs) = machineF n ts (avCons x y ∷ rs)
machineF (suc n) (kCons ∷ ts)             []           = nothing
machineF (suc n) (kCons ∷ ts)             (_ ∷ [])     = nothing
machineF (suc n) (kHd ∷ ts)               (x ∷ rs)     = machineF n ts (avHd x ∷ rs)
machineF (suc n) (kHd ∷ ts)               []           = nothing
machineF (suc n) (kTl ∷ ts)               (x ∷ rs)     = machineF n ts (avTl x ∷ rs)
machineF (suc n) (kTl ∷ ts)               []           = nothing
machineF (suc n) (kEq ∷ ts)               (y ∷ x ∷ rs) = machineF n ts (avEq x y ∷ rs)
machineF (suc n) (kEq ∷ ts)               []           = nothing
machineF (suc n) (kEq ∷ ts)               (_ ∷ [])     = nothing
machineF (suc n) (kPairp ∷ ts)            (x ∷ rs)     = machineF n ts (avPairp x ∷ rs)
machineF (suc n) (kPairp ∷ ts)            []           = nothing

machineF-sound : ∀ n ts rs {r} → machineF n ts rs ≡ just r → (ts , rs) ⟱ r
machineF-sound zero ts rs ()
machineF-sound (suc n) [] rs refl = ⟱nil rs
machineF-sound (suc n) (doEx (varN k) ∷ ts) rs eq = ⟱varN (machineF-sound n ts (avNth k (D cVar) ∷ rs) eq)
machineF-sound (suc n) (doEx (exVal v) ∷ ts) rs eq = ⟱val (machineF-sound n ts (S v ∷ rs) eq)
machineF-sound (suc n) (doEx (exCons a b) ∷ ts) rs eq =
  ⟱cons (machineF-sound n (doEx a ∷ doEx b ∷ kCons ∷ ts) rs eq)
machineF-sound (suc n) (doEx (exHd e) ∷ ts) rs eq = ⟱hd (machineF-sound n (doEx e ∷ kHd ∷ ts) rs eq)
machineF-sound (suc n) (doEx (exTl e) ∷ ts) rs eq = ⟱tl (machineF-sound n (doEx e ∷ kTl ∷ ts) rs eq)
machineF-sound (suc n) (doEx (exEq a b) ∷ ts) rs eq =
  ⟱eq (machineF-sound n (doEx a ∷ doEx b ∷ kEq ∷ ts) rs eq)
machineF-sound (suc n) (doEx (exPairp e) ∷ ts) rs eq = ⟱pairp (machineF-sound n (doEx e ∷ kPairp ∷ ts) rs eq)
machineF-sound (suc n) (kCons ∷ ts) (y ∷ x ∷ rs) eq = ⟱kCons (machineF-sound n ts (avCons x y ∷ rs) eq)
machineF-sound (suc n) (kCons ∷ ts) [] ()
machineF-sound (suc n) (kCons ∷ ts) (_ ∷ []) ()
machineF-sound (suc n) (kHd ∷ ts) (x ∷ rs) eq = ⟱kHd (machineF-sound n ts (avHd x ∷ rs) eq)
machineF-sound (suc n) (kHd ∷ ts) [] ()
machineF-sound (suc n) (kTl ∷ ts) (x ∷ rs) eq = ⟱kTl (machineF-sound n ts (avTl x ∷ rs) eq)
machineF-sound (suc n) (kTl ∷ ts) [] ()
machineF-sound (suc n) (kEq ∷ ts) (y ∷ x ∷ rs) eq = ⟱kEq (machineF-sound n ts (avEq x y ∷ rs) eq)
machineF-sound (suc n) (kEq ∷ ts) [] ()
machineF-sound (suc n) (kEq ∷ ts) (_ ∷ []) ()
machineF-sound (suc n) (kPairp ∷ ts) (x ∷ rs) eq = ⟱kPairp (machineF-sound n ts (avPairp x ∷ rs) eq)
machineF-sound (suc n) (kPairp ∷ ts) [] ()

machineF-mono-≤ : ∀ {n m} → n ≤ m → ∀ ts rs {r} → machineF n ts rs ≡ just r → machineF m ts rs ≡ just r
machineF-mono-≤ z≤n ts rs ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) [] rs eq = eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (varN k) ∷ ts) rs eq = machineF-mono-≤ le ts (avNth k (D cVar) ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exVal v) ∷ ts) rs eq = machineF-mono-≤ le ts (S v ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exCons a b) ∷ ts) rs eq = machineF-mono-≤ le (doEx a ∷ doEx b ∷ kCons ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exHd e) ∷ ts) rs eq = machineF-mono-≤ le (doEx e ∷ kHd ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exTl e) ∷ ts) rs eq = machineF-mono-≤ le (doEx e ∷ kTl ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exEq a b) ∷ ts) rs eq = machineF-mono-≤ le (doEx a ∷ doEx b ∷ kEq ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exPairp e) ∷ ts) rs eq = machineF-mono-≤ le (doEx e ∷ kPairp ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kCons ∷ ts) (y ∷ x ∷ rs) eq = machineF-mono-≤ le ts (avCons x y ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kCons ∷ ts) [] ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kCons ∷ ts) (_ ∷ []) ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kHd ∷ ts) (x ∷ rs) eq = machineF-mono-≤ le ts (avHd x ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kHd ∷ ts) [] ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kTl ∷ ts) (x ∷ rs) eq = machineF-mono-≤ le ts (avTl x ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kTl ∷ ts) [] ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kEq ∷ ts) (y ∷ x ∷ rs) eq = machineF-mono-≤ le ts (avEq x y ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kEq ∷ ts) [] ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kEq ∷ ts) (_ ∷ []) ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kPairp ∷ ts) (x ∷ rs) eq = machineF-mono-≤ le ts (avPairp x ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kPairp ∷ ts) [] ()

machineF-complete : ∀ {ts rs r} → (ts , rs) ⟱ r → Σ ℕ (λ n → machineF n ts rs ≡ just r)
machineF-complete (⟱nil rs)   = suc zero , refl
machineF-complete (⟱varN d)   with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱val d)    with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱cons d)   with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱hd d)     with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱tl d)     with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱eq d)     with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱pairp d)  with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kCons d)  with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kHd d)    with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kTl d)    with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kEq d)    with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kPairp d) with machineF-complete d
... | n , e = suc n , e

-- the fuelled worklist assembles avEval ex within some finite fuel, and γ-soundly.
worklist-fuel-sound :
  ∀ ex ρ → Σ ℕ (λ n → machineF n (doEx ex ∷ []) [] ≡ just (avEval ex ∷ []))
         × (γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ)
worklist-fuel-sound ex ρ = machineF-complete (machine-correct ex) , avEval-sound ex ρ

------------------------------------------------------------------------
-- Witness: a PARTIAL-STATIC residual using STORE access and EQ.  The expression
-- `cons (val vtrue) (varN 0)` reads slot 0 of the store and conses a static head,
-- assembling `C (S vtrue) (avNth 0 (D cVar))` (partial-static), γ-sound to
-- vtrue · hd ρ.

module Witness where
  ex0 : Ex
  ex0 = exCons (exVal vtrue) (varN 0)

  -- the worklist builds the partial-static AV (static head, dynamic store slot).
  build : Σ ℕ (λ n → machineF n (doEx ex0 ∷ []) [] ≡ just (avEval ex0 ∷ []))
  build = machineF-complete (machine-correct ex0)

  -- and it is sound for every store ρ: γ of the residual equals the concrete value.
  sound : ∀ ρ → γ (avEval ex0) ρ ≡ (vtrue · hd ρ)
  sound ρ = refl
