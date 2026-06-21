{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Tier-2 #5 (engineering, step 2): the spec_av WORKLIST carrying the REAL AV
-- ALGEBRA.  RWhileH2Worklist modelled spec_av's SPEC-EXP-AV stack machine with
-- an abstract combine; here we load the actual annotated-value operations of
-- RWhileAVSound (avCons/avHd/avTl, with 'S static / 'D dynamic / 'C partial-
-- static cons) into the worklist, so it ASSEMBLES AV RESIDUALS exactly as
-- spec_av does, and prove the assembled residual is SOUND: concretising it (γ,
-- filling the dynamic hole ρ) equals the source expression's concrete value.
--
-- Expression language Ex = var | val | cons | hd | tl (spec_av's SPEC-EXP-AV
-- cases).  The worklist is a fuel-indexed stack machine (tasks doEx / kCons /
-- kHd / kTl = the begin/end markers), proven via a relation `_⟱_` to assemble
-- `avEval ex`, then γ-sound: γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ.  Partial-static
-- residuals (e.g. cons of a static head and the dynamic input) are produced and
-- shown correct -- the looping AV specialiser of spec_av, concretised + verified.
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
  ( Val; ⟨⟩; _·_; vtrue; hd; tl; Code; cVar; ⟦_⟧c
  ; AV; S; D; C; γ; avCons; avHd; avTl; avCons-sound; avHd-sound; avTl-sound)

------------------------------------------------------------------------
-- Source expressions (spec_av's expression cases) and their concrete semantics.

data Ex : Set where
  exVar  : Ex
  exVal  : Val → Ex
  exCons : Ex → Ex → Ex
  exHd   : Ex → Ex
  exTl   : Ex → Ex

⟦_⟧ : Ex → Val → Val
⟦ exVar      ⟧ ρ = ρ
⟦ exVal v    ⟧ ρ = v
⟦ exCons a b ⟧ ρ = (⟦ a ⟧ ρ) · (⟦ b ⟧ ρ)
⟦ exHd e     ⟧ ρ = hd (⟦ e ⟧ ρ)
⟦ exTl e     ⟧ ρ = tl (⟦ e ⟧ ρ)

------------------------------------------------------------------------
-- Meta-level AV evaluation (the residual spec_av builds) and its soundness.

avEval : Ex → AV
avEval exVar        = D cVar          -- the dynamic input
avEval (exVal v)    = S v             -- static
avEval (exCons a b) = avCons (avEval a) (avEval b)
avEval (exHd e)     = avHd (avEval e)
avEval (exTl e)     = avTl (avEval e)

avEval-sound : ∀ ex ρ → γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ
avEval-sound exVar        ρ = refl
avEval-sound (exVal v)    ρ = refl
avEval-sound (exCons a b) ρ =
  trans (avCons-sound (avEval a) (avEval b) ρ)
        (cong₂ _·_ (avEval-sound a ρ) (avEval-sound b ρ))
avEval-sound (exHd e)     ρ = trans (avHd-sound (avEval e) ρ) (cong hd (avEval-sound e ρ))
avEval-sound (exTl e)     ρ = trans (avTl-sound (avEval e) ρ) (cong tl (avEval-sound e ρ))

------------------------------------------------------------------------
-- The worklist stack machine: tasks evaluate an expr or combine results with the
-- real AV operations (kCons = avCons, kHd = avHd, kTl = avTl).

data Task : Set where
  doEx  : Ex → Task
  kCons : Task
  kHd   : Task
  kTl   : Task

infix 4 _⟱_
data _⟱_ : (List Task × List AV) → List AV → Set where
  ⟱nil  : ∀ rs → ([] , rs) ⟱ rs
  ⟱var  : ∀ {ts rs r}     → (ts , D cVar ∷ rs) ⟱ r → (doEx exVar ∷ ts , rs) ⟱ r
  ⟱val  : ∀ {v ts rs r}   → (ts , S v ∷ rs) ⟱ r     → (doEx (exVal v) ∷ ts , rs) ⟱ r
  ⟱cons : ∀ {a b ts rs r} → (doEx a ∷ doEx b ∷ kCons ∷ ts , rs) ⟱ r → (doEx (exCons a b) ∷ ts , rs) ⟱ r
  ⟱hd   : ∀ {e ts rs r}   → (doEx e ∷ kHd ∷ ts , rs) ⟱ r → (doEx (exHd e) ∷ ts , rs) ⟱ r
  ⟱tl   : ∀ {e ts rs r}   → (doEx e ∷ kTl ∷ ts , rs) ⟱ r → (doEx (exTl e) ∷ ts , rs) ⟱ r
  ⟱kCons : ∀ {x y ts rs r} → (ts , avCons x y ∷ rs) ⟱ r → (kCons ∷ ts , y ∷ x ∷ rs) ⟱ r
  ⟱kHd  : ∀ {x ts rs r}   → (ts , avHd x ∷ rs) ⟱ r → (kHd ∷ ts , x ∷ rs) ⟱ r
  ⟱kTl  : ∀ {x ts rs r}   → (ts , avTl x ∷ rs) ⟱ r → (kTl ∷ ts , x ∷ rs) ⟱ r

-- the worklist assembles `avEval ex` on top of any stacks (abstract-machine lemma).
machine-spec : ∀ ex ts rs {r} → (ts , avEval ex ∷ rs) ⟱ r → (doEx ex ∷ ts , rs) ⟱ r
machine-spec exVar ts rs h = ⟱var h
machine-spec (exVal v) ts rs h = ⟱val h
machine-spec (exCons a b) ts rs h =
  ⟱cons (machine-spec a (doEx b ∷ kCons ∷ ts) rs
          (machine-spec b (kCons ∷ ts) (avEval a ∷ rs)
            (⟱kCons {x = avEval a} {y = avEval b} h)))
machine-spec (exHd e) ts rs h = ⟱hd (machine-spec e (kHd ∷ ts) rs (⟱kHd {x = avEval e} h))
machine-spec (exTl e) ts rs h = ⟱tl (machine-spec e (kTl ∷ ts) rs (⟱kTl {x = avEval e} h))

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
machineF zero    _                       _            = nothing
machineF (suc n) []                      rs           = just rs
machineF (suc n) (doEx exVar ∷ ts)       rs           = machineF n ts (D cVar ∷ rs)
machineF (suc n) (doEx (exVal v) ∷ ts)   rs           = machineF n ts (S v ∷ rs)
machineF (suc n) (doEx (exCons a b) ∷ ts) rs          = machineF n (doEx a ∷ doEx b ∷ kCons ∷ ts) rs
machineF (suc n) (doEx (exHd e) ∷ ts)    rs           = machineF n (doEx e ∷ kHd ∷ ts) rs
machineF (suc n) (doEx (exTl e) ∷ ts)    rs           = machineF n (doEx e ∷ kTl ∷ ts) rs
machineF (suc n) (kCons ∷ ts)            (y ∷ x ∷ rs) = machineF n ts (avCons x y ∷ rs)
machineF (suc n) (kCons ∷ ts)            []           = nothing
machineF (suc n) (kCons ∷ ts)            (_ ∷ [])     = nothing
machineF (suc n) (kHd ∷ ts)              (x ∷ rs)     = machineF n ts (avHd x ∷ rs)
machineF (suc n) (kHd ∷ ts)              []           = nothing
machineF (suc n) (kTl ∷ ts)              (x ∷ rs)     = machineF n ts (avTl x ∷ rs)
machineF (suc n) (kTl ∷ ts)              []           = nothing

machineF-sound : ∀ n ts rs {r} → machineF n ts rs ≡ just r → (ts , rs) ⟱ r
machineF-sound zero ts rs ()
machineF-sound (suc n) [] rs refl = ⟱nil rs
machineF-sound (suc n) (doEx exVar ∷ ts) rs eq = ⟱var (machineF-sound n ts (D cVar ∷ rs) eq)
machineF-sound (suc n) (doEx (exVal v) ∷ ts) rs eq = ⟱val (machineF-sound n ts (S v ∷ rs) eq)
machineF-sound (suc n) (doEx (exCons a b) ∷ ts) rs eq =
  ⟱cons (machineF-sound n (doEx a ∷ doEx b ∷ kCons ∷ ts) rs eq)
machineF-sound (suc n) (doEx (exHd e) ∷ ts) rs eq = ⟱hd (machineF-sound n (doEx e ∷ kHd ∷ ts) rs eq)
machineF-sound (suc n) (doEx (exTl e) ∷ ts) rs eq = ⟱tl (machineF-sound n (doEx e ∷ kTl ∷ ts) rs eq)
machineF-sound (suc n) (kCons ∷ ts) (y ∷ x ∷ rs) eq = ⟱kCons (machineF-sound n ts (avCons x y ∷ rs) eq)
machineF-sound (suc n) (kCons ∷ ts) [] ()
machineF-sound (suc n) (kCons ∷ ts) (_ ∷ []) ()
machineF-sound (suc n) (kHd ∷ ts) (x ∷ rs) eq = ⟱kHd (machineF-sound n ts (avHd x ∷ rs) eq)
machineF-sound (suc n) (kHd ∷ ts) [] ()
machineF-sound (suc n) (kTl ∷ ts) (x ∷ rs) eq = ⟱kTl (machineF-sound n ts (avTl x ∷ rs) eq)
machineF-sound (suc n) (kTl ∷ ts) [] ()

machineF-mono-≤ : ∀ {n m} → n ≤ m → ∀ ts rs {r} → machineF n ts rs ≡ just r → machineF m ts rs ≡ just r
machineF-mono-≤ z≤n ts rs ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) [] rs eq = eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx exVar ∷ ts) rs eq = machineF-mono-≤ le ts (D cVar ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exVal v) ∷ ts) rs eq = machineF-mono-≤ le ts (S v ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exCons a b) ∷ ts) rs eq =
  machineF-mono-≤ le (doEx a ∷ doEx b ∷ kCons ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exHd e) ∷ ts) rs eq =
  machineF-mono-≤ le (doEx e ∷ kHd ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (doEx (exTl e) ∷ ts) rs eq =
  machineF-mono-≤ le (doEx e ∷ kTl ∷ ts) rs eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kCons ∷ ts) (y ∷ x ∷ rs) eq = machineF-mono-≤ le ts (avCons x y ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kCons ∷ ts) [] ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kCons ∷ ts) (_ ∷ []) ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kHd ∷ ts) (x ∷ rs) eq = machineF-mono-≤ le ts (avHd x ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kHd ∷ ts) [] ()
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kTl ∷ ts) (x ∷ rs) eq = machineF-mono-≤ le ts (avTl x ∷ rs) eq
machineF-mono-≤ {suc n} {suc m} (s≤s le) (kTl ∷ ts) [] ()

machineF-complete : ∀ {ts rs r} → (ts , rs) ⟱ r → Σ ℕ (λ n → machineF n ts rs ≡ just r)
machineF-complete (⟱nil rs)  = suc zero , refl
machineF-complete (⟱var d)   with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱val d)   with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱cons d)  with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱hd d)    with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱tl d)    with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kCons d) with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kHd d)   with machineF-complete d
... | n , e = suc n , e
machineF-complete (⟱kTl d)   with machineF-complete d
... | n , e = suc n , e

-- the fuelled worklist assembles avEval ex within some finite fuel, and γ-soundly.
worklist-fuel-sound :
  ∀ ex ρ → Σ ℕ (λ n → machineF n (doEx ex ∷ []) [] ≡ just (avEval ex ∷ []))
         × (γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ)
worklist-fuel-sound ex ρ = machineF-complete (machine-correct ex) , avEval-sound ex ρ

------------------------------------------------------------------------
-- Witness: a PARTIAL-STATIC residual.  cons of a static head (vtrue) and the
-- dynamic input assembles to `C (S vtrue) (D cVar)` and concretises to vtrue · ρ.

module Witness where
  ex0 : Ex
  ex0 = exCons (exVal vtrue) exVar

  -- the worklist builds the partial-static AV  C (S vtrue) (D cVar).
  build : Σ ℕ (λ n → machineF n (doEx ex0 ∷ []) [] ≡ just (C (S vtrue) (D cVar) ∷ []))
  build = machineF-complete (machine-correct ex0)

  -- and it is sound: γ of that residual is vtrue · ρ = ⟦ ex0 ⟧ ρ for every ρ.
  sound : ∀ ρ → γ (C (S vtrue) (D cVar)) ρ ≡ (vtrue · ρ)
  sound ρ = refl
