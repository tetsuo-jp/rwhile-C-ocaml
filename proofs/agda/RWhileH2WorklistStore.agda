{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Tier-2 #5 (engineering, the LAST piece): the PARTIAL-STATIC MULTI-SLOT STORE.
--
-- RWhileH2WorklistAV modelled the store as one dynamic input ρ (every slot
-- dynamic).  spec_av's real store `Vl` is a list of INDEPENDENT annotated values
-- -- some slots STATICALLY KNOWN (S v), some dynamic (D code) -- so a variable
-- read returns a partial-static AV directly.  Here the store is `List AV`; slot
-- access uses `cSlot n = cHd (cTl^n cVar)` (= spec_av's AUX/LOOKUP walk on the
-- runtime store), and out-of-range slots default to the dynamic `D (cSlot n)`.
--
-- The new content is a CONSISTENCY condition: a partial-static store `s` is
-- consistent with a runtime store ρ iff every slot's AV concretises to ρ's
-- actual slot (the STATIC slots must match ρ; dynamic slots match by cSlot-sound).
-- Under consistency, the worklist's assembled residual is SOUND:
--     Consistent s ρ → γ (avEval s ex) ρ ≡ ⟦ ex ⟧ ρ.
-- The witness builds a genuinely partial-static residual `C (S vtrue) (D (cSlot 1))`
-- from a store with a static slot 0 and a dynamic slot 1.  (The fuel-indexed
-- machine is identical to RWhileH2WorklistAV's with `varN n` pushing
-- `lookupAV n s`; we keep the relation-level machine here.)
--
-- `--safe`, no postulates/holes.  Reuses the AV algebra of RWhileAVSound.
------------------------------------------------------------------------

module RWhileH2WorklistStore where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import RWhileAVSound using
  ( Val; ⟨⟩; _·_; vtrue; hd; tl; pairp; veq; Code; cVar; cHd; cTl; ⟦_⟧c
  ; AV; S; D; C; γ; avCons; avHd; avTl; avEq; avPairp
  ; avCons-sound; avHd-sound; avTl-sound; avEq-sound; avPairp-sound)

------------------------------------------------------------------------
-- Store slot n of a cons-list value, and the residual code that reads it.

vNth : ℕ → Val → Val
vNth zero    ρ = hd ρ
vNth (suc n) ρ = vNth n (tl ρ)

cSlot′ : ℕ → Code → Code
cSlot′ zero    c = cHd c
cSlot′ (suc n) c = cSlot′ n (cTl c)

cSlot : ℕ → Code
cSlot n = cSlot′ n cVar

cSlot′-sound : ∀ n c ρ → ⟦ cSlot′ n c ⟧c ρ ≡ vNth n (⟦ c ⟧c ρ)
cSlot′-sound zero    c ρ = refl
cSlot′-sound (suc n) c ρ = cSlot′-sound n (cTl c) ρ

cSlot-sound : ∀ n ρ → ⟦ cSlot n ⟧c ρ ≡ vNth n ρ
cSlot-sound n ρ = cSlot′-sound n cVar ρ

------------------------------------------------------------------------
-- The partial-static store: a list of AVs.  lookupAV keeps the ABSOLUTE index
-- for the out-of-range default `D (cSlot n)` (a dynamic read of runtime slot n).

lk : ℕ → List AV → Maybe AV
lk _       []      = nothing
lk zero    (a ∷ _) = just a
lk (suc n) (_ ∷ s) = lk n s

lookupAV : ℕ → List AV → AV
lookupAV n s = maybe′ (λ a → a) (D (cSlot n)) (lk n s)

-- a store `s` is consistent with runtime store ρ: each slot concretises to ρ's.
Consistent : List AV → Val → Set
Consistent s ρ = ∀ n → γ (lookupAV n s) ρ ≡ vNth n ρ

------------------------------------------------------------------------
-- Source expressions and concrete semantics (over the runtime store ρ).

data Ex : Set where
  varN    : ℕ → Ex
  exVal   : Val → Ex
  exCons  : Ex → Ex → Ex
  exHd    : Ex → Ex
  exTl    : Ex → Ex
  exEq    : Ex → Ex → Ex
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
-- Specialisation over a fixed partial-static store `s`, and its soundness.

module Core (s : List AV) where

  avEval : Ex → AV
  avEval (varN n)     = lookupAV n s          -- read the slot's AV (static OR dynamic)
  avEval (exVal v)    = S v
  avEval (exCons a b) = avCons (avEval a) (avEval b)
  avEval (exHd e)     = avHd (avEval e)
  avEval (exTl e)     = avTl (avEval e)
  avEval (exEq a b)   = avEq (avEval a) (avEval b)
  avEval (exPairp e)  = avPairp (avEval e)

  -- SOUNDNESS under consistency: the assembled residual concretises to the
  -- concrete value -- even with statically-known store slots.
  avEval-sound : ∀ ρ → Consistent s ρ → ∀ ex → γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ
  avEval-sound ρ c (varN n)     = c n
  avEval-sound ρ c (exVal v)    = refl
  avEval-sound ρ c (exCons a b) =
    trans (avCons-sound (avEval a) (avEval b) ρ)
          (cong₂ _·_ (avEval-sound ρ c a) (avEval-sound ρ c b))
  avEval-sound ρ c (exHd e)     = trans (avHd-sound (avEval e) ρ) (cong hd (avEval-sound ρ c e))
  avEval-sound ρ c (exTl e)     = trans (avTl-sound (avEval e) ρ) (cong tl (avEval-sound ρ c e))
  avEval-sound ρ c (exEq a b)   =
    trans (avEq-sound (avEval a) (avEval b) ρ)
          (cong₂ veq (avEval-sound ρ c a) (avEval-sound ρ c b))
  avEval-sound ρ c (exPairp e)  = trans (avPairp-sound (avEval e) ρ) (cong pairp (avEval-sound ρ c e))

  ----------------------------------------------------------------------
  -- The worklist stack machine (relation level; varN reads slot from store s).
  data Task : Set where
    doEx   : Ex → Task
    kCons kHd kTl kEq kPairp : Task

  infix 4 _⟱_
  data _⟱_ : (List Task × List AV) → List AV → Set where
    ⟱nil   : ∀ rs → ([] , rs) ⟱ rs
    ⟱varN  : ∀ {n ts rs r}   → (ts , lookupAV n s ∷ rs) ⟱ r → (doEx (varN n) ∷ ts , rs) ⟱ r
    ⟱val   : ∀ {v ts rs r}   → (ts , S v ∷ rs) ⟱ r → (doEx (exVal v) ∷ ts , rs) ⟱ r
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

  -- HEADLINE: the worklist assembles the partial-static residual, and it is
  -- γ-sound for every runtime store consistent with the static slots.
  worklist-store-sound :
    ∀ ρ → Consistent s ρ → ∀ ex →
      ((doEx ex ∷ [] , []) ⟱ (avEval ex ∷ [])) × (γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ)
  worklist-store-sound ρ c ex = machine-correct ex , avEval-sound ρ c ex

------------------------------------------------------------------------
-- Witness: a genuinely PARTIAL-STATIC store -- slot 0 static (S vtrue), slot 1
-- dynamic (D (cSlot 1)).  Reading `cons (varN 0) (varN 1)` assembles
-- C (S vtrue) (D (cSlot 1)) (a partial-static residual), sound for any runtime
-- store of the form (vtrue · σ).

module Witness where
  storeWit : List AV
  storeWit = S vtrue ∷ D (cSlot 1) ∷ []

  open Core storeWit

  -- the store is consistent with every runtime store whose slot 0 is vtrue.
  consistent : ∀ σ → Consistent storeWit (vtrue · σ)
  consistent σ zero          = refl
  consistent σ (suc zero)    = cSlot-sound 1 (vtrue · σ)
  consistent σ (suc (suc n)) = cSlot-sound (suc (suc n)) (vtrue · σ)

  ex0 : Ex
  ex0 = exCons (varN 0) (varN 1)

  -- the assembled residual is the partial-static  C (S vtrue) (D (cSlot 1)).
  residual : avEval ex0 ≡ C (S vtrue) (D (cSlot 1))
  residual = refl

  -- and it is sound: γ of it on (vtrue · σ) equals the concrete value.
  sound : ∀ σ → γ (avEval ex0) (vtrue · σ) ≡ ⟦ ex0 ⟧ (vtrue · σ)
  sound σ = avEval-sound (vtrue · σ) (consistent σ) ex0
