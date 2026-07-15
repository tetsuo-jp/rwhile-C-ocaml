{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- C2: a COMMAND-LEVEL AV specialiser over the wire AST, with γ-soundness
-- against the big-step semantics of RWhileWireSem — the semantic half of
-- the spec_av bridge for the STATIC-CONTROL fragment (the fp1 regime:
-- conditionals and loops whose tests are static are RESOLVED/UNROLLED;
-- data flows through a partial-static multi-slot store and residualises
-- into straight-line Code — exactly the `loops=0` residuals measured by
-- `measure_proj jones`).
--
-- The specialiser state is a partial-static MULTI-SLOT store σ : List AV
-- (each slot an independent AV; the residual's dynamic input is the
-- single hole cVar).  Per command:
--
--   specAss  reversible XOR update on AVs: a nil slot takes the new AV,
--            assigning a static nil is a no-op, static⊕static is decided
--            NOW by updR; a dynamic update conflict cannot be decided
--            statically and REFUSES (spec_av residualises an update
--            command there — outside this fragment, cf. RWhileOfflineBTA8).
--   specPat  pattern read on AVs (clears slots, builds avCons).
--   specInv  pattern write: C-conses and static conses split statically,
--            a DYNAMIC value splits via avHd/avTl — sound because the
--            theorem is a SUCCESS-simulation: a successful runtime
--            cons-match certifies the value is a cons.
--   specCom  cond: STATIC test → only the live branch is specialised
--            (dead branch dropped — RWhileSimpSound's deadbranch rules);
--            dynamic test → refuse (residual conditionals: OfflineBTA8).
--            loop: unrolled while the EXIT test stays static — exactly
--            RWhileLoopBTA's binding-time rule (a dynamic exit forces
--            residualisation, which this fragment refuses).  The
--            entry/exit ASSERTIONS need no static check: the runtime
--            enforces them, and the theorem only speaks about
--            successful runs.
--
-- HEADLINE (used by C3): the contract of RWhileFutamura3, on the model,
-- for this fragment —
--
--   spec-contract : specProg n p s ≡ just cr →
--                   evalProg m p (s · d) ≡ just w →
--                   ⟦ cr ⟧c d ≡ w
--
-- When the model spec_av specialises p to its static input s (the input
-- slot bound to the partial-static (s . cVar), MKAV's binding-time
-- split), the residual Code computes on the dynamic input d exactly what
-- p computes on (s · d) — for EVERY p, s, d in the fragment.  `--safe`.
------------------------------------------------------------------------

module RWhileSpecCom where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import RWhileAVSound using
  ( Val; ⟨⟩; _·_; hd; tl; vtrue; vfalse; veq; pairp
  ; Code; cVar; cVal; cHd; cTl; cCons; ⟦_⟧c
  ; AV; S; D; C; γ; lift; lift-sound
  ; avCons; avHd; avTl; avEq; avPairp
  ; avCons-sound; avHd-sound; avTl-sound; avEq-sound; avPairp-sound )
open import RWhileH2WorklistAV using
  (Ex; varN; exVal; exCons; exHd; exTl; exEq; exPairp; ⟦_⟧; vNth)
open import RWhileSpecAVWireCom using
  (Pat; pVar; pVal; pCons; Com; cSeq; cAss; cRep; cCond; cLoop; Prog; prog)
open import RWhileWireSem using
  ( isT; beq; vSet; updR; assertB; _>>=_; nothing≢just
  ; evalP; invP; evalC; evalL; evalProg; clearedB )

------------------------------------------------------------------------
-- Maybe plumbing (plain functions, so everything reduces in proofs).

bindM : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindM (just x) f = f x
bindM nothing  f = nothing

mapM : {A B : Set} → (A → B) → Maybe A → Maybe B
mapM f (just x) = just (f x)
mapM f nothing  = nothing

just-inj : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

assertB-just : ∀ b ρ {ρ'} → assertB b ρ ≡ just ρ' → ρ' ≡ ρ
assertB-just true  ρ refl = refl
assertB-just false ρ ()

------------------------------------------------------------------------
-- The partial-static multi-slot store: slot n of σ, defaulting to a
-- static nil beyond the populated prefix (matching vNth's nil default).

nthA : ℕ → List AV → AV
nthA _       []      = S ⟨⟩
nthA zero    (a ∷ _) = a
nthA (suc n) (_ ∷ σ) = nthA n σ

setA : ℕ → AV → List AV → List AV
setA zero    a []      = a ∷ []
setA zero    a (_ ∷ σ) = a ∷ σ
setA (suc n) a []      = S ⟨⟩ ∷ setA n a []
setA (suc n) a (x ∷ σ) = x ∷ setA n a σ

-- runtime store ρ agrees with AV store σ at dynamic input d, slot-wise.
Sim : Val → List AV → Val → Set
Sim ρ σ d = ∀ k → vNth k ρ ≡ γ (nthA k σ) d

------------------------------------------------------------------------
-- get/set laws on both sides, and their Sim consequence.

vNth-set-eq : ∀ n v ρ → vNth n (vSet n v ρ) ≡ v
vNth-set-eq zero    v ρ = refl
vNth-set-eq (suc n) v ρ = vNth-set-eq n v (tl ρ)

vNth-set-neq : ∀ k n v ρ → ¬ (k ≡ n) → vNth k (vSet n v ρ) ≡ vNth k ρ
vNth-set-neq zero    zero    v ρ neq = ⊥-elim (neq refl)
vNth-set-neq zero    (suc n) v ρ neq = refl
vNth-set-neq (suc k) zero    v ρ neq = refl
vNth-set-neq (suc k) (suc n) v ρ neq =
  vNth-set-neq k n v (tl ρ) (λ e → neq (cong suc e))

nthA-set-eq : ∀ n a σ → nthA n (setA n a σ) ≡ a
nthA-set-eq zero    a []      = refl
nthA-set-eq zero    a (_ ∷ _) = refl
nthA-set-eq (suc n) a []      = nthA-set-eq n a []
nthA-set-eq (suc n) a (_ ∷ σ) = nthA-set-eq n a σ

nthA-set-neq : ∀ k n a σ → ¬ (k ≡ n) → nthA k (setA n a σ) ≡ nthA k σ
nthA-set-neq zero    zero    a σ       neq = ⊥-elim (neq refl)
nthA-set-neq zero    (suc n) a []      neq = refl
nthA-set-neq zero    (suc n) a (x ∷ σ) neq = refl
nthA-set-neq (suc k) zero    a []      neq = refl
nthA-set-neq (suc k) zero    a (x ∷ σ) neq = refl
nthA-set-neq (suc k) (suc n) a []      neq =
  nthA-set-neq k n a [] (λ e → neq (cong suc e))
nthA-set-neq (suc k) (suc n) a (x ∷ σ) neq =
  nthA-set-neq k n a σ (λ e → neq (cong suc e))

set-Sim : ∀ {ρ σ d} n {a v} → Sim ρ σ d → γ a d ≡ v →
          Sim (vSet n v ρ) (setA n a σ) d
set-Sim {ρ} {σ} {d} n {a} {v} sim gav k with k ≟ n
... | yes refl =
  trans (vNth-set-eq k v ρ)
        (sym (subst (λ x → γ x d ≡ v) (sym (nthA-set-eq k a σ)) gav))
... | no neq =
  trans (vNth-set-neq k n v ρ neq)
        (trans (sim k) (cong (λ x → γ x d) (sym (nthA-set-neq k n a σ neq))))

------------------------------------------------------------------------
-- Expression specialisation over the multi-slot store (spec_av's
-- SPEC-EXP-AV with a partial-static store; RWhileH2WorklistAV's avEval
-- is its single-slot all-dynamic instance).

specEx : Ex → List AV → AV
specEx (varN n)     σ = nthA n σ
specEx (exVal v)    σ = S v
specEx (exCons a b) σ = avCons (specEx a σ) (specEx b σ)
specEx (exHd e)     σ = avHd (specEx e σ)
specEx (exTl e)     σ = avTl (specEx e σ)
specEx (exEq a b)   σ = avEq (specEx a σ) (specEx b σ)
specEx (exPairp e)  σ = avPairp (specEx e σ)

specEx-sound : ∀ {ρ σ d} → Sim ρ σ d → ∀ e → γ (specEx e σ) d ≡ ⟦ e ⟧ ρ
specEx-sound sim (varN n)  = sym (sim n)
specEx-sound sim (exVal v) = refl
specEx-sound {d = d} sim (exCons a b) =
  trans (avCons-sound (specEx a _) (specEx b _) d)
        (cong₂ _·_ (specEx-sound sim a) (specEx-sound sim b))
specEx-sound {d = d} sim (exHd e) =
  trans (avHd-sound (specEx e _) d) (cong hd (specEx-sound sim e))
specEx-sound {d = d} sim (exTl e) =
  trans (avTl-sound (specEx e _) d) (cong tl (specEx-sound sim e))
specEx-sound {d = d} sim (exEq a b) =
  trans (avEq-sound (specEx a _) (specEx b _) d)
        (cong₂ veq (specEx-sound sim a) (specEx-sound sim b))
specEx-sound {d = d} sim (exPairp e) =
  trans (avPairp-sound (specEx e _) d) (cong pairp (specEx-sound sim e))

------------------------------------------------------------------------
-- Pattern read (evalPat on AVs): total, clears slots, builds avCons.

specPat : Pat → List AV → List AV × AV
specPat (pVar n)    σ = setA n (S ⟨⟩) σ , nthA n σ
specPat (pVal v)    σ = σ , S v
specPat (pCons p q) σ =
  let (σ₁ , a) = specPat p σ
      (σ₂ , b) = specPat q σ₁
  in σ₂ , avCons a b

specPat-sim : ∀ {ρ σ d} → Sim ρ σ d → ∀ p →
  (γ (proj₂ (specPat p σ)) d ≡ proj₂ (evalP p ρ))
  × Sim (proj₁ (evalP p ρ)) (proj₁ (specPat p σ)) d
specPat-sim sim (pVar n) = sym (sim n) , set-Sim n sim refl
specPat-sim sim (pVal v) = refl , sim
specPat-sim {ρ} {σ} {d} sim (pCons p q) =
  let gp   = proj₁ (specPat-sim {ρ} {σ} {d} sim p)
      simp = proj₂ (specPat-sim {ρ} {σ} {d} sim p)
      gq   = proj₁ (specPat-sim {proj₁ (evalP p ρ)} {proj₁ (specPat p σ)} {d} simp q)
      simq = proj₂ (specPat-sim {proj₁ (evalP p ρ)} {proj₁ (specPat p σ)} {d} simp q)
  in trans (avCons-sound (proj₂ (specPat p σ)) _ d) (cong₂ _·_ gp gq) , simq

------------------------------------------------------------------------
-- Pattern write (inv_evalPat on AVs).

specInv : Pat → AV → List AV → Maybe (List AV)
specInv (pVar n) a σ = just (setA n a σ)
specInv (pVal w) a σ = just σ
specInv (pCons p q) (C x y)     σ = bindM (specInv p x σ) (specInv q y)
specInv (pCons p q) (S ⟨⟩)      σ = nothing
specInv (pCons p q) (S (u · w)) σ = bindM (specInv p (S u) σ) (specInv q (S w))
specInv (pCons p q) (D c)       σ =
  bindM (specInv p (D (cHd c)) σ) (specInv q (D (cTl c)))

-- inversion of the runtime pVar write (invP is with-defined; invert here).
invP-var : ∀ n v ρ {ρ'} → invP (pVar n) v ρ ≡ just ρ' → ρ' ≡ vSet n v ρ
invP-var n v ρ rt with vNth n ρ
... | ⟨⟩    = sym (just-inj rt)
... | _ · _ = nothing≢just rt

·-inj₁ : ∀ {a b c d} → (a · b) ≡ (c · d) → a ≡ c
·-inj₁ refl = refl
·-inj₂ : ∀ {a b c d} → (a · b) ≡ (c · d) → b ≡ d
·-inj₂ refl = refl

specInv-sim : ∀ {σ σ' d} p a {v ρ ρ'} → Sim ρ σ d → γ a d ≡ v →
  specInv p a σ ≡ just σ' → invP p v ρ ≡ just ρ' → Sim ρ' σ' d
specInv-sim {σ} {σ'} {d} (pVar n) a {v} {ρ} sim gav sp rt =
  subst₂ (λ x y → Sim x y d) (sym (invP-var n v ρ rt)) (just-inj sp)
         (set-Sim n sim gav)
specInv-sim (pVal w) a {v} {ρ} sim gav sp rt =
  subst₂ (λ x y → Sim x y _) (sym (assertB-just (beq v w) ρ rt)) (just-inj sp)
         sim
specInv-sim (pCons p q) (C x y) {⟨⟩} sim gav sp ()
specInv-sim {σ} {σ'} {d} (pCons p q) (C x y) {v₁ · v₂} {ρ} {ρ'} sim gav sp rt
  with specInv p x σ in eqp
... | nothing = nothing≢just sp
... | just σ₁ with invP p v₁ ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specInv-sim {σ₁} {σ'} {d} q y {v₂} {ρ₁} {ρ'}
          (specInv-sim {σ} {σ₁} {d} p x {v₁} {ρ} {ρ₁} sim (·-inj₁ gav) eqp eqr)
          (·-inj₂ gav) sp rt
specInv-sim (pCons p q) (S ⟨⟩) sim gav () rt
specInv-sim (pCons p q) (S (u · w)) {⟨⟩} sim gav sp ()
specInv-sim {σ} {σ'} {d} (pCons p q) (S (u · w)) {v₁ · v₂} {ρ} {ρ'} sim gav sp rt
  with specInv p (S u) σ in eqp
... | nothing = nothing≢just sp
... | just σ₁ with invP p v₁ ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specInv-sim {σ₁} {σ'} {d} q (S w) {v₂} {ρ₁} {ρ'}
          (specInv-sim {σ} {σ₁} {d} p (S u) {v₁} {ρ} {ρ₁} sim (·-inj₁ gav) eqp eqr)
          (·-inj₂ gav) sp rt
specInv-sim (pCons p q) (D c) {⟨⟩} sim gav sp ()
specInv-sim {σ} {σ'} {d} (pCons p q) (D c) {v₁ · v₂} {ρ} {ρ'} sim gav sp rt
  with specInv p (D (cHd c)) σ in eqp
... | nothing = nothing≢just sp
... | just σ₁ with invP p v₁ ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specInv-sim {σ₁} {σ'} {d} q (D (cTl c)) {v₂} {ρ₁} {ρ'}
          (specInv-sim {σ} {σ₁} {d} p (D (cHd c)) {v₁} {ρ} {ρ₁} sim (cong hd gav) eqp eqr)
          (cong tl gav) sp rt

------------------------------------------------------------------------
-- Reversible XOR update on AVs.

mapS : Maybe Val → Maybe AV
mapS = mapM S

specAss : AV → AV → Maybe AV
specAss (S ⟨⟩)         b             = just b
specAss (S (v₁ · v₂))  (S ⟨⟩)        = just (S (v₁ · v₂))
specAss (D c)          (S ⟨⟩)        = just (D c)
specAss (C x y)        (S ⟨⟩)        = just (C x y)
specAss (S (v₁ · v₂))  (S (w₁ · w₂)) = mapS (updR (v₁ · v₂) (w₁ · w₂))
specAss (S (_ · _))    (D _)         = nothing
specAss (S (_ · _))    (C _ _)       = nothing
specAss (D _)          (S (_ · _))   = nothing
specAss (D _)          (D _)         = nothing
specAss (D _)          (C _ _)       = nothing
specAss (C _ _)        (S (_ · _))   = nothing
specAss (C _ _)        (D _)         = nothing
specAss (C _ _)        (C _ _)       = nothing

updR-nil : ∀ x {u} → updR x ⟨⟩ ≡ just u → x ≡ u
updR-nil ⟨⟩      refl = refl
updR-nil (a · b) refl = refl

specAss-sim : ∀ a b {c cur v u d} → specAss a b ≡ just c →
  γ a d ≡ cur → γ b d ≡ v → updR cur v ≡ just u → γ c d ≡ u
specAss-sim (S ⟨⟩) b refl refl gbv refl = gbv
specAss-sim (S (v₁ · v₂)) (S ⟨⟩) refl refl refl refl = refl
specAss-sim (D c₀)  (S ⟨⟩) refl refl refl ru = updR-nil _ ru
specAss-sim (C x y) (S ⟨⟩) refl refl refl refl = refl
specAss-sim (S (v₁ · v₂)) (S (w₁ · w₂)) sp refl refl ru
  with updR (v₁ · v₂) (w₁ · w₂)
specAss-sim (S (v₁ · v₂)) (S (w₁ · w₂)) sp refl refl ru | just u′
  with sp | ru
... | refl | refl = refl
specAss-sim (S (v₁ · v₂)) (S (w₁ · w₂)) () refl refl ru | nothing
specAss-sim (S (_ · _)) (D _)       () _ _ _
specAss-sim (S (_ · _)) (C _ _)     () _ _ _
specAss-sim (D _)       (S (_ · _)) () _ _ _
specAss-sim (D _)       (D _)       () _ _ _
specAss-sim (D _)       (C _ _)     () _ _ _
specAss-sim (C _ _)     (S (_ · _)) () _ _ _
specAss-sim (C _ _)     (D _)       () _ _ _
specAss-sim (C _ _)     (C _ _)     () _ _ _

------------------------------------------------------------------------
-- Command specialisation: static control resolved/unrolled, data flow
-- residualised in the slots.

specCom  : ℕ → Com → List AV → Maybe (List AV)
specCond : ℕ → Com → Com → List AV → AV → Maybe (List AV)
specL    : ℕ → Com → Com → Ex → List AV → Maybe (List AV)
specLf   : ℕ → Com → Com → Ex → List AV → AV → Maybe (List AV)

specCom zero    _ _ = nothing
specCom (suc n) (cSeq a b) σ = bindM (specCom n a σ) (specCom n b)
specCom (suc n) (cAss k e) σ =
  mapM (λ a → setA k a σ) (specAss (nthA k σ) (specEx e σ))
specCom (suc n) (cRep q r) σ =
  specInv q (proj₂ (specPat r σ)) (proj₁ (specPat r σ))
specCom (suc n) (cCond e t el f) σ = specCond n t el σ (specEx e σ)
specCom (suc n) (cLoop e d l f) σ =
  bindM (specCom n d σ) (specL n d l f)

specCond n t el σ (S v)   = specCom n (if isT v then t else el) σ
specCond n t el σ (D _)   = nothing
specCond n t el σ (C _ _) = nothing

specL zero    _ _ _ _ = nothing
specL (suc n) d l f σ = specLf n d l f σ (specEx f σ)

specLf n d l f σ (S v) =
  if isT v then just σ
  else bindM (specCom n l σ)
             (λ σ₁ → bindM (specCom n d σ₁) (specL n d l f))
specLf n d l f σ (D _)   = nothing
specLf n d l f σ (C _ _) = nothing

------------------------------------------------------------------------
-- Success-simulation: when the specialiser commits (just σ') and the
-- interpreter succeeds on an agreeing runtime store, the results agree.

private
  if-branch : ∀ {x v : Val} {A B r : Maybe Val} → x ≡ v →
              (if isT x then A else B) ≡ r → (if isT v then A else B) ≡ r
  if-branch refl h = h

specCom-sim : ∀ {n m} c {σ σ' ρ ρ' dyn} →
  specCom n c σ ≡ just σ' → evalC m c ρ ≡ just ρ' →
  Sim ρ σ dyn → Sim ρ' σ' dyn
specL-sim : ∀ {n m} d l f {e σ σ' ρ ρ' dyn} →
  specL n d l f σ ≡ just σ' → evalL m e d l f ρ ≡ just ρ' →
  Sim ρ σ dyn → Sim ρ' σ' dyn

specCom-sim {zero} c sp rt sim = nothing≢just sp
specCom-sim {suc n} {zero} c sp rt sim = nothing≢just rt
specCom-sim {suc n} {suc m} (cSeq a b) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specCom n a σ in eqs
... | nothing = nothing≢just sp
... | just σ₁ with evalC m a ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specCom-sim {n} {m} b {σ₁} {σ'} {ρ₁} {ρ'} {dyn} sp rt
          (specCom-sim {n} {m} a {σ} {σ₁} {ρ} {ρ₁} {dyn} eqs eqr sim)
specCom-sim {suc n} {suc m} (cAss k e) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specAss (nthA k σ) (specEx e σ) in eqa
... | nothing = nothing≢just sp
... | just a with updR (vNth k ρ) (⟦ e ⟧ ρ) in equ
...   | nothing = nothing≢just rt
...   | just u =
        subst₂ (λ x y → Sim x y dyn) (just-inj rt) (just-inj sp)
          (set-Sim k sim
            (specAss-sim (nthA k σ) (specEx e σ) eqa
              (sym (sim k)) (specEx-sound sim e) equ))
specCom-sim {suc n} {suc m} (cRep q r) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim =
  specInv-sim {proj₁ (specPat r σ)} {σ'} {dyn} q (proj₂ (specPat r σ))
    {proj₂ (evalP r ρ)} {proj₁ (evalP r ρ)} {ρ'}
    (proj₂ (specPat-sim {ρ} {σ} {dyn} sim r))
    (proj₁ (specPat-sim {ρ} {σ} {dyn} sim r)) sp rt
specCom-sim {suc n} {suc m} (cCond e t el f) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specEx e σ in eqe
... | D _   = nothing≢just sp
... | C _ _ = nothing≢just sp
... | S v = cond-case sp (if-branch eveq rt)
  where
  eveq : ⟦ e ⟧ ρ ≡ v
  eveq = trans (sym (specEx-sound sim e)) (cong (λ x → γ x dyn) eqe)
  cond-case :
    specCom n (if isT v then t else el) σ ≡ just σ' →
    (if isT v
     then (evalC m t ρ >>= λ ρ₁ → assertB (isT (⟦ f ⟧ ρ₁)) ρ₁)
     else (evalC m el ρ >>= λ ρ₁ → assertB (not (isT (⟦ f ⟧ ρ₁))) ρ₁))
      ≡ just ρ' →
    Sim ρ' σ' dyn
  cond-case sp' rt' with isT v
  cond-case sp' rt' | true with evalC m t ρ in eqr
  ... | nothing = nothing≢just rt'
  ... | just ρ₁ =
        subst (λ x → Sim x σ' dyn)
          (sym (assertB-just (isT (⟦ f ⟧ ρ₁)) ρ₁ rt'))
          (specCom-sim {n} {m} t {σ} {σ'} {ρ} {ρ₁} {dyn} sp' eqr sim)
  cond-case sp' rt' | false with evalC m el ρ in eqr
  ... | nothing = nothing≢just rt'
  ... | just ρ₁ =
        subst (λ x → Sim x σ' dyn)
          (sym (assertB-just (not (isT (⟦ f ⟧ ρ₁))) ρ₁ rt'))
          (specCom-sim {n} {m} el {σ} {σ'} {ρ} {ρ₁} {dyn} sp' eqr sim)
specCom-sim {suc n} {suc m} (cLoop e d l f) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with isT (⟦ e ⟧ ρ)
... | false = nothing≢just rt
... | true with specCom n d σ in eqs
...   | nothing = nothing≢just sp
...   | just σ₁ with evalC m d ρ in eqr
...     | nothing = nothing≢just rt
...     | just ρ₁ =
          specL-sim {n} {m} d l f {e} {σ₁} {σ'} {ρ₁} {ρ'} {dyn} sp rt
            (specCom-sim {n} {m} d {σ} {σ₁} {ρ} {ρ₁} {dyn} eqs eqr sim)

specL-sim {zero} d l f sp rt sim = nothing≢just sp
specL-sim {suc n} {zero} d l f sp rt sim = nothing≢just rt
specL-sim {suc n} {suc m} d l f {e} {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specEx f σ in eqf
... | D _   = nothing≢just sp
... | C _ _ = nothing≢just sp
... | S v = loop-case sp (if-branch feq rt)
  where
  feq : ⟦ f ⟧ ρ ≡ v
  feq = trans (sym (specEx-sound sim f)) (cong (λ x → γ x dyn) eqf)
  loop-case :
    (if isT v then just σ
     else bindM (specCom n l σ)
                (λ σ₁ → bindM (specCom n d σ₁) (specL n d l f)))
      ≡ just σ' →
    (if isT v then just ρ
     else (evalC m l ρ >>= λ ρ₁ →
           if isT (⟦ e ⟧ ρ₁) then nothing
           else (evalC m d ρ₁ >>= evalL m e d l f)))
      ≡ just ρ' →
    Sim ρ' σ' dyn
  loop-case sp' rt' with isT v
  loop-case sp' rt' | true =
    subst₂ (λ x y → Sim x y dyn) (just-inj rt') (just-inj sp') sim
  loop-case sp' rt' | false with specCom n l σ in eqsl
  ... | nothing = nothing≢just sp'
  ... | just σ₁ with evalC m l ρ in eqrl
  ...   | nothing = nothing≢just rt'
  ...   | just ρ₁ with isT (⟦ e ⟧ ρ₁)
  ...     | true = nothing≢just rt'
  ...     | false with specCom n d σ₁ in eqsd
  ...       | nothing = nothing≢just sp'
  ...       | just σ₂ with evalC m d ρ₁ in eqrd
  ...         | nothing = nothing≢just rt'
  ...         | just ρ₂ =
                specL-sim {n} {m} d l f {e} {σ₂} {σ'} {ρ₂} {ρ'} {dyn} sp' rt'
                  (specCom-sim {n} {m} d {σ₁} {σ₂} {ρ₁} {ρ₂} {dyn} eqsd eqrd
                     (specCom-sim {n} {m} l {σ} {σ₁} {ρ} {ρ₁} {dyn} eqsl eqrl sim))

------------------------------------------------------------------------
-- HEADLINE: the model contract, for the static-control fragment.
-- specProg mirrors spec_av's setup: the source's input slot is bound to
-- the partial-static (static-s . dynamic-input) pair — MKAV's binding-
-- time split — and the residual is the OUTPUT slot's AV, lifted to Code.

emptyσ : List AV
emptyσ = []

specProg : ℕ → Prog → Val → Maybe Code
specProg n (prog i c j) s =
  mapM (λ σ → lift (nthA j σ))
       (specCom n c (setA i (avCons (S s) (D cVar)) emptyσ))

init-Sim : ∀ i s d → Sim (vSet i (s · d) ⟨⟩) (setA i (avCons (S s) (D cVar)) emptyσ) d
init-Sim i s d k with k ≟ i
... | yes refl
  rewrite nthA-set-eq k (avCons (S s) (D cVar)) emptyσ = vNth-set-eq k (s · d) ⟨⟩
... | no neq
  rewrite nthA-set-neq k i (avCons (S s) (D cVar)) emptyσ neq =
  trans (vNth-set-neq k i (s · d) ⟨⟩ neq) (vNth-nil k)
  where
  vNth-nil : ∀ k → vNth k ⟨⟩ ≡ ⟨⟩
  vNth-nil zero    = refl
  vNth-nil (suc k) = vNth-nil k

spec-contract : ∀ {n m} p s {d w cr} →
  specProg n p s ≡ just cr →
  evalProg m p (s · d) ≡ just w →
  ⟦ cr ⟧c d ≡ w
spec-contract {n} {m} (prog i c j) s {d} {w} {cr} sp rt
  with specCom n c (setA i (avCons (S s) (D cVar)) emptyσ) in eqs
... | nothing = nothing≢just sp
... | just σ with evalC m c (vSet i (s · d) ⟨⟩) in eqr
...   | nothing = nothing≢just rt
...   | just ρ = final sp rt
  where
  simρ : Sim ρ σ d
  simρ = specCom-sim {n} {m} c
           {setA i (avCons (S s) (D cVar)) emptyσ} {σ}
           {vSet i (s · d) ⟨⟩} {ρ} {d}
           eqs eqr (init-Sim i s d)
  final : just (lift (nthA j σ)) ≡ just cr →
          assertB (clearedB (vSet j ⟨⟩ ρ)) (vNth j ρ) ≡ just w →
          ⟦ cr ⟧c d ≡ w
  final sp' rt' with clearedB (vSet j ⟨⟩ ρ)
  final refl refl | true = trans (lift-sound (nthA j σ) d) (sym (simρ j))
  final sp'  ()   | false

------------------------------------------------------------------------
-- Witness (test-first check): specialising the 2-CRep SWAP program of
-- RWhileWireSem.Examples w.r.t. static s = vtrue residualises to the
-- straight-line Code (cons dynamic-input (quoted vtrue)) — the
-- interpreter-free, Futamura-gain residual — checked by refl, and the
-- contract instance computes on both sides.

module Witness where

  swapP : Prog
  swapP = prog 0 (cSeq (cRep (pCons (pVar 1) (pVar 2)) (pVar 0))
                       (cRep (pVar 0) (pCons (pVar 2) (pVar 1)))) 0

  -- residual: d ↦ (d · vtrue), the static s baked in, no interpretation.
  resid : specProg 10 swapP vtrue ≡ just (cCons cVar (cVal vtrue))
  resid = refl

  -- the contract instance by computation: [p]((s·d)) = (d·s) and the
  -- residual computes the same.
  run-src : ∀ d → evalProg 10 swapP (vtrue · d) ≡ just (d · vtrue)
  run-src d = refl

  run-resid : ∀ d → ⟦ cCons cVar (cVal vtrue) ⟧c d ≡ (d · vtrue)
  run-resid d = refl
