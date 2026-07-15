{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- C2-dyn: the command-level AV specialiser EXTENDED WITH DYNAMIC
-- CONDITIONALS — the first step past RWhileSpecCom's static-control
-- fragment, following RWhileOfflineBTA8's rule: a dynamic conditional
-- must keep BOTH branches (dropping one is the branch-collapse bug,
-- specBug-wrong / a reversibility violation, OfflineBTA9).
--
-- RWhileSpecCom's residuals live in RWhileAVSound.Code, which has no
-- conditional, so a dynamic test had to refuse.  Here the residual
-- language RC adds `rIf`, and a dynamic conditional is specialised by
-- running the specialiser down BOTH branches and JOINING the resulting
-- AV stores POINTWISE:
--
--   slot k of (join tc σt σe)  =  DD (rIf tc (lift σt[k]) (lift σe[k]))
--
-- — a per-slot conditional expression instead of spec_av's residual
-- conditional COMMAND (same meaning, expression-level; the command-level
-- emission is the production O3 item).  Soundness stays a SUCCESS-
-- simulation: the runtime takes one branch, and γ of the joined slot
-- reduces to that branch's value because the test code tc means exactly
-- the runtime test (specExD-sound).  A partial-static-cons test (CD) is
-- statically TRUTHY (a cons is true), so it resolves to the then-branch
-- — the avPairp trick at control level.
--
-- Loops still require a static exit (RWhileLoopBTA: a dynamic exit
-- forces a residual LOOP, which has no expression-level counterpart —
-- that is the production O1 path, implemented in spec_av_bti.rwhile).
--
-- HEADLINE: spec-contract-dyn, same shape as RWhileSpecCom's:
--   specProgD n p s ≡ just cr → evalProg m p (s·d) ≡ just w → ⟦cr⟧r d ≡ w
-- now covering programs whose CONTROL depends on the dynamic input.
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileSpecComDyn where

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
open import RWhileAVSound using (Val; ⟨⟩; _·_; hd; tl; vtrue; vfalse; veq; pairp)
open import RWhileH2WorklistAV using
  (Ex; varN; exVal; exCons; exHd; exTl; exEq; exPairp; ⟦_⟧; vNth)
open import RWhileSpecAVWireCom using
  (Pat; pVar; pVal; pCons; Com; cSeq; cAss; cRep; cCond; cLoop; Prog; prog)
open import RWhileWireSem using
  ( isT; beq; vSet; updR; assertB; _>>=_; nothing≢just
  ; evalP; invP; evalC; evalL; evalProg; clearedB )
open import RWhileSpecCom using
  ( bindM; mapM; just-inj; assertB-just
  ; vNth-set-eq; vNth-set-neq; updR-nil; ·-inj₁; ·-inj₂ )

------------------------------------------------------------------------
-- Residual code with a CONDITIONAL, and its semantics.

data RC : Set where
  rVar   : RC
  rVal   : Val → RC
  rHd    : RC → RC
  rTl    : RC → RC
  rCons  : RC → RC → RC
  rEq    : RC → RC → RC
  rPairp : RC → RC
  rIf    : RC → RC → RC → RC          -- NEW: the residual conditional

⟦_⟧r : RC → Val → Val
⟦ rVar      ⟧r d = d
⟦ rVal v    ⟧r d = v
⟦ rHd c     ⟧r d = hd (⟦ c ⟧r d)
⟦ rTl c     ⟧r d = tl (⟦ c ⟧r d)
⟦ rCons a b ⟧r d = (⟦ a ⟧r d) · (⟦ b ⟧r d)
⟦ rEq a b   ⟧r d = veq (⟦ a ⟧r d) (⟦ b ⟧r d)
⟦ rPairp c  ⟧r d = pairp (⟦ c ⟧r d)
⟦ rIf c a b ⟧r d = if isT (⟦ c ⟧r d) then ⟦ a ⟧r d else ⟦ b ⟧r d

------------------------------------------------------------------------
-- Annotated values over RC (the AV algebra, verbatim from RWhileAVSound
-- but with the richer code type).

data AVD : Set where
  SD : Val → AVD
  DD : RC → AVD
  CD : AVD → AVD → AVD

γd : AVD → Val → Val
γd (SD v)   d = v
γd (DD c)   d = ⟦ c ⟧r d
γd (CD a b) d = (γd a d) · (γd b d)

liftd : AVD → RC
liftd (SD v)   = rVal v
liftd (DD c)   = c
liftd (CD a b) = rCons (liftd a) (liftd b)

liftd-sound : ∀ a d → ⟦ liftd a ⟧r d ≡ γd a d
liftd-sound (SD v)   d = refl
liftd-sound (DD c)   d = refl
liftd-sound (CD a b) d = cong₂ _·_ (liftd-sound a d) (liftd-sound b d)

avdHd : AVD → AVD
avdHd (SD v)   = SD (hd v)
avdHd (CD a _) = a
avdHd (DD c)   = DD (rHd c)

avdHd-sound : ∀ a d → γd (avdHd a) d ≡ hd (γd a d)
avdHd-sound (SD v)   d = refl
avdHd-sound (CD a b) d = refl
avdHd-sound (DD c)   d = refl

avdTl : AVD → AVD
avdTl (SD v)   = SD (tl v)
avdTl (CD _ b) = b
avdTl (DD c)   = DD (rTl c)

avdTl-sound : ∀ a d → γd (avdTl a) d ≡ tl (γd a d)
avdTl-sound (SD v)   d = refl
avdTl-sound (CD a b) d = refl
avdTl-sound (DD c)   d = refl

avdCons : AVD → AVD → AVD
avdCons (SD v₁)  (SD v₂) = SD (v₁ · v₂)
avdCons (SD x)   (DD y)  = CD (SD x) (DD y)
avdCons (SD x)   (CD y z) = CD (SD x) (CD y z)
avdCons (DD x)   b       = CD (DD x) b
avdCons (CD x y) b       = CD (CD x y) b

avdCons-sound : ∀ a b d → γd (avdCons a b) d ≡ (γd a d) · (γd b d)
avdCons-sound (SD v₁)  (SD v₂)  d = refl
avdCons-sound (SD x)   (DD y)   d = refl
avdCons-sound (SD x)   (CD y z) d = refl
avdCons-sound (DD x)   b        d = refl
avdCons-sound (CD x y) b        d = refl

avdEq : AVD → AVD → AVD
avdEq (SD v₁)  (SD v₂)  = SD (veq v₁ v₂)
avdEq (SD x)   (DD y)   = DD (rEq (liftd (SD x)) (liftd (DD y)))
avdEq (SD x)   (CD y z) = DD (rEq (liftd (SD x)) (liftd (CD y z)))
avdEq (DD x)   b        = DD (rEq (liftd (DD x)) (liftd b))
avdEq (CD x y) b        = DD (rEq (liftd (CD x y)) (liftd b))

avdEq-sound : ∀ a b d → γd (avdEq a b) d ≡ veq (γd a d) (γd b d)
avdEq-sound (SD v₁)  (SD v₂)  d = refl
avdEq-sound (SD x)   (DD y)   d = cong₂ veq (liftd-sound (SD x) d)   (liftd-sound (DD y) d)
avdEq-sound (SD x)   (CD y z) d = cong₂ veq (liftd-sound (SD x) d)   (liftd-sound (CD y z) d)
avdEq-sound (DD x)   b        d = cong₂ veq (liftd-sound (DD x) d)   (liftd-sound b d)
avdEq-sound (CD x y) b        d = cong₂ veq (liftd-sound (CD x y) d) (liftd-sound b d)

avdPairp : AVD → AVD
avdPairp (SD v)   = SD (pairp v)
avdPairp (CD _ _) = SD vtrue
avdPairp (DD c)   = DD (rPairp c)

avdPairp-sound : ∀ a d → γd (avdPairp a) d ≡ pairp (γd a d)
avdPairp-sound (SD v)   d = refl
avdPairp-sound (CD a b) d = refl
avdPairp-sound (DD c)   d = refl

------------------------------------------------------------------------
-- Multi-slot store over AVD, get/set laws, Sim.

nthAD : ℕ → List AVD → AVD
nthAD _       []      = SD ⟨⟩
nthAD zero    (a ∷ _) = a
nthAD (suc n) (_ ∷ σ) = nthAD n σ

setAD : ℕ → AVD → List AVD → List AVD
setAD zero    a []      = a ∷ []
setAD zero    a (_ ∷ σ) = a ∷ σ
setAD (suc n) a []      = SD ⟨⟩ ∷ setAD n a []
setAD (suc n) a (x ∷ σ) = x ∷ setAD n a σ

nthAD-set-eq : ∀ n a σ → nthAD n (setAD n a σ) ≡ a
nthAD-set-eq zero    a []      = refl
nthAD-set-eq zero    a (_ ∷ _) = refl
nthAD-set-eq (suc n) a []      = nthAD-set-eq n a []
nthAD-set-eq (suc n) a (_ ∷ σ) = nthAD-set-eq n a σ

nthAD-set-neq : ∀ k n a σ → ¬ (k ≡ n) → nthAD k (setAD n a σ) ≡ nthAD k σ
nthAD-set-neq zero    zero    a σ       neq = ⊥-elim (neq refl)
nthAD-set-neq zero    (suc n) a []      neq = refl
nthAD-set-neq zero    (suc n) a (x ∷ σ) neq = refl
nthAD-set-neq (suc k) zero    a []      neq = refl
nthAD-set-neq (suc k) zero    a (x ∷ σ) neq = refl
nthAD-set-neq (suc k) (suc n) a []      neq =
  nthAD-set-neq k n a [] (λ e → neq (cong suc e))
nthAD-set-neq (suc k) (suc n) a (x ∷ σ) neq =
  nthAD-set-neq k n a σ (λ e → neq (cong suc e))

SimD : Val → List AVD → Val → Set
SimD ρ σ d = ∀ k → vNth k ρ ≡ γd (nthAD k σ) d

set-SimD : ∀ {ρ σ d} n {a v} → SimD ρ σ d → γd a d ≡ v →
           SimD (vSet n v ρ) (setAD n a σ) d
set-SimD {ρ} {σ} {d} n {a} {v} sim gav k with k ≟ n
... | yes refl =
  trans (vNth-set-eq k v ρ)
        (sym (subst (λ x → γd x d ≡ v) (sym (nthAD-set-eq k a σ)) gav))
... | no neq =
  trans (vNth-set-neq k n v ρ neq)
        (trans (sim k) (cong (λ x → γd x d) (sym (nthAD-set-neq k n a σ neq))))

------------------------------------------------------------------------
-- Expression / pattern / assignment specialisation (as RWhileSpecCom,
-- over AVD).

specExD : Ex → List AVD → AVD
specExD (varN n)     σ = nthAD n σ
specExD (exVal v)    σ = SD v
specExD (exCons a b) σ = avdCons (specExD a σ) (specExD b σ)
specExD (exHd e)     σ = avdHd (specExD e σ)
specExD (exTl e)     σ = avdTl (specExD e σ)
specExD (exEq a b)   σ = avdEq (specExD a σ) (specExD b σ)
specExD (exPairp e)  σ = avdPairp (specExD e σ)

specExD-sound : ∀ {ρ σ d} → SimD ρ σ d → ∀ e → γd (specExD e σ) d ≡ ⟦ e ⟧ ρ
specExD-sound sim (varN n)  = sym (sim n)
specExD-sound sim (exVal v) = refl
specExD-sound {d = d} sim (exCons a b) =
  trans (avdCons-sound (specExD a _) (specExD b _) d)
        (cong₂ _·_ (specExD-sound sim a) (specExD-sound sim b))
specExD-sound {d = d} sim (exHd e) =
  trans (avdHd-sound (specExD e _) d) (cong hd (specExD-sound sim e))
specExD-sound {d = d} sim (exTl e) =
  trans (avdTl-sound (specExD e _) d) (cong tl (specExD-sound sim e))
specExD-sound {d = d} sim (exEq a b) =
  trans (avdEq-sound (specExD a _) (specExD b _) d)
        (cong₂ veq (specExD-sound sim a) (specExD-sound sim b))
specExD-sound {d = d} sim (exPairp e) =
  trans (avdPairp-sound (specExD e _) d) (cong pairp (specExD-sound sim e))

specPatD : Pat → List AVD → List AVD × AVD
specPatD (pVar n)    σ = setAD n (SD ⟨⟩) σ , nthAD n σ
specPatD (pVal v)    σ = σ , SD v
specPatD (pCons p q) σ =
  let (σ₁ , a) = specPatD p σ
      (σ₂ , b) = specPatD q σ₁
  in σ₂ , avdCons a b

specPatD-sim : ∀ {ρ σ d} → SimD ρ σ d → ∀ p →
  (γd (proj₂ (specPatD p σ)) d ≡ proj₂ (evalP p ρ))
  × SimD (proj₁ (evalP p ρ)) (proj₁ (specPatD p σ)) d
specPatD-sim sim (pVar n) = sym (sim n) , set-SimD n sim refl
specPatD-sim sim (pVal v) = refl , sim
specPatD-sim {ρ} {σ} {d} sim (pCons p q) =
  let gp   = proj₁ (specPatD-sim {ρ} {σ} {d} sim p)
      simp = proj₂ (specPatD-sim {ρ} {σ} {d} sim p)
      gq   = proj₁ (specPatD-sim {proj₁ (evalP p ρ)} {proj₁ (specPatD p σ)} {d} simp q)
      simq = proj₂ (specPatD-sim {proj₁ (evalP p ρ)} {proj₁ (specPatD p σ)} {d} simp q)
  in trans (avdCons-sound (proj₂ (specPatD p σ)) _ d) (cong₂ _·_ gp gq) , simq

specInvD : Pat → AVD → List AVD → Maybe (List AVD)
specInvD (pVar n) a σ = just (setAD n a σ)
specInvD (pVal w) a σ = just σ
specInvD (pCons p q) (CD x y)     σ = bindM (specInvD p x σ) (specInvD q y)
specInvD (pCons p q) (SD ⟨⟩)      σ = nothing
specInvD (pCons p q) (SD (u · w)) σ = bindM (specInvD p (SD u) σ) (specInvD q (SD w))
specInvD (pCons p q) (DD c)       σ =
  bindM (specInvD p (DD (rHd c)) σ) (specInvD q (DD (rTl c)))

invP-var : ∀ n v ρ {ρ'} → invP (pVar n) v ρ ≡ just ρ' → ρ' ≡ vSet n v ρ
invP-var n v ρ rt with vNth n ρ
... | ⟨⟩    = sym (just-inj rt)
... | _ · _ = nothing≢just rt

specInvD-sim : ∀ {σ σ' d} p a {v ρ ρ'} → SimD ρ σ d → γd a d ≡ v →
  specInvD p a σ ≡ just σ' → invP p v ρ ≡ just ρ' → SimD ρ' σ' d
specInvD-sim {σ} {σ'} {d} (pVar n) a {v} {ρ} sim gav sp rt =
  subst₂ (λ x y → SimD x y d) (sym (invP-var n v ρ rt)) (just-inj sp)
         (set-SimD n sim gav)
specInvD-sim (pVal w) a {v} {ρ} sim gav sp rt =
  subst₂ (λ x y → SimD x y _) (sym (assertB-just (beq v w) ρ rt)) (just-inj sp)
         sim
specInvD-sim (pCons p q) (CD x y) {⟨⟩} sim gav sp ()
specInvD-sim {σ} {σ'} {d} (pCons p q) (CD x y) {v₁ · v₂} {ρ} {ρ'} sim gav sp rt
  with specInvD p x σ in eqp
... | nothing = nothing≢just sp
... | just σ₁ with invP p v₁ ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specInvD-sim {σ₁} {σ'} {d} q y {v₂} {ρ₁} {ρ'}
          (specInvD-sim {σ} {σ₁} {d} p x {v₁} {ρ} {ρ₁} sim (·-inj₁ gav) eqp eqr)
          (·-inj₂ gav) sp rt
specInvD-sim (pCons p q) (SD ⟨⟩) sim gav () rt
specInvD-sim (pCons p q) (SD (u · w)) {⟨⟩} sim gav sp ()
specInvD-sim {σ} {σ'} {d} (pCons p q) (SD (u · w)) {v₁ · v₂} {ρ} {ρ'} sim gav sp rt
  with specInvD p (SD u) σ in eqp
... | nothing = nothing≢just sp
... | just σ₁ with invP p v₁ ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specInvD-sim {σ₁} {σ'} {d} q (SD w) {v₂} {ρ₁} {ρ'}
          (specInvD-sim {σ} {σ₁} {d} p (SD u) {v₁} {ρ} {ρ₁} sim (·-inj₁ gav) eqp eqr)
          (·-inj₂ gav) sp rt
specInvD-sim (pCons p q) (DD c) {⟨⟩} sim gav sp ()
specInvD-sim {σ} {σ'} {d} (pCons p q) (DD c) {v₁ · v₂} {ρ} {ρ'} sim gav sp rt
  with specInvD p (DD (rHd c)) σ in eqp
... | nothing = nothing≢just sp
... | just σ₁ with invP p v₁ ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specInvD-sim {σ₁} {σ'} {d} q (DD (rTl c)) {v₂} {ρ₁} {ρ'}
          (specInvD-sim {σ} {σ₁} {d} p (DD (rHd c)) {v₁} {ρ} {ρ₁} sim (cong hd gav) eqp eqr)
          (cong tl gav) sp rt

mapSD : Maybe Val → Maybe AVD
mapSD = mapM SD

specAssD : AVD → AVD → Maybe AVD
specAssD (SD ⟨⟩)         b              = just b
specAssD (SD (v₁ · v₂))  (SD ⟨⟩)        = just (SD (v₁ · v₂))
specAssD (DD c)          (SD ⟨⟩)        = just (DD c)
specAssD (CD x y)        (SD ⟨⟩)        = just (CD x y)
specAssD (SD (v₁ · v₂))  (SD (w₁ · w₂)) = mapSD (updR (v₁ · v₂) (w₁ · w₂))
specAssD (SD (_ · _))    (DD _)         = nothing
specAssD (SD (_ · _))    (CD _ _)       = nothing
specAssD (DD _)          (SD (_ · _))   = nothing
specAssD (DD _)          (DD _)         = nothing
specAssD (DD _)          (CD _ _)       = nothing
specAssD (CD _ _)        (SD (_ · _))   = nothing
specAssD (CD _ _)        (DD _)         = nothing
specAssD (CD _ _)        (CD _ _)       = nothing

specAssD-sim : ∀ a b {c cur v u d} → specAssD a b ≡ just c →
  γd a d ≡ cur → γd b d ≡ v → updR cur v ≡ just u → γd c d ≡ u
specAssD-sim (SD ⟨⟩) b refl refl gbv refl = gbv
specAssD-sim (SD (v₁ · v₂)) (SD ⟨⟩) refl refl refl refl = refl
specAssD-sim (DD c₀)  (SD ⟨⟩) refl refl refl ru = updR-nil _ ru
specAssD-sim (CD x y) (SD ⟨⟩) refl refl refl refl = refl
specAssD-sim (SD (v₁ · v₂)) (SD (w₁ · w₂)) sp refl refl ru
  with updR (v₁ · v₂) (w₁ · w₂)
specAssD-sim (SD (v₁ · v₂)) (SD (w₁ · w₂)) sp refl refl ru | just u′
  with sp | ru
... | refl | refl = refl
specAssD-sim (SD (v₁ · v₂)) (SD (w₁ · w₂)) () refl refl ru | nothing
specAssD-sim (SD (_ · _)) (DD _)       () _ _ _
specAssD-sim (SD (_ · _)) (CD _ _)     () _ _ _
specAssD-sim (DD _)       (SD (_ · _)) () _ _ _
specAssD-sim (DD _)       (DD _)       () _ _ _
specAssD-sim (DD _)       (CD _ _)     () _ _ _
specAssD-sim (CD _ _)     (SD (_ · _)) () _ _ _
specAssD-sim (CD _ _)     (DD _)       () _ _ _
specAssD-sim (CD _ _)     (CD _ _)     () _ _ _

------------------------------------------------------------------------
-- The pointwise store JOIN for a dynamic conditional.

joinAV : RC → AVD → AVD → AVD
joinAV tc x y = DD (rIf tc (liftd x) (liftd y))

joinσ : RC → List AVD → List AVD → List AVD
joinσ tc []       []       = []
joinσ tc (x ∷ xs) []       = joinAV tc x (SD ⟨⟩) ∷ joinσ tc xs []
joinσ tc []       (y ∷ ys) = joinAV tc (SD ⟨⟩) y ∷ joinσ tc [] ys
joinσ tc (x ∷ xs) (y ∷ ys) = joinAV tc x y ∷ joinσ tc xs ys

-- when the test is TRUE at d, the joined store means the then-store …
joinσ-γ-t : ∀ {tc d} → isT (⟦ tc ⟧r d) ≡ true → ∀ σt σe k →
  γd (nthAD k (joinσ tc σt σe)) d ≡ γd (nthAD k σt) d
joinσ-γ-t {tc} {d} eq [] [] k = refl
joinσ-γ-t {tc} {d} eq (x ∷ xs) [] zero
  rewrite eq = liftd-sound x d
joinσ-γ-t {tc} {d} eq (x ∷ xs) [] (suc k) = joinσ-γ-t eq xs [] k
joinσ-γ-t {tc} {d} eq [] (y ∷ ys) zero
  rewrite eq = refl
joinσ-γ-t {tc} {d} eq [] (y ∷ ys) (suc k) = joinσ-γ-t eq [] ys k
joinσ-γ-t {tc} {d} eq (x ∷ xs) (y ∷ ys) zero
  rewrite eq = liftd-sound x d
joinσ-γ-t {tc} {d} eq (x ∷ xs) (y ∷ ys) (suc k) = joinσ-γ-t eq xs ys k

-- … and when FALSE, the else-store.
joinσ-γ-f : ∀ {tc d} → isT (⟦ tc ⟧r d) ≡ false → ∀ σt σe k →
  γd (nthAD k (joinσ tc σt σe)) d ≡ γd (nthAD k σe) d
joinσ-γ-f {tc} {d} eq [] [] k = refl
joinσ-γ-f {tc} {d} eq (x ∷ xs) [] zero
  rewrite eq = refl
joinσ-γ-f {tc} {d} eq (x ∷ xs) [] (suc k) = joinσ-γ-f eq xs [] k
joinσ-γ-f {tc} {d} eq [] (y ∷ ys) zero
  rewrite eq = liftd-sound y d
joinσ-γ-f {tc} {d} eq [] (y ∷ ys) (suc k) = joinσ-γ-f eq [] ys k
joinσ-γ-f {tc} {d} eq (x ∷ xs) (y ∷ ys) zero
  rewrite eq = liftd-sound y d
joinσ-γ-f {tc} {d} eq (x ∷ xs) (y ∷ ys) (suc k) = joinσ-γ-f eq xs ys k

------------------------------------------------------------------------
-- Command specialisation with DYNAMIC conditionals.

specComD  : ℕ → Com → List AVD → Maybe (List AVD)
specCondD : ℕ → Com → Com → List AVD → AVD → Maybe (List AVD)
specLD    : ℕ → Com → Com → Ex → List AVD → Maybe (List AVD)
specLfD   : ℕ → Com → Com → Ex → List AVD → AVD → Maybe (List AVD)

specComD zero    _ _ = nothing
specComD (suc n) (cSeq a b) σ = bindM (specComD n a σ) (specComD n b)
specComD (suc n) (cAss k e) σ =
  mapM (λ a → setAD k a σ) (specAssD (nthAD k σ) (specExD e σ))
specComD (suc n) (cRep q r) σ =
  specInvD q (proj₂ (specPatD r σ)) (proj₁ (specPatD r σ))
specComD (suc n) (cCond e t el f) σ = specCondD n t el σ (specExD e σ)
specComD (suc n) (cLoop e d l f) σ =
  bindM (specComD n d σ) (specLD n d l f)

specCondD n t el σ (SD v)   = specComD n (if isT v then t else el) σ
specCondD n t el σ (CD _ _) = specComD n t σ          -- a cons is TRUTHY
specCondD n t el σ (DD c)   =
  bindM (specComD n t σ)
        (λ σt → bindM (specComD n el σ)
        (λ σe → just (joinσ c σt σe)))

specLD zero    _ _ _ _ = nothing
specLD (suc n) d l f σ = specLfD n d l f σ (specExD f σ)

specLfD n d l f σ (SD v) =
  if isT v then just σ
  else bindM (specComD n l σ)
             (λ σ₁ → bindM (specComD n d σ₁) (specLD n d l f))
specLfD n d l f σ (DD _)   = nothing
specLfD n d l f σ (CD _ _) = nothing

------------------------------------------------------------------------
-- Success-simulation.

private
  if-branch : ∀ {x v : Val} {A B r : Maybe Val} → x ≡ v →
              (if isT x then A else B) ≡ r → (if isT v then A else B) ≡ r
  if-branch refl h = h

specComD-sim : ∀ {n m} c {σ σ' ρ ρ' dyn} →
  specComD n c σ ≡ just σ' → evalC m c ρ ≡ just ρ' →
  SimD ρ σ dyn → SimD ρ' σ' dyn
specLD-sim : ∀ {n m} d l f {e σ σ' ρ ρ' dyn} →
  specLD n d l f σ ≡ just σ' → evalL m e d l f ρ ≡ just ρ' →
  SimD ρ σ dyn → SimD ρ' σ' dyn

specComD-sim {zero} c sp rt sim = nothing≢just sp
specComD-sim {suc n} {zero} c sp rt sim = nothing≢just rt
specComD-sim {suc n} {suc m} (cSeq a b) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specComD n a σ in eqs
... | nothing = nothing≢just sp
... | just σ₁ with evalC m a ρ in eqr
...   | nothing = nothing≢just rt
...   | just ρ₁ =
        specComD-sim {n} {m} b {σ₁} {σ'} {ρ₁} {ρ'} {dyn} sp rt
          (specComD-sim {n} {m} a {σ} {σ₁} {ρ} {ρ₁} {dyn} eqs eqr sim)
specComD-sim {suc n} {suc m} (cAss k e) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specAssD (nthAD k σ) (specExD e σ) in eqa
... | nothing = nothing≢just sp
... | just a with updR (vNth k ρ) (⟦ e ⟧ ρ) in equ
...   | nothing = nothing≢just rt
...   | just u =
        subst₂ (λ x y → SimD x y dyn) (just-inj rt) (just-inj sp)
          (set-SimD k sim
            (specAssD-sim (nthAD k σ) (specExD e σ) eqa
              (sym (sim k)) (specExD-sound sim e) equ))
specComD-sim {suc n} {suc m} (cRep q r) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim =
  specInvD-sim {proj₁ (specPatD r σ)} {σ'} {dyn} q (proj₂ (specPatD r σ))
    {proj₂ (evalP r ρ)} {proj₁ (evalP r ρ)} {ρ'}
    (proj₂ (specPatD-sim {ρ} {σ} {dyn} sim r))
    (proj₁ (specPatD-sim {ρ} {σ} {dyn} sim r)) sp rt
specComD-sim {suc n} {suc m} (cCond e t el f) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specExD e σ in eqe
... | SD v = cond-case sp (if-branch eveq rt)
  where
  eveq : ⟦ e ⟧ ρ ≡ v
  eveq = trans (sym (specExD-sound sim e)) (cong (λ x → γd x dyn) eqe)
  cond-case :
    specComD n (if isT v then t else el) σ ≡ just σ' →
    (if isT v
     then (evalC m t ρ >>= λ ρ₁ → assertB (isT (⟦ f ⟧ ρ₁)) ρ₁)
     else (evalC m el ρ >>= λ ρ₁ → assertB (not (isT (⟦ f ⟧ ρ₁))) ρ₁))
      ≡ just ρ' →
    SimD ρ' σ' dyn
  cond-case sp' rt' with isT v
  cond-case sp' rt' | true with evalC m t ρ in eqr
  ... | nothing = nothing≢just rt'
  ... | just ρ₁ =
        subst (λ x → SimD x σ' dyn)
          (sym (assertB-just (isT (⟦ f ⟧ ρ₁)) ρ₁ rt'))
          (specComD-sim {n} {m} t {σ} {σ'} {ρ} {ρ₁} {dyn} sp' eqr sim)
  cond-case sp' rt' | false with evalC m el ρ in eqr
  ... | nothing = nothing≢just rt'
  ... | just ρ₁ =
        subst (λ x → SimD x σ' dyn)
          (sym (assertB-just (not (isT (⟦ f ⟧ ρ₁))) ρ₁ rt'))
          (specComD-sim {n} {m} el {σ} {σ'} {ρ} {ρ₁} {dyn} sp' eqr sim)
... | CD x y = cons-case (if-branch eveq rt)
  where
  eveq : ⟦ e ⟧ ρ ≡ γd (CD x y) dyn
  eveq = sym (trans (sym (cong (λ z → γd z dyn) eqe)) (specExD-sound sim e))
  cons-case :
    (if isT (γd (CD x y) dyn)
     then (evalC m t ρ >>= λ ρ₁ → assertB (isT (⟦ f ⟧ ρ₁)) ρ₁)
     else (evalC m el ρ >>= λ ρ₁ → assertB (not (isT (⟦ f ⟧ ρ₁))) ρ₁))
      ≡ just ρ' →
    SimD ρ' σ' dyn
  cons-case rt' with evalC m t ρ in eqr
  ... | nothing = nothing≢just rt'
  ... | just ρ₁ =
        subst (λ x₁ → SimD x₁ σ' dyn)
          (sym (assertB-just (isT (⟦ f ⟧ ρ₁)) ρ₁ rt'))
          (specComD-sim {n} {m} t {σ} {σ'} {ρ} {ρ₁} {dyn} sp eqr sim)
... | DD c = dyn-case sp rt
  where
  tceq : ⟦ c ⟧r dyn ≡ ⟦ e ⟧ ρ
  tceq = trans (cong (λ x → γd x dyn) (sym eqe)) (specExD-sound sim e)
  dyn-case :
    bindM (specComD n t σ)
      (λ σt → bindM (specComD n el σ) (λ σe → just (joinσ c σt σe))) ≡ just σ' →
    evalC (suc m) (cCond e t el f) ρ ≡ just ρ' →
    SimD ρ' σ' dyn
  dyn-case sp' rt' with specComD n t σ in eqst
  ... | nothing = nothing≢just sp'
  ... | just σt with specComD n el σ in eqse
  ...   | nothing = nothing≢just sp'
  ...   | just σe = branch rt'
    where
    branch :
      (if isT (⟦ e ⟧ ρ)
       then (evalC m t ρ >>= λ ρ₁ → assertB (isT (⟦ f ⟧ ρ₁)) ρ₁)
       else (evalC m el ρ >>= λ ρ₁ → assertB (not (isT (⟦ f ⟧ ρ₁))) ρ₁))
        ≡ just ρ' →
      SimD ρ' σ' dyn
    branch rt'' with isT (⟦ e ⟧ ρ) in eqb
    branch rt'' | true with evalC m t ρ in eqr
    ... | nothing = nothing≢just rt''
    ... | just ρ₁ = final
      where
      simt : SimD ρ₁ σt dyn
      simt = specComD-sim {n} {m} t {σ} {σt} {ρ} {ρ₁} {dyn} eqst eqr sim
      tct : isT (⟦ c ⟧r dyn) ≡ true
      tct = trans (cong isT tceq) eqb
      final : SimD ρ' σ' dyn
      final rewrite sym (just-inj sp') =
        subst (λ x → SimD x (joinσ c σt σe) dyn)
          (sym (assertB-just (isT (⟦ f ⟧ ρ₁)) ρ₁ rt''))
          (λ k → trans (simt k) (sym (joinσ-γ-t tct σt σe k)))
    branch rt'' | false with evalC m el ρ in eqr
    ... | nothing = nothing≢just rt''
    ... | just ρ₁ = final
      where
      sime : SimD ρ₁ σe dyn
      sime = specComD-sim {n} {m} el {σ} {σe} {ρ} {ρ₁} {dyn} eqse eqr sim
      tcf : isT (⟦ c ⟧r dyn) ≡ false
      tcf = trans (cong isT tceq) eqb
      final : SimD ρ' σ' dyn
      final rewrite sym (just-inj sp') =
        subst (λ x → SimD x (joinσ c σt σe) dyn)
          (sym (assertB-just (not (isT (⟦ f ⟧ ρ₁))) ρ₁ rt''))
          (λ k → trans (sime k) (sym (joinσ-γ-f tcf σt σe k)))
specComD-sim {suc n} {suc m} (cLoop e d l f) {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with isT (⟦ e ⟧ ρ)
... | false = nothing≢just rt
... | true with specComD n d σ in eqs
...   | nothing = nothing≢just sp
...   | just σ₁ with evalC m d ρ in eqr
...     | nothing = nothing≢just rt
...     | just ρ₁ =
          specLD-sim {n} {m} d l f {e} {σ₁} {σ'} {ρ₁} {ρ'} {dyn} sp rt
            (specComD-sim {n} {m} d {σ} {σ₁} {ρ} {ρ₁} {dyn} eqs eqr sim)

specLD-sim {zero} d l f sp rt sim = nothing≢just sp
specLD-sim {suc n} {zero} d l f sp rt sim = nothing≢just rt
specLD-sim {suc n} {suc m} d l f {e} {σ} {σ'} {ρ} {ρ'} {dyn} sp rt sim
  with specExD f σ in eqf
... | DD _   = nothing≢just sp
... | CD _ _ = nothing≢just sp
... | SD v = loop-case sp (if-branch feq rt)
  where
  feq : ⟦ f ⟧ ρ ≡ v
  feq = trans (sym (specExD-sound sim f)) (cong (λ x → γd x dyn) eqf)
  loop-case :
    (if isT v then just σ
     else bindM (specComD n l σ)
                (λ σ₁ → bindM (specComD n d σ₁) (specLD n d l f)))
      ≡ just σ' →
    (if isT v then just ρ
     else (evalC m l ρ >>= λ ρ₁ →
           if isT (⟦ e ⟧ ρ₁) then nothing
           else (evalC m d ρ₁ >>= evalL m e d l f)))
      ≡ just ρ' →
    SimD ρ' σ' dyn
  loop-case sp' rt' with isT v
  loop-case sp' rt' | true =
    subst₂ (λ x y → SimD x y dyn) (just-inj rt') (just-inj sp') sim
  loop-case sp' rt' | false with specComD n l σ in eqsl
  ... | nothing = nothing≢just sp'
  ... | just σ₁ with evalC m l ρ in eqrl
  ...   | nothing = nothing≢just rt'
  ...   | just ρ₁ with isT (⟦ e ⟧ ρ₁)
  ...     | true = nothing≢just rt'
  ...     | false with specComD n d σ₁ in eqsd
  ...       | nothing = nothing≢just sp'
  ...       | just σ₂ with evalC m d ρ₁ in eqrd
  ...         | nothing = nothing≢just rt'
  ...         | just ρ₂ =
                specLD-sim {n} {m} d l f {e} {σ₂} {σ'} {ρ₂} {ρ'} {dyn} sp' rt'
                  (specComD-sim {n} {m} d {σ₁} {σ₂} {ρ₁} {ρ₂} {dyn} eqsd eqrd
                     (specComD-sim {n} {m} l {σ} {σ₁} {ρ} {ρ₁} {dyn} eqsl eqrl sim))

------------------------------------------------------------------------
-- HEADLINE: the contract, now with dynamic control.

emptyσD : List AVD
emptyσD = []

specProgD : ℕ → Prog → Val → Maybe RC
specProgD n (prog i c j) s =
  mapM (λ σ → liftd (nthAD j σ))
       (specComD n c (setAD i (avdCons (SD s) (DD rVar)) emptyσD))

init-SimD : ∀ i s d →
  SimD (vSet i (s · d) ⟨⟩) (setAD i (avdCons (SD s) (DD rVar)) emptyσD) d
init-SimD i s d k with k ≟ i
... | yes refl
  rewrite nthAD-set-eq k (avdCons (SD s) (DD rVar)) emptyσD = vNth-set-eq k (s · d) ⟨⟩
... | no neq
  rewrite nthAD-set-neq k i (avdCons (SD s) (DD rVar)) emptyσD neq =
  trans (vNth-set-neq k i (s · d) ⟨⟩ neq) (vNth-nil k)
  where
  vNth-nil : ∀ k → vNth k ⟨⟩ ≡ ⟨⟩
  vNth-nil zero    = refl
  vNth-nil (suc k) = vNth-nil k

spec-contract-dyn : ∀ {n m} p s {d w cr} →
  specProgD n p s ≡ just cr →
  evalProg m p (s · d) ≡ just w →
  ⟦ cr ⟧r d ≡ w
spec-contract-dyn {n} {m} (prog i c j) s {d} {w} {cr} sp rt
  with specComD n c (setAD i (avdCons (SD s) (DD rVar)) emptyσD) in eqs
... | nothing = nothing≢just sp
... | just σ with evalC m c (vSet i (s · d) ⟨⟩) in eqr
...   | nothing = nothing≢just rt
...   | just ρ = final sp rt
  where
  simρ : SimD ρ σ d
  simρ = specComD-sim {n} {m} c
           {setAD i (avdCons (SD s) (DD rVar)) emptyσD} {σ}
           {vSet i (s · d) ⟨⟩} {ρ} {d}
           eqs eqr (init-SimD i s d)
  final : just (liftd (nthAD j σ)) ≡ just cr →
          assertB (clearedB (vSet j ⟨⟩ ρ)) (vNth j ρ) ≡ just w →
          ⟦ cr ⟧r d ≡ w
  final sp' rt' with clearedB (vSet j ⟨⟩ ρ)
  final refl refl | true = trans (liftd-sound (nthAD j σ) d) (sym (simρ j))
  final sp'  ()   | false

------------------------------------------------------------------------
-- Witness: a program whose CONTROL depends on the dynamic input.
-- read 0; ⟨1,2⟩ <= 0; if pair?(x2) then 0 <= ⟨2,1⟩ else 0 <= ⟨1,2⟩
-- fi pair?(hd x0); write 0.  With s = nil the residual is a SINGLE rIf
-- over the dynamic input — both branches kept, per OfflineBTA8.

module Witness where

  dynP : Prog
  dynP = prog 0 (cSeq (cRep (pCons (pVar 1) (pVar 2)) (pVar 0))
                      (cCond (exPairp (varN 2))
                             (cRep (pVar 0) (pCons (pVar 2) (pVar 1)))
                             (cRep (pVar 0) (pCons (pVar 1) (pVar 2)))
                             (exPairp (exHd (varN 0))))) 0

  residual : RC
  residual = rIf (rPairp rVar)
                 (rCons rVar (rVal ⟨⟩))
                 (rCons (rVal ⟨⟩) rVar)

  _ : specProgD 10 dynP ⟨⟩ ≡ just residual
  _ = refl

  -- then-branch instance (dynamic input a cons):
  _ : evalProg 10 dynP (⟨⟩ · (vtrue · vtrue)) ≡ just ((vtrue · vtrue) · ⟨⟩)
  _ = refl
  _ : ⟦ residual ⟧r (vtrue · vtrue) ≡ ((vtrue · vtrue) · ⟨⟩)
  _ = refl

  -- else-branch instance (dynamic input nil):
  _ : evalProg 10 dynP (⟨⟩ · ⟨⟩) ≡ just (⟨⟩ · ⟨⟩)
  _ = refl
  _ : ⟦ residual ⟧r ⟨⟩ ≡ (⟨⟩ · ⟨⟩)
  _ = refl
