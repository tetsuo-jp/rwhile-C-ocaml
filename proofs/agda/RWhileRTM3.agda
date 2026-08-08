{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Part of the r-Turing completeness development; see RWhileRTM.agda
-- for the overview.  Split into several modules so that Agda's peak
-- memory stays bounded (one module held all of it and needed 47 GB).
------------------------------------------------------------------------

module RWhileRTM3 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileTimeInv using (inv)
open import RWhileSIWf
  using (get-set-≡; get-set-≢; Wf; wf-skip; wf-ass; wf-seq; wf-cond; wf-loop;
         NotIn; ni-opd; ni-cns; ni-hd; ni-tl; ni-eq; ni-pr; ni-var; ni-cst)

open import RWhileRTM2 public

------------------------------------------------------------------------
-- 8.  The translation of one rule (Fig. 3).
--
--   (q₁,(s₁,s₂),q₂)  ↦  [q̄₁,(L s̄₁ R)] => [q̄₂,(L s̄₂ R)]
--   (q₁,←,q₂)        ↦  [q̄₁,T] => { MOVEL(T) ; Q ^= q̄₁ ; Q ^= q̄₂ }
--   (q₁,↓,q₂)        ↦  [q̄₁,T] => [q̄₂,T]
--   (q₁,→,q₂)        ↦  [q̄₁,T] => { MOVER(T) ; Q ^= q̄₁ ; Q ^= q̄₂ }
--
-- Here only the BODY of each branch is built; the dispatch that selects it
-- is `stepC` (milestone 2).  A state change is always the pair of
-- assignments `Q ^= q̄₁ ; Q ^= q̄₂`: the first clears (rupd case 2), the
-- second sets (rupd case 1).

setState : ℕ → ℕ → Cmd
setState q₁ q₂ = vQ ^= opd (cst (atm q₁)) ⨾ vQ ^= opd (cst (atm q₂))

ruleC : ℕ → Rule → Cmd
ruleC b (rsym q₁ s₁ s₂ q₂) =
    unpackT
  ⨾ vS ^= opd (cst (atm s₁))
  ⨾ vS ^= opd (cst (atm s₂))
  ⨾ packT
  ⨾ setState q₁ q₂
ruleC b (rmov q₁ mvL q₂) = movelC b ⨾ setState q₁ q₂
ruleC b (rmov q₁ mvS q₂) = setState q₁ q₂
ruleC b (rmov q₁ mvR q₂) = moverC b ⨾ setState q₁ q₂

wf-setState : ∀ q₁ q₂ → Wf (setState q₁ q₂)
wf-setState q₁ q₂ = wf-seq (wf-ass (ni-opd ni-cst)) (wf-ass (ni-opd ni-cst))

-- THE TRANSLATION EMITS ONLY LEGAL R-WHILE.
wf-ruleC : ∀ b d → Wf (ruleC b d)
wf-ruleC b (rsym q₁ s₁ s₂ q₂) =
  wf-seq wf-unpackT
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq wf-packT (wf-setState q₁ q₂))))
wf-ruleC b (rmov q₁ mvL q₂) = wf-seq (wf-movelC b) (wf-setState q₁ q₂)
wf-ruleC b (rmov q₁ mvS q₂) = wf-setState q₁ q₂
wf-ruleC b (rmov q₁ mvR q₂) = wf-seq (wf-moverC b) (wf-setState q₁ q₂)

setState-sound : ∀ q₁ q₂ σ → get σ vQ ≡ atm q₁
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (setState q₁ q₂ ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂)
      × (∀ y → ¬ (y ≡ vQ) → get σ′ y ≡ get σ y) )
setState-sound q₁ q₂ σ hQ =
    set (set σ vQ nil) vQ (atm q₂) , _
  , e-seq s1 s2
  , get-set-≡ (set σ vQ nil) vQ (atm q₂)
  , (λ y yq → trans (get-set-≢ (set σ vQ nil) vQ y (atm q₂) (λ e → yq (sym e)))
                    (get-set-≢ σ vQ y nil (λ e → yq (sym e))))
  where
  s1 : (vQ ^= opd (cst (atm q₁))) ⊢ σ ⇒ set σ vQ nil ∣ 1
  s1 = e-ass refl (subst (λ z → rupd z (atm q₁) ≡ just nil) (sym hQ)
                         (rupd-self (atm q₁)))
  s2 : (vQ ^= opd (cst (atm q₂))) ⊢ set σ vQ nil
                                 ⇒ set (set σ vQ nil) vQ (atm q₂) ∣ 1
  s2 = e-ass refl (subst (λ z → rupd z (atm q₂) ≡ just (atm q₂))
                         (sym (get-set-≡ σ vQ nil)) refl)

------------------------------------------------------------------------
-- 8c.  THE RULE BODIES ON THE UNPACKED TAPE, WITH THE DISPATCH KEY.
--
-- Invariant of the main loop: Q holds the state, S the symbol under the
-- head, L and R the half-tapes, and K the PAIR (Q . S).  K is redundant —
-- it is a function of Q and S — but it is what makes the guard of a symbol
-- rule a single flat test, and it is cleared again when the loop ends, so
-- it is not garbage.
--
-- A state change is `Q ^= q̄ ; Q ^= q̄′` (clear then set) as before, and the
-- key is re-established by `K ^= cons Q S`, which is its own inverse: it
-- CLEARS K when K already holds (Q . S) and SETS it when K is nil.

-- Projections of a tape.  Tape is a Σ-type, so these reduce even when the
-- tape is a variable; that is what lets `HoldsU` be stated on an
-- undestructured configuration and still compute.
lefts : Tape → List ℕ
lefts (l , _ , _) = l
symOf : Tape → ℕ
symOf (_ , x , _) = x
rights : Tape → List ℕ
rights (_ , _ , r) = r

stOf : Conf → ℕ
stOf (q , _) = q
tpOf : Conf → Tape
tpOf (_ , t) = t

HoldsU : Conf → Store → Set
HoldsU c σ =
    (get σ vQ ≡ atm (stOf c)) × (get σ vS ≡ atm (symOf (tpOf c)))
  × (get σ vL ≡ encL (lefts (tpOf c))) × (get σ vR ≡ encL (rights (tpOf c)))
  × (get σ vK ≡ atm (stOf c) ∙ atm (symOf (tpOf c)))

UFrame : Store → Store → Set
UFrame σ′ σ = ∀ y → ¬ (y ≡ vQ) → ¬ (y ≡ vS) → ¬ (y ≡ vL) → ¬ (y ≡ vR)
            → ¬ (y ≡ vK) → ¬ (y ≡ vW) → get σ′ y ≡ get σ y

setKey : Cmd
setKey = vK ^= cns (var vQ) (var vS)

uruleC : ℕ → Rule → Cmd
uruleC b (rsym q s s′ q′) =
    vK ^= opd (cst (atm q  ∙ atm s ))
  ⨾ vS ^= opd (cst (atm s ))
  ⨾ vS ^= opd (cst (atm s′))
  ⨾ vQ ^= opd (cst (atm q ))
  ⨾ vQ ^= opd (cst (atm q′))
  ⨾ vK ^= opd (cst (atm q′ ∙ atm s′))
uruleC b (rmov q mvL q′) = setKey ⨾ setState q q′ ⨾ moveLC b ⨾ setKey
uruleC b (rmov q mvS q′) = setKey ⨾ setState q q′ ⨾ setKey
uruleC b (rmov q mvR q′) = setKey ⨾ setState q q′ ⨾ moveRC b ⨾ setKey

wf-setKey : Wf setKey
wf-setKey = wf-ass (ni-cns (ni-var (λ ())) (ni-var (λ ())))

wf-uruleC : ∀ b d → Wf (uruleC b d)
wf-uruleC b (rsym q s s′ q′) =
  wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst)) (wf-ass (ni-opd ni-cst))))))
wf-uruleC b (rmov q mvL q′) =
  wf-seq wf-setKey (wf-seq (wf-setState q q′) (wf-seq (wf-moveLC b) wf-setKey))
wf-uruleC b (rmov q mvS q′) =
  wf-seq wf-setKey (wf-seq (wf-setState q q′) wf-setKey)
wf-uruleC b (rmov q mvR q′) =
  wf-seq wf-setKey (wf-seq (wf-setState q q′) (wf-seq (wf-moveRC b) wf-setKey))

-- the two directions of a constant reversible assignment
constSet : ∀ x c σ → get σ x ≡ nil → (x ^= opd (cst c)) ⊢ σ ⇒ set σ x c ∣ 1
constSet x c σ h = e-ass refl (subst (λ z → rupd z c ≡ just c) (sym h) refl)

constClr : ∀ x c σ → get σ x ≡ c → (x ^= opd (cst c)) ⊢ σ ⇒ set σ x nil ∣ 1
constClr x c σ h = e-ass refl (subst (λ z → rupd z c ≡ just nil) (sym h) (rupd-self c))

setKey-set : ∀ σ q x → get σ vQ ≡ atm q → get σ vS ≡ atm x → get σ vK ≡ nil
           → setKey ⊢ σ ⇒ set σ vK (atm q ∙ atm x) ∣ 1
setKey-set σ q x hQ hS hK =
  e-ass (cong just (cong₂ _∙_ hQ hS))
        (subst (λ z → rupd z (atm q ∙ atm x) ≡ just (atm q ∙ atm x)) (sym hK) refl)

setKey-clr : ∀ σ q x → get σ vQ ≡ atm q → get σ vS ≡ atm x
           → get σ vK ≡ atm q ∙ atm x → setKey ⊢ σ ⇒ set σ vK nil ∣ 1
setKey-clr σ q x hQ hS hK =
  e-ass (cong just (cong₂ _∙_ hQ hS))
        (subst (λ z → rupd z (atm q ∙ atm x) ≡ just nil) (sym hK)
               (rupd-self (atm q ∙ atm x)))

USpec : ℕ → Rule → Conf → Store → Set
USpec b d c′ σ =
  Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
    ( (uruleC b d ⊢ σ ⇒ σ′ ∣ k) × HoldsU c′ σ′ × (get σ′ vW ≡ nil) × UFrame σ′ σ )

-- (q,(s,s′),q′) : six constant assignments, nothing else moves.
usym-sound : ∀ b q s s′ q′ σ l r
  → HoldsU (q , (l , s , r)) σ → get σ vW ≡ nil
  → USpec b (rsym q s s′ q′) (q′ , (l , s′ , r)) σ
usym-sound b q s s′ q′ σ l r (hQ , hS , hL , hR , hK) hW =
    τ6 , _
  , e-seq a1 (e-seq a2 (e-seq a3 (e-seq a4 (e-seq a5 a6))))
  , (g6Q , g6S , g6L , g6R , get-set-≡ τ5 vK (atm q′ ∙ atm s′))
  , g6W , frame
  where
  τ1 τ2 τ3 τ4 τ5 τ6 : Store
  τ1 = set σ  vK nil
  τ2 = set τ1 vS nil
  τ3 = set τ2 vS (atm s′)
  τ4 = set τ3 vQ nil
  τ5 = set τ4 vQ (atm q′)
  τ6 = set τ5 vK (atm q′ ∙ atm s′)

  g1S : get τ1 vS ≡ atm s
  g1S = trans (get-set-≢ σ vK vS nil (λ ())) hS
  g3Q : get τ3 vQ ≡ atm q
  g3Q = trans (get-set-≢ τ2 vS vQ (atm s′) (λ ()))
        (trans (get-set-≢ τ1 vS vQ nil (λ ()))
               (trans (get-set-≢ σ vK vQ nil (λ ())) hQ))
  g5K : get τ5 vK ≡ nil
  g5K = trans (get-set-≢ τ4 vQ vK (atm q′) (λ ()))
        (trans (get-set-≢ τ3 vQ vK nil (λ ()))
        (trans (get-set-≢ τ2 vS vK (atm s′) (λ ()))
        (trans (get-set-≢ τ1 vS vK nil (λ ())) (get-set-≡ σ vK nil))))

  a1 = constClr vK (atm q ∙ atm s) σ hK
  a2 = constClr vS (atm s) τ1 g1S
  a3 = constSet vS (atm s′) τ2 (get-set-≡ τ1 vS nil)
  a4 = constClr vQ (atm q) τ3 g3Q
  a5 = constSet vQ (atm q′) τ4 (get-set-≡ τ3 vQ nil)
  a6 = constSet vK (atm q′ ∙ atm s′) τ5 g5K

  g6Q : get τ6 vQ ≡ atm q′
  g6Q = trans (get-set-≢ τ5 vK vQ (atm q′ ∙ atm s′) (λ ()))
              (get-set-≡ τ4 vQ (atm q′))
  g6S : get τ6 vS ≡ atm s′
  g6S = trans (get-set-≢ τ5 vK vS (atm q′ ∙ atm s′) (λ ()))
        (trans (get-set-≢ τ4 vQ vS (atm q′) (λ ()))
        (trans (get-set-≢ τ3 vQ vS nil (λ ())) (get-set-≡ τ2 vS (atm s′))))
  down : ∀ y → ¬ (y ≡ vQ) → ¬ (y ≡ vS) → ¬ (y ≡ vK) → get τ6 y ≡ get σ y
  down y yQ yS yK =
    trans (get-set-≢ τ5 vK y (atm q′ ∙ atm s′) (λ e → yK (sym e)))
    (trans (get-set-≢ τ4 vQ y (atm q′) (λ e → yQ (sym e)))
    (trans (get-set-≢ τ3 vQ y nil (λ e → yQ (sym e)))
    (trans (get-set-≢ τ2 vS y (atm s′) (λ e → yS (sym e)))
    (trans (get-set-≢ τ1 vS y nil (λ e → yS (sym e)))
           (get-set-≢ σ vK y nil (λ e → yK (sym e)))))))
  g6L : get τ6 vL ≡ encL l
  g6L = trans (down vL (λ ()) (λ ()) (λ ())) hL
  g6R : get τ6 vR ≡ encL r
  g6R = trans (down vR (λ ()) (λ ()) (λ ())) hR
  g6W : get τ6 vW ≡ nil
  g6W = trans (down vW (λ ()) (λ ()) (λ ())) hW
  frame : UFrame τ6 σ
  frame y yQ yS yL yR yK yW = down y yQ yS yK

-- (q,↓,q′) : clear the key, change the state, re-establish the key.
umvS-sound : ∀ b q q′ σ l x r
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → USpec b (rmov q mvS q′) (q′ , (l , x , r)) σ
umvS-sound b q q′ σ l x r (hQ , hS , hL , hR , hK) hW
  with setState-sound q q′ (set σ vK nil)
         (trans (get-set-≢ σ vK vQ nil (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2 =
    set σ₂ vK (atm q′ ∙ atm x) , _
  , e-seq (setKey-clr σ q x hQ hS hK) (e-seq dS (setKey-set σ₂ q′ x g2Q g2S g2K))
  , ( trans (get-set-≢ σ₂ vK vQ (atm q′ ∙ atm x) (λ ())) g2Q
    , trans (get-set-≢ σ₂ vK vS (atm q′ ∙ atm x) (λ ())) g2S
    , trans (get-set-≢ σ₂ vK vL (atm q′ ∙ atm x) (λ ())) g2L
    , trans (get-set-≢ σ₂ vK vR (atm q′ ∙ atm x) (λ ())) g2R
    , get-set-≡ σ₂ vK (atm q′ ∙ atm x) )
  , trans (get-set-≢ σ₂ vK vW (atm q′ ∙ atm x) (λ ())) g2W
  , (λ y yQ yS yL yR yK yW →
       trans (get-set-≢ σ₂ vK y (atm q′ ∙ atm x) (λ e → yK (sym e)))
       (trans (f2 y yQ) (get-set-≢ σ vK y nil (λ e → yK (sym e)))))
  where
  g2S : get σ₂ vS ≡ atm x
  g2S = trans (f2 vS (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS)
  g2L : get σ₂ vL ≡ encL l
  g2L = trans (f2 vL (λ ())) (trans (get-set-≢ σ vK vL nil (λ ())) hL)
  g2R : get σ₂ vR ≡ encL r
  g2R = trans (f2 vR (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR)
  g2W : get σ₂ vW ≡ nil
  g2W = trans (f2 vW (λ ())) (trans (get-set-≢ σ vK vW nil (λ ())) hW)
  g2K : get σ₂ vK ≡ nil
  g2K = trans (f2 vK (λ ())) (get-set-≡ σ vK nil)

-- (q,←,q′) : clear the key, change the state, MOVE, re-establish the key.
umvL-sound : ∀ b q q′ σ l x r → NoTrailB b l
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → USpec b (rmov q mvL q′) (q′ , (popTail l , popHead b l , consNB b x r)) σ
umvL-sound b q q′ σ l x r ntl (hQ , hS , hL , hR , hK) hW
  with setState-sound q q′ (set σ vK nil)
         (trans (get-set-≢ σ vK vQ nil (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2
  with moveL-sound b σ₂ l x r ntl
         (trans (f2 vS (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS))
         (trans (f2 vL (λ ())) (trans (get-set-≢ σ vK vL nil (λ ())) hL))
         (trans (f2 vR (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR))
         (trans (f2 vW (λ ())) (trans (get-set-≢ σ vK vW nil (λ ())) hW))
... | σ₃ , _ , dM , g3S , g3L , g3R , g3W , f3 =
    set σ₃ vK (atm q′ ∙ atm (popHead b l)) , _
  , e-seq (setKey-clr σ q x hQ hS hK)
          (e-seq dS (e-seq dM (setKey-set σ₃ q′ (popHead b l) g3Q g3S g3K)))
  , ( trans (get-set-≢ σ₃ vK vQ (atm q′ ∙ atm (popHead b l)) (λ ())) g3Q
    , trans (get-set-≢ σ₃ vK vS (atm q′ ∙ atm (popHead b l)) (λ ())) g3S
    , trans (get-set-≢ σ₃ vK vL (atm q′ ∙ atm (popHead b l)) (λ ())) g3L
    , trans (get-set-≢ σ₃ vK vR (atm q′ ∙ atm (popHead b l)) (λ ())) g3R
    , get-set-≡ σ₃ vK (atm q′ ∙ atm (popHead b l)) )
  , trans (get-set-≢ σ₃ vK vW (atm q′ ∙ atm (popHead b l)) (λ ())) g3W
  , (λ y yQ yS yL yR yK yW →
       trans (get-set-≢ σ₃ vK y (atm q′ ∙ atm (popHead b l)) (λ e → yK (sym e)))
       (trans (f3 y yS yL yR yW)
       (trans (f2 y yQ) (get-set-≢ σ vK y nil (λ e → yK (sym e))))))
  where
  g3Q : get σ₃ vQ ≡ atm q′
  g3Q = trans (f3 vQ (λ ()) (λ ()) (λ ()) (λ ())) g2Q
  g3K : get σ₃ vK ≡ nil
  g3K = trans (f3 vK (λ ()) (λ ()) (λ ()) (λ ()))
              (trans (f2 vK (λ ())) (get-set-≡ σ vK nil))

-- (q,→,q′) : the mirror image.
umvR-sound : ∀ b q q′ σ l x r → NoTrailB b r
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → USpec b (rmov q mvR q′) (q′ , (consNB b x l , popHead b r , popTail r)) σ
umvR-sound b q q′ σ l x r ntr (hQ , hS , hL , hR , hK) hW
  with setState-sound q q′ (set σ vK nil)
         (trans (get-set-≢ σ vK vQ nil (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2
  with moveR-sound b σ₂ l x r ntr
         (trans (f2 vS (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS))
         (trans (f2 vL (λ ())) (trans (get-set-≢ σ vK vL nil (λ ())) hL))
         (trans (f2 vR (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR))
         (trans (f2 vW (λ ())) (trans (get-set-≢ σ vK vW nil (λ ())) hW))
... | σ₃ , _ , dM , g3S , g3R , g3L , g3W , f3 =
    set σ₃ vK (atm q′ ∙ atm (popHead b r)) , _
  , e-seq (setKey-clr σ q x hQ hS hK)
          (e-seq dS (e-seq dM (setKey-set σ₃ q′ (popHead b r) g3Q g3S g3K)))
  , ( trans (get-set-≢ σ₃ vK vQ _ (λ ())) g3Q
    , trans (get-set-≢ σ₃ vK vS _ (λ ())) g3S
    , trans (get-set-≢ σ₃ vK vL _ (λ ())) g3L
    , trans (get-set-≢ σ₃ vK vR _ (λ ())) g3R
    , get-set-≡ σ₃ vK _ )
  , trans (get-set-≢ σ₃ vK vW _ (λ ())) g3W
  , (λ y yQ yS yL yR yK yW →
       trans (get-set-≢ σ₃ vK y _ (λ e → yK (sym e)))
       (trans (f3 y yS yL yR yW)
       (trans (f2 y yQ) (get-set-≢ σ vK y nil (λ e → yK (sym e))))))
  where
  g3Q : get σ₃ vQ ≡ atm q′
  g3Q = trans (f3 vQ (λ ()) (λ ()) (λ ()) (λ ())) g2Q
  g3K : get σ₃ vK ≡ nil
  g3K = trans (f3 vK (λ ()) (λ ()) (λ ()) (λ ()))
              (trans (f2 vK (λ ())) (get-set-≡ σ vK nil))
