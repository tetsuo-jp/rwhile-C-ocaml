{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Part of the r-Turing completeness development; see RWhileRTM.agda
-- for the overview.  Split into several modules so that Agda's peak
-- memory stays bounded (one module held all of it and needed 47 GB).
------------------------------------------------------------------------

module RWhileRTM4 where

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

open import RWhileRTM3 public

------------------------------------------------------------------------
-- 8d.  THE GUARDS OF THE DISPATCH, AND WHAT THE RTM CONDITIONS BUY.
--
-- The letter's STEP is `rewrite [Q,T] by d̲₁ | … | d̲ₙ`, a reversible
-- multi-way case.  In the core it becomes a chain of binary conditionals,
-- one per rule: the ENTRY test says "this rule's left pattern matches" and
-- the EXIT test says "its right pattern matches".  Local forward
-- determinism makes the entry tests mutually exclusive (so the chain picks
-- the right branch going forwards); local backward determinism makes the
-- exit tests mutually exclusive (so it does going backwards).  Both are
-- packaged below as "at most one rule fires", which is what the chain
-- actually consumes.

ft→⊥ : false ≡ true → ⊥
ft→⊥ ()

_≟M_ : (a c : Move) → Dec (a ≡ c)
mvL ≟M mvL = yes refl
mvL ≟M mvS = no λ ()
mvL ≟M mvR = no λ ()
mvS ≟M mvL = no λ ()
mvS ≟M mvS = yes refl
mvS ≟M mvR = no λ ()
mvR ≟M mvL = no λ ()
mvR ≟M mvS = no λ ()
mvR ≟M mvR = yes refl

_≟R_ : (d e : Rule) → Dec (d ≡ e)
rsym _ _ _ _ ≟R rmov _ _ _   = no λ ()
rmov _ _ _   ≟R rsym _ _ _ _ = no λ ()
rsym q s u p ≟R rsym q′ s′ u′ p′ with q ≟ q′
... | no ne = no λ { refl → ne refl }
... | yes refl with s ≟ s′
...   | no ne = no λ { refl → ne refl }
...   | yes refl with u ≟ u′
...     | no ne = no λ { refl → ne refl }
...     | yes refl with p ≟ p′
...       | no ne = no λ { refl → ne refl }
...       | yes refl = yes refl
rmov q a p ≟R rmov q′ a′ p′ with q ≟ q′
... | no ne = no λ { refl → ne refl }
... | yes refl with a ≟M a′
...   | no ne = no λ { refl → ne refl }
...   | yes refl with p ≟ p′
...     | no ne = no λ { refl → ne refl }
...     | yes refl = yes refl

-- The guards, as R-WHILE expressions.  Each is ONE equality against a
-- constant: a symbol rule tests the key (Q . S), a move rule tests Q alone.
entryE : Rule → Exp
entryE (rsym q s _ _)  = eqE (var vK) (cst (atm q ∙ atm s))
entryE (rmov q _ _)    = eqE (var vQ) (cst (atm q))

exitE : Rule → Exp
exitE (rsym _ _ s′ q′) = eqE (var vK) (cst (atm q′ ∙ atm s′))
exitE (rmov _ _ q′)    = eqE (var vQ) (cst (atm q′))

-- and what they compute, as booleans on the (state, symbol) pair
entryB : Rule → ℕ → ℕ → Bool
entryB (rsym q₀ s₀ _ _) q x = if eqℕ q q₀ then eqℕ x s₀ else false
entryB (rmov q₀ _ _)    q x = eqℕ q q₀

exitB : Rule → ℕ → ℕ → Bool
exitB (rsym _ _ s₀ q₀) q x = if eqℕ q q₀ then eqℕ x s₀ else false
exitB (rmov _ _ q₀)    q x = eqℕ q q₀

eval-entry : ∀ d σ q x → get σ vQ ≡ atm q → get σ vK ≡ atm q ∙ atm x
           → evalT σ (entryE d) ≡ just (entryB d q x)
eval-entry (rsym _ _ _ _) σ q x hQ hK rewrite hK = cong just (isTrue-boolV _)
eval-entry (rmov _ _ _)   σ q x hQ hK rewrite hQ = cong just (isTrue-boolV _)

eval-exit : ∀ d σ q x → get σ vQ ≡ atm q → get σ vK ≡ atm q ∙ atm x
          → evalT σ (exitE d) ≡ just (exitB d q x)
eval-exit (rsym _ _ _ _) σ q x hQ hK rewrite hK = cong just (isTrue-boolV _)
eval-exit (rmov _ _ _)   σ q x hQ hK rewrite hQ = cong just (isTrue-boolV _)

-- reading a firing guard back
entryB-src : ∀ d q x → entryB d q x ≡ true → src d ≡ q
entryB-src (rsym q₀ s₀ _ _) q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → q₀ ≡ q
  go true  h = sym (eqℕ-true-inv q q₀ h)
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))
entryB-src (rmov q₀ _ _) q x e = sym (eqℕ-true-inv q q₀ e)

entryB-read : ∀ q₀ s₀ u₀ p₀ q x → entryB (rsym q₀ s₀ u₀ p₀) q x ≡ true → s₀ ≡ x
entryB-read q₀ s₀ u₀ p₀ q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → s₀ ≡ x
  go true  h = sym (eqℕ-true-inv x s₀
                 (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))

exitB-tgt : ∀ d q x → exitB d q x ≡ true → tgt d ≡ q
exitB-tgt (rsym _ _ s₀ q₀) q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → q₀ ≡ q
  go true  h = sym (eqℕ-true-inv q q₀ h)
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))
exitB-tgt (rmov _ _ q₀) q x e = sym (eqℕ-true-inv q q₀ e)

exitB-write : ∀ p₀ s₀ u₀ q₀ q x → exitB (rsym p₀ s₀ u₀ q₀) q x ≡ true → u₀ ≡ x
exitB-write p₀ s₀ u₀ q₀ q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → u₀ ≡ x
  go true  h = sym (eqℕ-true-inv x u₀
                 (subst (λ z → (if z then eqℕ x u₀ else false) ≡ true) h e))
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x u₀ else false) ≡ true) h e))

-- LOCAL FORWARD DETERMINISM, in the form the dispatch uses: at most one
-- rule of the machine fires on a given (state, scanned symbol).
lfd-fires : ∀ M → LFD M → ∀ d₁ d₂ q x → d₁ ∈ rules M → d₂ ∈ rules M
          → entryB d₁ q x ≡ true → entryB d₂ q x ≡ true → d₁ ≡ d₂
lfd-fires M lfd d₁ d₂ q x m₁ m₂ e₁ e₂ with d₁ ≟R d₂
... | yes eq = eq
... | no ne
  with lfd d₁ d₂ m₁ m₂ ne
         (trans (entryB-src d₁ q x e₁) (sym (entryB-src d₂ q x e₂)))
...  | qq , s₁ , t₁ , p₁ , s₂ , t₂ , p₂ , refl , refl , s₁≢s₂ =
       ⊥-elim (s₁≢s₂ (trans (entryB-read qq s₁ t₁ p₁ q x e₁)
                            (sym (entryB-read qq s₂ t₂ p₂ q x e₂))))

-- LOCAL BACKWARD DETERMINISM, likewise: at most one rule of the machine can
-- have produced a given (state, written symbol).
lbd-fires : ∀ M → LBD M → ∀ d₁ d₂ q x → d₁ ∈ rules M → d₂ ∈ rules M
          → exitB d₁ q x ≡ true → exitB d₂ q x ≡ true → d₁ ≡ d₂
lbd-fires M lbd d₁ d₂ q x m₁ m₂ e₁ e₂ with d₁ ≟R d₂
... | yes eq = eq
... | no ne
  with lbd d₁ d₂ m₁ m₂ ne
         (trans (exitB-tgt d₁ q x e₁) (sym (exitB-tgt d₂ q x e₂)))
...  | qq , s₁ , u₁ , p₁ , s₂ , u₂ , p₂ , refl , refl , u₁≢u₂ =
       ⊥-elim (u₁≢u₂ (trans (exitB-write p₁ s₁ u₁ qq q x e₁)
                            (sym (exitB-write p₂ s₂ u₂ qq q x e₂))))

------------------------------------------------------------------------
-- 8e.  ONE LEMMA FOR THE FOUR RULE BODIES, PLUS THE TWO GUARD FACTS.

-- the rule that makes a step fires on that step's (state, scanned symbol) ...
fires-entry : ∀ b d q t c′ → StepBy b d (q , t) c′ → entryB d q (symOf t) ≡ true
fires-entry b (rsym q s _ _) _ _ _ sb-sym rewrite eqℕ-refl q | eqℕ-refl s = refl
fires-entry b (rmov q _ _) _ _ _ sb-lft   = eqℕ-refl q
fires-entry b (rmov q _ _) _ _ _ sb-sty   = eqℕ-refl q
fires-entry b (rmov q _ _) _ _ _ (sb-rgt _) = eqℕ-refl q

-- ... and its output pattern matches the (state, written symbol) it left
fires-exit : ∀ b d q t q′ t′ → StepBy b d (q , t) (q′ , t′)
           → exitB d q′ (symOf t′) ≡ true
fires-exit b (rsym _ _ s′ q′) _ _ _ _ sb-sym rewrite eqℕ-refl q′ | eqℕ-refl s′ = refl
fires-exit b (rmov _ _ q′) _ _ _ _ sb-lft     = eqℕ-refl q′
fires-exit b (rmov _ _ q′) _ _ _ _ sb-sty     = eqℕ-refl q′
fires-exit b (rmov _ _ q′) _ _ _ _ (sb-rgt _) = eqℕ-refl q′

ubody-sound : ∀ b d q l x r c′ σ
  → StepBy b d (q , (l , x , r)) c′
  → TapeOK b (l , x , r) → TapeOK b (tpOf c′)
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (uruleC b d ⊢ σ ⇒ σ′ ∣ k) × HoldsU c′ σ′
      × (get σ′ vW ≡ nil) × UFrame σ′ σ )
ubody-sound b _ q l x r _ σ (sb-sym {s′ = s′} {q′ = q′}) _ _ hu hW =
  usym-sound b q x s′ q′ σ l r hu hW
ubody-sound b _ q l x r _ σ (sb-lft {q′ = q′}) (ntl , _) _ hu hW =
  subst (λ z → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
                 ( (uruleC b (rmov q mvL q′) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , z) σ′
                 × (get σ′ vW ≡ nil) × UFrame σ′ σ ))
        (sym (movel-pop-push b l x r))
        (umvL-sound b q q′ σ l x r ntl hu hW)
ubody-sound b _ q l x r _ σ (sb-sty {q′ = q′}) _ _ hu hW =
  umvS-sound b q q′ σ l x r hu hW
ubody-sound b _ q l x r _ σ (sb-rgt {q′ = q′} {l′ = l′} {x′} {r′} em) (_ , ntr)
            (ntl′ , _) hu hW =
  subst (λ z → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
                 ( (uruleC b (rmov q mvR q′) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , z) σ′
                 × (get σ′ vW ≡ nil) × UFrame σ′ σ ))
        t′-is
        (umvR-sound b q q′ σ l x r ntr hu hW)
  where
  t′-is : (consNB b x l , popHead b r , popTail r) ≡ (l′ , x′ , r′)
  t′-is = trans (sym (cong (mover b) em)) (mover-movel b l′ x′ r′ ntl′)

------------------------------------------------------------------------
-- 8f.  THE DISPATCH: the letter's `rewrite [Q,T] by d̲₁ | … | d̲ₙ`.
--
-- One binary conditional per rule.  Going FORWARDS the chain picks the
-- branch whose entry guard fires, and local forward determinism says at
-- most one does.  Going BACKWARDS — which is what the exit assertions
-- police — local backward determinism says at most one rule could have
-- produced the state and symbol now in place.  Both conditions are used
-- exactly once each, below.

stepC : ℕ → List Rule → Cmd
stepC b []       = skip
stepC b (d ∷ ds) = cond (entryE d) (uruleC b d) (stepC b ds) (exitE d)

wf-stepC : ∀ b ds → Wf (stepC b ds)
wf-stepC b []       = wf-skip
wf-stepC b (d ∷ ds) = wf-cond (wf-uruleC b d) (wf-stepC b ds)

module Dispatch (M : RTM) (ok : IsRTM M) where
  open IsRTM ok

  dispatch-sound : ∀ ds d q l x r q′ t′ σ
    → (∀ e → e ∈ ds → e ∈ rules M)
    → d ∈ ds → d ∈ rules M
    → StepBy (blank M) d (q , (l , x , r)) (q′ , t′)
    → TapeOK (blank M) (l , x , r) → TapeOK (blank M) t′
    → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
    → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
        ( (stepC (blank M) ds ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , t′) σ′
        × (get σ′ vW ≡ nil) × UFrame σ′ σ )
  dispatch-sound [] d q l x r q′ t′ σ sub () md st tok tok′ hu hW
  dispatch-sound (d₀ ∷ ds) d q l x r q′ t′ σ sub mem md st tok tok′
                 (hQ , hS , hL , hR , hK) hW = go (entryB d₀ q x) refl
    where
    firesE : entryB d q x ≡ true
    firesE = fires-entry (blank M) d q (l , x , r) (q′ , t′) st
    firesX : exitB d q′ (symOf t′) ≡ true
    firesX = fires-exit (blank M) d q (l , x , r) q′ t′ st

    -- if the head's guard does NOT fire, the head is not our rule ...
    neq : entryB d₀ q x ≡ false → ¬ (d ≡ d₀)
    neq h px = tf→⊥ (trans (sym (subst (λ z → entryB z q x ≡ true) px firesE)) h)

    -- ... so the rule is further down the chain ...
    memTail : (m : d ∈ (d₀ ∷ ds)) → entryB d₀ q x ≡ false → d ∈ ds
    memTail (here px) h = ⊥-elim (neq h px)
    memTail (there m) h = m

    -- ... and, by LOCAL BACKWARD DETERMINISM, the head's exit assertion is
    -- false on the store the rest of the chain leaves behind.  Without that
    -- the else-branch could not be closed.
    exFalse : entryB d₀ q x ≡ false → exitB d₀ q′ (symOf t′) ≡ false
    exFalse h = g2 (exitB d₀ q′ (symOf t′)) refl
      where
      g2 : ∀ u → exitB d₀ q′ (symOf t′) ≡ u → exitB d₀ q′ (symOf t′) ≡ false
      g2 true hh = ⊥-elim (neq h (sym (lbd-fires M lbd d₀ d q′ (symOf t′)
                                        (sub d₀ (here refl)) md hh firesX)))
      g2 false hh = hh

    go : ∀ u → entryB d₀ q x ≡ u
       → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
           ( (stepC (blank M) (d₀ ∷ ds) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , t′) σ′
           × (get σ′ vW ≡ nil) × UFrame σ′ σ )
    -- the head's guard fires: by LOCAL FORWARD DETERMINISM it IS our rule
    go true h
      with lfd-fires M lfd d₀ d q x (sub d₀ (here refl)) md h firesE
    ... | refl
      with ubody-sound (blank M) d q l x r (q′ , t′) σ st tok tok′
                       (hQ , hS , hL , hR , hK) hW
    ...  | σ′ , _ , dBody , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr =
           σ′ , _
         , e-then (trans (eval-entry d σ q x hQ hK) (cong just firesE))
                  dBody
                  (trans (eval-exit d σ′ q′ (symOf t′) hQ′ hK′) (cong just firesX))
         , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr
    -- it does not: skip this branch and recurse
    go false h
      with dispatch-sound ds d q l x r q′ t′ σ (λ e me → sub e (there me))
                          (memTail mem h) md st tok tok′ (hQ , hS , hL , hR , hK) hW
    ... | σ′ , _ , dRest , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr =
          σ′ , _
        , e-else (trans (eval-entry d₀ σ q x hQ hK) (cong just h))
                 dRest
                 (trans (eval-exit d₀ σ′ q′ (symOf t′) hQ′ hK′)
                        (cong just (exFalse h)))
        , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr

  -- THE STEP: the whole rule list, for a step the machine actually makes.
  step-sound : ∀ q l x r q′ t′ σ
    → Step M (q , (l , x , r)) (q′ , t′)
    → TapeOK (blank M) (l , x , r) → TapeOK (blank M) t′
    → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
    → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
        ( (stepC (blank M) (rules M) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , t′) σ′
        × (get σ′ vW ≡ nil) × UFrame σ′ σ )
  step-sound q l x r q′ t′ σ stp tok tok′ hu hW with step-splits stp
  ... | d , md , sb =
    dispatch-sound (rules M) d q l x r q′ t′ σ (λ _ me → me) md md sb
                   tok tok′ hu hW
