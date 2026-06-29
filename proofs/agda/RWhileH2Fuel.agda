{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Phase A2 / Tier-2 #5: a FUEL-INDEXED total interpreter for the general,
-- first-class-application language of RWhileH2Hier2, proven to COINCIDE with its
-- big-step relation, and the Futamura hierarchy lifted to fuel-level theorems.
--
-- RWhileH2Hier2 modelled general application by a RELATION `_·_⇓_` (partial =
-- "no derivation"), sidestepping the totality wall but giving no executable,
-- total interpreter.  Here we give that total interpreter:
--
--     runF : ℕ → Tm → Tm → Maybe Tm        (decreasing fuel ⇒ total in `--safe`)
--
-- whose `apT` case runs a COMPUTED program on a COMPUTED argument — the genuinely
-- Turing-complete, possibly-non-terminating part, which the fuel bounds (returns
-- `nothing` when it runs out).  We prove:
--   * runF-sound     : runF n p x ≡ just v → p · x ⇓ v        (results are correct)
--   * runF-complete  : p · x ⇓ v → ∃ n, runF n p x ≡ just v   (enough fuel exists)
--   * runF-mono-≤    : n ≤ m → runF n … ≡ just v → runF m … ≡ just v
-- Hence the relation and the total fuelled function denote the SAME partial map,
-- and the relational fp1/fp2/fp3 become fuel-level total statements
-- (fp1-fuel/fp2-fuel/fp3-fuel): the looping self-application holds whenever fuel
-- suffices.  This is the fuel/partiality model the H2 obstruction calls for.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2Fuel where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import RWhileH2Hier using
  (Tm; inp; quo; pr; fstT; sndT; apT; bInp; bQuo; bAp; spec; specP; int)
open import RWhileH2Hier2 using
  (_·_⇓_; ⇓inp; ⇓quo; ⇓pr; ⇓fst; ⇓snd; ⇓ap; ⇓bInp; ⇓bQuo; ⇓bAp
  ; ⇓-det; target; compiler; cogen; fp1-bwd; fp2; fp3)

------------------------------------------------------------------------
-- Maybe plumbing.

infixl 1 _>>=ₘ_
_>>=ₘ_ : Maybe Tm → (Tm → Maybe Tm) → Maybe Tm
just x  >>=ₘ f = f x
nothing >>=ₘ _ = nothing

bind-inv : ∀ (m : Maybe Tm) (f : Tm → Maybe Tm) {v}
         → (m >>=ₘ f) ≡ just v → Σ Tm (λ a → (m ≡ just a) × (f a ≡ just v))
bind-inv (just a) f eq = a , refl , eq
bind-inv nothing  f ()

-- projections of a pair value, as Maybe.
fstM sndM : Tm → Maybe Tm
fstM (pr a b) = just a
fstM _        = nothing
sndM (pr a b) = just b
sndM _        = nothing

fstM-inv : ∀ r {v} → fstM r ≡ just v → Σ Tm (λ b → r ≡ pr v b)
fstM-inv (pr a b) refl = b , refl
fstM-inv inp ()
fstM-inv (quo _) ()
fstM-inv (fstT _) ()
fstM-inv (sndT _) ()
fstM-inv (apT _ _) ()
fstM-inv bInp ()
fstM-inv (bQuo _) ()
fstM-inv (bAp _ _) ()

sndM-inv : ∀ r {v} → sndM r ≡ just v → Σ Tm (λ a → r ≡ pr a v)
sndM-inv (pr a b) refl = a , refl
sndM-inv inp ()
sndM-inv (quo _) ()
sndM-inv (fstT _) ()
sndM-inv (sndT _) ()
sndM-inv (apT _ _) ()
sndM-inv bInp ()
sndM-inv (bQuo _) ()
sndM-inv (bAp _ _) ()

------------------------------------------------------------------------
-- The fuel-indexed interpreter.

runF : ℕ → Tm → Tm → Maybe Tm
runF zero    _        _ = nothing
runF (suc n) inp      x = just x
runF (suc n) (quo p)  x = just p
runF (suc n) (pr a b) x = runF n a x >>=ₘ λ va → runF n b x >>=ₘ λ vb → just (pr va vb)
runF (suc n) (fstT e) x = runF n e x >>=ₘ fstM
runF (suc n) (sndT e) x = runF n e x >>=ₘ sndM
runF (suc n) (apT f a) x = runF n f x >>=ₘ λ fv → runF n a x >>=ₘ λ av → runF n fv av
runF (suc n) bInp     x = just inp
runF (suc n) (bQuo a) x = runF n a x >>=ₘ λ va → just (quo va)
runF (suc n) (bAp a b) x = runF n a x >>=ₘ λ va → runF n b x >>=ₘ λ vb → just (apT va vb)

------------------------------------------------------------------------
-- SOUNDNESS: a `just` result is a valid derivation.

runF-sound : ∀ n p x {v} → runF n p x ≡ just v → p · x ⇓ v
runF-sound zero p x ()
runF-sound (suc n) inp x refl = ⇓inp x
runF-sound (suc n) (quo p) x refl = ⇓quo p x
runF-sound (suc n) (pr a b) x eq
  with bind-inv (runF n a x) _ eq
... | va , ea , eq2 with bind-inv (runF n b x) _ eq2
...   | vb , eb , eq3 =
        subst (λ w → pr a b · x ⇓ w) (just-injective eq3)
              (⇓pr (runF-sound n a x ea) (runF-sound n b x eb))
runF-sound (suc n) (fstT e) x eq
  with bind-inv (runF n e x) fstM eq
... | r , er , eqf with fstM-inv r eqf
...   | b , refl = ⇓fst (runF-sound n e x er)
runF-sound (suc n) (sndT e) x eq
  with bind-inv (runF n e x) sndM eq
... | r , er , eqf with sndM-inv r eqf
...   | a , refl = ⇓snd (runF-sound n e x er)
runF-sound (suc n) (apT f a) x eq
  with bind-inv (runF n f x) _ eq
... | fv , ef , eq2 with bind-inv (runF n a x) _ eq2
...   | av , ea , eq3 =
        ⇓ap (runF-sound n f x ef) (runF-sound n a x ea) (runF-sound n fv av eq3)
runF-sound (suc n) bInp x refl = ⇓bInp x
runF-sound (suc n) (bQuo a) x eq
  with bind-inv (runF n a x) _ eq
... | va , ea , eq2 =
        subst (λ w → bQuo a · x ⇓ w) (just-injective eq2) (⇓bQuo (runF-sound n a x ea))
runF-sound (suc n) (bAp a b) x eq
  with bind-inv (runF n a x) _ eq
... | va , ea , eq2 with bind-inv (runF n b x) _ eq2
...   | vb , eb , eq3 =
        subst (λ w → bAp a b · x ⇓ w) (just-injective eq3)
              (⇓bAp (runF-sound n a x ea) (runF-sound n b x eb))

------------------------------------------------------------------------
-- MONOTONICITY: more fuel preserves `just` results.

runF-mono-≤ : ∀ {n m} → n ≤ m → ∀ p x {v} → runF n p x ≡ just v → runF m p x ≡ just v
runF-mono-≤ z≤n p x ()
runF-mono-≤ {suc n} {suc m} (s≤s le) inp x eq = eq
runF-mono-≤ {suc n} {suc m} (s≤s le) (quo p) x eq = eq
runF-mono-≤ {suc n} {suc m} (s≤s le) (pr a b) x eq
  with bind-inv (runF n a x) _ eq
... | va , ea , eq2 with bind-inv (runF n b x) _ eq2
...   | vb , eb , eq3 rewrite runF-mono-≤ le a x ea | runF-mono-≤ le b x eb = eq3
runF-mono-≤ {suc n} {suc m} (s≤s le) (fstT e) x eq
  with bind-inv (runF n e x) fstM eq
... | r , er , eqf rewrite runF-mono-≤ le e x er = eqf
runF-mono-≤ {suc n} {suc m} (s≤s le) (sndT e) x eq
  with bind-inv (runF n e x) sndM eq
... | r , er , eqf rewrite runF-mono-≤ le e x er = eqf
runF-mono-≤ {suc n} {suc m} (s≤s le) (apT f a) x eq
  with bind-inv (runF n f x) _ eq
... | fv , ef , eq2 with bind-inv (runF n a x) _ eq2
...   | av , ea , eq3 rewrite runF-mono-≤ le f x ef | runF-mono-≤ le a x ea =
        runF-mono-≤ le fv av eq3
runF-mono-≤ {suc n} {suc m} (s≤s le) bInp x eq = eq
runF-mono-≤ {suc n} {suc m} (s≤s le) (bQuo a) x eq
  with bind-inv (runF n a x) _ eq
... | va , ea , eq2 rewrite runF-mono-≤ le a x ea = eq2
runF-mono-≤ {suc n} {suc m} (s≤s le) (bAp a b) x eq
  with bind-inv (runF n a x) _ eq
... | va , ea , eq2 with bind-inv (runF n b x) _ eq2
...   | vb , eb , eq3 rewrite runF-mono-≤ le a x ea | runF-mono-≤ le b x eb = eq3

------------------------------------------------------------------------
-- COMPLETENESS: every derivation runs within some fuel.

runF-complete : ∀ {p x v} → p · x ⇓ v → Σ ℕ (λ n → runF n p x ≡ just v)
runF-complete (⇓inp x)   = suc zero , refl
runF-complete (⇓quo p x) = suc zero , refl
runF-complete (⇓pr {a} {b} {x} {va} {vb} da db)
  with runF-complete da | runF-complete db
... | na , ea | nb , eb = suc (na ⊔ nb) , prf
  where
    prf : runF (suc (na ⊔ nb)) (pr a b) x ≡ just (pr va vb)
    prf rewrite runF-mono-≤ (m≤m⊔n na nb) a x ea
              | runF-mono-≤ (m≤n⊔m na nb) b x eb = refl
runF-complete (⇓fst {e} {x} {va} {vb} de)
  with runF-complete de
... | n , ee = suc n , prf
  where
    prf : runF (suc n) (fstT e) x ≡ just va
    prf rewrite ee = refl
runF-complete (⇓snd {e} {x} {va} {vb} de)
  with runF-complete de
... | n , ee = suc n , prf
  where
    prf : runF (suc n) (sndT e) x ≡ just vb
    prf rewrite ee = refl
runF-complete (⇓ap {f} {a} {x} {fv} {av} {rv} df da dr)
  with runF-complete df | runF-complete da | runF-complete dr
... | nf , ef | na , ea | nr , er = suc (nf ⊔ na ⊔ nr) , prf
  where
    n = nf ⊔ na ⊔ nr
    lef : nf ≤ n
    lef = ≤-trans (m≤m⊔n nf na) (m≤m⊔n (nf ⊔ na) nr)
    lea : na ≤ n
    lea = ≤-trans (m≤n⊔m nf na) (m≤m⊔n (nf ⊔ na) nr)
    ler : nr ≤ n
    ler = m≤n⊔m (nf ⊔ na) nr
    prf : runF (suc n) (apT f a) x ≡ just rv
    prf rewrite runF-mono-≤ lef f x ef
              | runF-mono-≤ lea a x ea
              | runF-mono-≤ ler fv av er = refl
runF-complete (⇓bInp x) = suc zero , refl
runF-complete (⇓bQuo {a} {x} {va} da)
  with runF-complete da
... | n , ea = suc n , prf
  where
    prf : runF (suc n) (bQuo a) x ≡ just (quo va)
    prf rewrite ea = refl
runF-complete (⇓bAp {a} {b} {x} {va} {vb} da db)
  with runF-complete da | runF-complete db
... | na , ea | nb , eb = suc (na ⊔ nb) , prf
  where
    prf : runF (suc (na ⊔ nb)) (bAp a b) x ≡ just (apT va vb)
    prf rewrite runF-mono-≤ (m≤m⊔n na nb) a x ea
              | runF-mono-≤ (m≤n⊔m na nb) b x eb = refl

------------------------------------------------------------------------
-- Corollary: the fuelled interpreter computes EXACTLY the relation's value.

runF-correct : ∀ n p x {v w} → runF n p x ≡ just v → p · x ⇓ w → v ≡ w
runF-correct n p x eq d = ⇓-det (runF-sound n p x eq) d

------------------------------------------------------------------------
-- The Futamura hierarchy at the fuel level: each projection holds for SOME
-- finite fuel (the looping self-application terminates with the right answer
-- whenever fuel suffices) -- a total `--safe` model of H2's self-application.

fp1-fuel : ∀ src d {v} → int · pr src d ⇓ v → Σ ℕ (λ n → runF n (target src) d ≡ just v)
fp1-fuel src d pf = runF-complete (fp1-bwd src d pf)

fp2-fuel : ∀ src → Σ ℕ (λ n → runF n compiler src ≡ just (target src))
fp2-fuel src = runF-complete (fp2 src)

fp3-fuel : ∀ q → Σ ℕ (λ n → runF n cogen q ≡ just (spec specP q))
fp3-fuel q = runF-complete (fp3 q)

------------------------------------------------------------------------
-- Worked examples: concrete runs of the fuel interpreter (checked by refl), and
-- the link runF-sound to the big-step relation.  Documentation + regression.

module Examples where
  -- the input variable returns the runtime input (one fuel unit).
  ex-inp : ∀ x → runF 1 inp x ≡ just x
  ex-inp x = refl

  -- a quotation returns its quoted program.
  ex-quo : ∀ p x → runF 1 (quo p) x ≡ just p
  ex-quo p x = refl

  -- a pair of input-projections builds the diagonal pair (two fuel levels).
  ex-pr : ∀ x → runF 2 (pr inp inp) x ≡ just (pr x x)
  ex-pr x = refl

  -- first projection of that diagonal recovers the input (three levels).
  ex-fst : ∀ x → runF 3 (fstT (pr inp inp)) x ≡ just x
  ex-fst x = refl

  -- the fuel result feeds runF-sound into the big-step relation.
  ex-⇓ : ∀ x → (pr inp inp) · x ⇓ (pr x x)
  ex-⇓ x = runF-sound 2 (pr inp inp) x (ex-pr x)
