{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick A2/B1: STORE LAWS and WELL-FORMEDNESS.
--
-- Two side conditions are needed before the dispatch body of the
-- self-interpreter can be built, and both are R-WHILE's own static
-- conditions rather than artefacts of the formalisation:
--
--  (1) `X ^= E` requires X ∉ Vars(E).  The interpreter uses this to
--      UNCOMPUTE: after updating the store it re-evaluates E to clear the
--      value register, which only works if E's value did not change
--      (`evalE-frame`).  This is `ri.rwhile`'s `INV-EVAL-EXP` idiom.
--
--  (2) The object store has a fixed size M (`ri.rwhile`: the variable list
--      `Vl` with M >= 75 cells), so every variable index must be < M
--      (`InR`).  Execution then preserves the store's length (`⇒-length`),
--      which is what keeps the interpreter's `Vl` walk well-defined.
--
-- Also proves the separation laws for `get`/`set` at distinct indices, the
-- workhorses for both.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIWf where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ⊔-monoˡ-≤; ⊔-monoʳ-≤)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileSIEnc using (vmax; vmaxᵉ; vmaxᵒ)

------------------------------------------------------------------------
-- Separation laws for the store.

get-set-≡ : ∀ σ x v → get (set σ x v) x ≡ v
get-set-≡ []      zero    v = refl
get-set-≡ []      (suc x) v = get-set-≡ [] x v
get-set-≡ (u ∷ σ) zero    v = refl
get-set-≡ (u ∷ σ) (suc x) v = get-set-≡ σ x v

get-set-≢ : ∀ σ x y v → ¬ (x ≡ y) → get (set σ x v) y ≡ get σ y
get-set-≢ []      zero    zero    v ne = ⊥-elim (ne refl)
get-set-≢ []      zero    (suc y) v ne = refl
get-set-≢ []      (suc x) zero    v ne = refl
get-set-≢ []      (suc x) (suc y) v ne = get-set-≢ [] x y v (λ e → ne (cong suc e))
get-set-≢ (u ∷ σ) zero    zero    v ne = ⊥-elim (ne refl)
get-set-≢ (u ∷ σ) zero    (suc y) v ne = refl
get-set-≢ (u ∷ σ) (suc x) zero    v ne = refl
get-set-≢ (u ∷ σ) (suc x) (suc y) v ne = get-set-≢ σ x y v (λ e → ne (cong suc e))

length-set : ∀ σ x v → x < length σ → length (set σ x v) ≡ length σ
length-set (u ∷ σ) zero    v _        = refl
length-set (u ∷ σ) (suc x) v (s≤s lt) = cong suc (length-set σ x v lt)

------------------------------------------------------------------------
-- "x does not occur in e" -- R-WHILE's condition on `X ^= E`.

data NotInO (x : ℕ) : Opd → Set where
  ni-var : ∀ {y} → ¬ (x ≡ y) → NotInO x (var y)
  ni-cst : ∀ {v} → NotInO x (cst v)

data NotIn (x : ℕ) : Exp → Set where
  ni-opd : ∀ {a}   → NotInO x a → NotIn x (opd a)
  ni-cns : ∀ {a b} → NotInO x a → NotInO x b → NotIn x (cns a b)
  ni-hd  : ∀ {a}   → NotInO x a → NotIn x (hdE a)
  ni-tl  : ∀ {a}   → NotInO x a → NotIn x (tlE a)
  ni-eq  : ∀ {a b} → NotInO x a → NotInO x b → NotIn x (eqE a b)
  ni-pr  : ∀ {a}   → NotInO x a → NotIn x (prE a)

-- FRAME: an assignment to x cannot change the value of an expression that
-- does not mention x.  (This is why re-running the interpreter's expression
-- evaluation after the update CLEARS the value register.)
evalO-frame : ∀ σ x u a → NotInO x a → evalO (set σ x u) a ≡ evalO σ a
evalO-frame σ x u (var y) (ni-var ne) = get-set-≢ σ x y u ne
evalO-frame σ x u (cst v) ni-cst      = refl

evalE-frame : ∀ σ x u e → NotIn x e → evalE (set σ x u) e ≡ evalE σ e
evalE-frame σ x u (opd a)   (ni-opd na)      = cong just (evalO-frame σ x u a na)
evalE-frame σ x u (cns a b) (ni-cns na nb)
  rewrite evalO-frame σ x u a na | evalO-frame σ x u b nb = refl
evalE-frame σ x u (hdE a)   (ni-hd na)  rewrite evalO-frame σ x u a na = refl
evalE-frame σ x u (tlE a)   (ni-tl na)  rewrite evalO-frame σ x u a na = refl
evalE-frame σ x u (prE a)   (ni-pr na)  rewrite evalO-frame σ x u a na = refl
evalE-frame σ x u (eqE a b) (ni-eq na nb)
  rewrite evalO-frame σ x u a na | evalO-frame σ x u b nb = refl

------------------------------------------------------------------------
-- Well-formed commands (every assignment satisfies the condition).

data Wf : Cmd → Set where
  wf-skip : Wf skip
  wf-ass  : ∀ {x e} → NotIn x e → Wf (x ^= e)
  wf-seq  : ∀ {c d} → Wf c → Wf d → Wf (c ⨾ d)
  wf-cond : ∀ {e c d f} → Wf c → Wf d → Wf (cond e c d f)
  wf-loop : ∀ {e D L f} → Wf D → Wf L → Wf (loop e D L f)

------------------------------------------------------------------------
-- In range: every variable of c is a cell of the store (R-WHILE-M).

InR : Cmd → Store → Set
InR c σ = vmax c ≤ length σ

ass-in-range : ∀ {x e σ} → InR (x ^= e) σ → x < length σ
ass-in-range {x} {e} ir = ≤-trans (m≤m⊔n (suc x) (vmaxᵉ e)) ir

-- sub-commands stay in range
inR-seqˡ : ∀ {c d σ} → InR (c ⨾ d) σ → InR c σ
inR-seqˡ {c} {d} ir = ≤-trans (m≤m⊔n (vmax c) (vmax d)) ir

inR-seqʳ : ∀ {c d σ} → InR (c ⨾ d) σ → InR d σ
inR-seqʳ {c} {d} ir = ≤-trans (m≤n⊔m (vmax c) (vmax d)) ir

inR-condˡ : ∀ {e c d f σ} → InR (cond e c d f) σ → InR c σ
inR-condˡ {e} {c} {d} {f} ir =
  ≤-trans (m≤n⊔m (vmaxᵉ e) (vmax c))
          (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax c) (vmax d))
                   (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax c ⊔ vmax d) (vmaxᵉ f)) ir))

inR-condʳ : ∀ {e c d f σ} → InR (cond e c d f) σ → InR d σ
inR-condʳ {e} {c} {d} {f} ir =
  ≤-trans (m≤n⊔m (vmaxᵉ e ⊔ vmax c) (vmax d))
          (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax c ⊔ vmax d) (vmaxᵉ f)) ir)

inR-loopˡ : ∀ {e D L f σ} → InR (loop e D L f) σ → InR D σ
inR-loopˡ {e} {D} {L} {f} ir =
  ≤-trans (m≤n⊔m (vmaxᵉ e) (vmax D))
          (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax D) (vmax L))
                   (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax D ⊔ vmax L) (vmaxᵉ f)) ir))

inR-loopʳ : ∀ {e D L f σ} → InR (loop e D L f) σ → InR L σ
inR-loopʳ {e} {D} {L} {f} ir =
  ≤-trans (m≤n⊔m (vmaxᵉ e ⊔ vmax D) (vmax L))
          (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax D ⊔ vmax L) (vmaxᵉ f)) ir)

------------------------------------------------------------------------
-- Execution preserves the store's length (so the interpreter's `Vl` keeps
-- exactly M cells throughout a run -- the invariant its walk needs).

⇒-length  : ∀ {c σ τ k} → InR c σ → c ⊢ σ ⇒ τ ∣ k → length τ ≡ length σ
Rest-length : ∀ {e D L f σ τ n} → InR D σ → InR L σ
            → Rest e D L f σ τ n → length τ ≡ length σ

⇒-length ir e-skip = refl
⇒-length {x ^= e} {σ} ir (e-ass {u = u} _ _) =
  length-set σ x u (ass-in-range {x} {e} {σ} ir)
⇒-length {c ⨾ d} {σ} ir (e-seq {t = t} dc dd) =
  trans (⇒-length irdʹ dd) eqt
  where
    eqt : length t ≡ length σ
    eqt = ⇒-length (inR-seqˡ {c} {d} {σ} ir) dc
    irdʹ : InR d t
    irdʹ = subst (λ n → vmax d ≤ n) (sym eqt) (inR-seqʳ {c} {d} {σ} ir)
⇒-length {cond e c d f} {σ} ir (e-then _ dc _) = ⇒-length (inR-condˡ {e} {c} {d} {f} {σ} ir) dc
⇒-length {cond e c d f} {σ} ir (e-else _ dd _) = ⇒-length (inR-condʳ {e} {c} {d} {f} {σ} ir) dd
⇒-length {loop e D L f} {σ} ir (e-loop {t = t} _ dD rest) =
  trans (Rest-length {e} {D} {L} {f} irDʹ irLʹ rest) eqt
  where
    eqt : length t ≡ length σ
    eqt = ⇒-length (inR-loopˡ {e} {D} {L} {f} {σ} ir) dD
    irDʹ : InR D t
    irDʹ = subst (λ n → vmax D ≤ n) (sym eqt) (inR-loopˡ {e} {D} {L} {f} {σ} ir)
    irLʹ : InR L t
    irLʹ = subst (λ n → vmax L ≤ n) (sym eqt) (inR-loopʳ {e} {D} {L} {f} {σ} ir)

Rest-length _ _ (r-exit _) = refl
Rest-length {e} {D} {L} {f} {σ} irD irL (r-iter {x = x} {y = y} _ dL _ dD rest) =
  trans (Rest-length {e} {D} {L} {f} irD″ irL″ rest) (trans eqy eqx)
  where
    eqx : length x ≡ length σ
    eqx = ⇒-length irL dL
    irDʹ : InR D x
    irDʹ = subst (λ n → vmax D ≤ n) (sym eqx) irD
    irLʹ : InR L x
    irLʹ = subst (λ n → vmax L ≤ n) (sym eqx) irL
    eqy : length y ≡ length x
    eqy = ⇒-length irDʹ dD
    irD″ : InR D y
    irD″ = subst (λ n → vmax D ≤ n) (sym eqy) irDʹ
    irL″ : InR L y
    irL″ = subst (λ n → vmax L ≤ n) (sym eqy) irLʹ

-- the tests of a conditional / loop are in range too
inR-condT : ∀ {e c d f σ} → InR (cond e c d f) σ → vmaxᵉ e ≤ length σ
inR-condT {e} {c} {d} {f} ir =
  ≤-trans (m≤m⊔n (vmaxᵉ e) (vmax c))
          (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax c) (vmax d))
                   (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax c ⊔ vmax d) (vmaxᵉ f)) ir))

inR-condF : ∀ {e c d f σ} → InR (cond e c d f) σ → vmaxᵉ f ≤ length σ
inR-condF {e} {c} {d} {f} ir =
  ≤-trans (m≤n⊔m (vmaxᵉ e ⊔ vmax c ⊔ vmax d) (vmaxᵉ f)) ir

inR-loopT : ∀ {e D L f σ} → InR (loop e D L f) σ → vmaxᵉ e ≤ length σ
inR-loopT {e} {D} {L} {f} ir =
  ≤-trans (m≤m⊔n (vmaxᵉ e) (vmax D))
          (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax D) (vmax L))
                   (≤-trans (m≤m⊔n (vmaxᵉ e ⊔ vmax D ⊔ vmax L) (vmaxᵉ f)) ir))

inR-loopF : ∀ {e D L f σ} → InR (loop e D L f) σ → vmaxᵉ f ≤ length σ
inR-loopF {e} {D} {L} {f} ir =
  ≤-trans (m≤n⊔m (vmaxᵉ e ⊔ vmax D ⊔ vmax L) (vmaxᵉ f)) ir

-- an assignment's expression is in range
inR-assE : ∀ {x e σ} → InR (x ^= e) σ → vmaxᵉ e ≤ length σ
inR-assE {x} {e} ir = ≤-trans (m≤n⊔m (suc x) (vmaxᵉ e)) ir
