{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Soundness of the residual simplifier `src/Simp.ml` (idea 1, Phase 2a):
-- the two transformations it performs preserve meaning (and reversibility).
--
-- Simp does (1) constant folding of closed expressions and (2) dead reversible-
-- branch elimination.  We machine-check the semantic core of both:
--
--   (1) the local folding rewrites on the residual expression language
--       (RWhileAVSound's `Code` / `⟦_⟧c`):  hd/tl/pairp of a cons fold to the
--       obvious subresult — each is meaning-preserving (`fold-*`).
--
--   (2) dead-branch elimination for the reversible conditional.  A reversible
--       `if e then T else E fi f` takes the THEN branch when the entry test e is
--       true and then ASSERTS the exit test f true; the ELSE branch when e is
--       false and asserts f false.  We model this forward semantics (`condF`,
--       a partial function via `Maybe`, mirroring EvalRwhile's CCond) and prove:
--         e,f constant TRUE   ⇒  condF e T E f s ≡ just (T s)     (else dead)
--         e,f constant FALSE  ⇒  condF e T E f s ≡ just (E s)     (then dead)
--       — exactly Simp's reduction `if (const) then C else D fi (const) ⇒ C|D`.
--       The dropped branch is genuinely unreachable and the constant assertions
--       always hold, so meaning and reversibility are preserved.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileSimpSound where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileAVSound using
  (Val; ⟨⟩; _·_; vtrue;
   Code; cVal; cHd; cTl; cCons; cPairp; ⟦_⟧c; hd; tl; pairp)

------------------------------------------------------------------------
-- (1) constant-folding rewrites are meaning-preserving on `Code`.

fold-hd : ∀ a b ρ → ⟦ cHd (cCons a b) ⟧c ρ ≡ ⟦ a ⟧c ρ
fold-hd a b ρ = refl

fold-tl : ∀ a b ρ → ⟦ cTl (cCons a b) ⟧c ρ ≡ ⟦ b ⟧c ρ
fold-tl a b ρ = refl

fold-pairp : ∀ a b ρ → ⟦ cPairp (cCons a b) ⟧c ρ ≡ ⟦ cVal vtrue ⟧c ρ
fold-pairp a b ρ = refl

-- folding a literal (cVal) is trivially meaning-preserving (it IS its value);
-- and the head/tail/pairp of a *closed* cons literal fold to literals:
fold-hd-lit : ∀ u v ρ → ⟦ cHd (cVal (u · v)) ⟧c ρ ≡ ⟦ cVal u ⟧c ρ
fold-hd-lit u v ρ = refl

fold-tl-lit : ∀ u v ρ → ⟦ cTl (cVal (u · v)) ⟧c ρ ≡ ⟦ cVal v ⟧c ρ
fold-tl-lit u v ρ = refl

------------------------------------------------------------------------
-- (2) dead reversible-branch elimination.

-- R-WHILE truth: a value is true iff it is non-nil.
istrue : Val → Bool
istrue ⟨⟩      = false
istrue (_ · _) = true

-- Forward semantics of `if e then T else E fi f` (store modelled as a Val):
--   then-branch when e true, asserting f true afterwards;
--   else-branch when e false, asserting f false afterwards.
-- `nothing` = the reversibility assertion failed (as in EvalRwhile's CCond).
condF : (Val → Val) → (Val → Val) → (Val → Val) → (Val → Val) → Val → Maybe Val
condF e T E f s with istrue (e s)
... | true  with istrue (f (T s))
...           | true  = just (T s)
...           | false = nothing
condF e T E f s | false with istrue (f (E s))
...                        | true  = nothing
...                        | false = just (E s)

-- "e is constantly true / false"
AllTrue  : (Val → Val) → Set
AllTrue  e = ∀ s → istrue (e s) ≡ true
AllFalse : (Val → Val) → Set
AllFalse e = ∀ s → istrue (e s) ≡ false

-- Dead-branch elimination: constant-true tests ⇒ reduces to the THEN branch.
deadbranch-true :
  ∀ e T E f → AllTrue e → AllTrue f → ∀ s → condF e T E f s ≡ just (T s)
deadbranch-true e T E f et ft s rewrite et s | ft (T s) = refl

-- constant-false tests ⇒ reduces to the ELSE branch.
deadbranch-false :
  ∀ e T E f → AllFalse e → AllFalse f → ∀ s → condF e T E f s ≡ just (E s)
deadbranch-false e T E f ef ff s rewrite ef s | ff (E s) = refl
