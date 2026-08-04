{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- ROUND-TRIP: what `RWhileSIShow` prints can be read back.
--
-- `showC` renders a `Cmd` in R-WHILE's concrete syntax, and `extract-si.sh`
-- writes the verified interpreter out with it.  For that text to *mean* the
-- Agda term, printing must lose nothing: no ambiguity, no missing brackets.
-- This module proves it at the TOKEN level -- the level where ambiguity
-- lives -- by giving a parser that follows `Rwhile.cf` and showing
--
--     parse (tokens c) ≡ just (c , [])
--
-- Tokens are produced in DIFFERENCE-LIST style (`tokV v ts` = the tokens of
-- `v` followed by `ts`), which removes `_++_` -- and with it every
-- associativity lemma -- from the proofs.  Parsers are fuel-indexed, like
-- `RWhileTime.exec`, so they are structurally terminating.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIParse where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import RWhileTime

------------------------------------------------------------------------
-- Tokens (one constructor per lexeme of Rwhile.cf).

data Tok : Set where
  tVar   : ℕ → Tok          -- X0, X1, ...
  tAtm   : ℕ → Tok          -- '0, '7, ...
  tNil   : Tok
  tLP tDot tRP : Tok        -- ( . )
  tCons tHd tTl tEq tPair : Tok
  tAss tSemi : Tok          -- ^=  ;
  tIf tThen tElse tFi : Tok
  tFrom tDo tLoop tUntil : Tok

------------------------------------------------------------------------
-- Printing to tokens (difference-list style).

tokV : V → List Tok → List Tok
tokV nil     ts = tNil ∷ ts
tokV (atm n) ts = tAtm n ∷ ts
tokV (a ∙ b) ts = tLP ∷ tokV a (tDot ∷ tokV b (tRP ∷ ts))

tokO : Opd → List Tok → List Tok
tokO (var x) ts = tVar x ∷ ts
tokO (cst v) ts = tokV v ts

tokE : Exp → List Tok → List Tok
tokE (opd a)   ts = tokO a ts
tokE (cns a b) ts = tCons ∷ tokO a (tokO b ts)
tokE (hdE a)   ts = tHd   ∷ tokO a ts
tokE (tlE a)   ts = tTl   ∷ tokO a ts
tokE (eqE a b) ts = tEq   ∷ tokO a (tokO b ts)
tokE (prE a)   ts = tPair ∷ tokO a ts

------------------------------------------------------------------------
-- Parsing (fuel-indexed: the fuel bounds the nesting depth of a value).

pV : ℕ → List Tok → Maybe (V × List Tok)
pV zero    _              = nothing
pV (suc n) (tNil ∷ ts)    = just (nil , ts)
pV (suc n) (tAtm m ∷ ts)  = just (atm m , ts)
pV (suc n) (tLP ∷ ts)     with pV n ts
... | just (a , tDot ∷ ts₁) with pV n ts₁
...   | just (b , tRP ∷ ts₂) = just (a ∙ b , ts₂)
...   | _                    = nothing
pV (suc n) (tLP ∷ ts) | _    = nothing
pV (suc n) _                 = nothing

-- one clause per leading token, so every application reduces as soon as
-- the first token is known (which is what the round-trip proofs need)

pO : ℕ → List Tok → Maybe (Opd × List Tok)
pO n (tVar x ∷ ts) = just (var x , ts)
pO n (tNil ∷ ts)   = just (cst nil , ts)
pO n (tAtm m ∷ ts) = just (cst (atm m) , ts)
pO n (tLP ∷ ts)    with pV n (tLP ∷ ts)
... | just (v , ts₁) = just (cst v , ts₁)
... | nothing        = nothing
pO n _ = nothing

pE : ℕ → List Tok → Maybe (Exp × List Tok)
pE n (tCons ∷ ts) with pO n ts
... | just (a , ts₁) with pO n ts₁
...   | just (b , ts₂) = just (cns a b , ts₂)
...   | nothing        = nothing
pE n (tCons ∷ ts) | nothing = nothing
pE n (tHd ∷ ts)   with pO n ts
... | just (a , ts₁) = just (hdE a , ts₁)
... | nothing        = nothing
pE n (tTl ∷ ts)   with pO n ts
... | just (a , ts₁) = just (tlE a , ts₁)
... | nothing        = nothing
pE n (tEq ∷ ts)   with pO n ts
... | just (a , ts₁) with pO n ts₁
...   | just (b , ts₂) = just (eqE a b , ts₂)
...   | nothing        = nothing
pE n (tEq ∷ ts) | nothing = nothing
pE n (tPair ∷ ts) with pO n ts
... | just (a , ts₁) = just (prE a , ts₁)
... | nothing        = nothing
pE n (tVar x ∷ ts) = just (opd (var x) , ts)
pE n (tNil ∷ ts)   = just (opd (cst nil) , ts)
pE n (tAtm m ∷ ts) = just (opd (cst (atm m)) , ts)
pE n (tLP ∷ ts)    with pO n (tLP ∷ ts)
... | just (a , ts₁) = just (opd a , ts₁)
... | nothing        = nothing
pE n _ = nothing

------------------------------------------------------------------------
-- Round-trip, for values, operands and expressions.

depth : V → ℕ
depth nil     = 0
depth (atm _) = 0
depth (a ∙ b) = suc (depth a ⊔ depth b)

pV-ok : ∀ n v ts → depth v ≤ n → pV (suc n) (tokV v ts) ≡ just (v , ts)
pV-ok n nil     ts _        = refl
pV-ok n (atm m) ts _        = refl
pV-ok (suc n) (a ∙ b) ts (s≤s le)
  rewrite pV-ok n a (tDot ∷ tokV b (tRP ∷ ts)) (≤-trans (m≤m⊔n (depth a) (depth b)) le)
        | pV-ok n b (tRP ∷ ts)                 (≤-trans (m≤n⊔m (depth a) (depth b)) le)
        = refl

depthO : Opd → ℕ
depthO (var _) = 0
depthO (cst v) = depth v

pO-ok : ∀ n a ts → depthO a ≤ n → pO (suc n) (tokO a ts) ≡ just (a , ts)
pO-ok n (var x)       ts _  = refl
pO-ok n (cst nil)     ts _  = refl
pO-ok n (cst (atm m)) ts _  = refl
pO-ok n (cst (a ∙ b)) ts le rewrite pV-ok n (a ∙ b) ts le = refl

depthE : Exp → ℕ
depthE (opd a)   = depthO a
depthE (cns a b) = depthO a ⊔ depthO b
depthE (hdE a)   = depthO a
depthE (tlE a)   = depthO a
depthE (eqE a b) = depthO a ⊔ depthO b
depthE (prE a)   = depthO a

pE-ok : ∀ n e ts → depthE e ≤ n → pE (suc n) (tokE e ts) ≡ just (e , ts)
pE-ok n (opd (var x))       ts _  = refl
pE-ok n (opd (cst nil))     ts _  = refl
pE-ok n (opd (cst (atm m))) ts _  = refl
pE-ok n (opd (cst (a ∙ b))) ts le rewrite pV-ok n (a ∙ b) ts le = refl
pE-ok n (cns a b) ts le
  rewrite pO-ok n a (tokO b ts) (≤-trans (m≤m⊔n (depthO a) (depthO b)) le)
        | pO-ok n b ts          (≤-trans (m≤n⊔m (depthO a) (depthO b)) le)
        = refl
pE-ok n (hdE a) ts le rewrite pO-ok n a ts le = refl
pE-ok n (tlE a) ts le rewrite pO-ok n a ts le = refl
pE-ok n (eqE a b) ts le
  rewrite pO-ok n a (tokO b ts) (≤-trans (m≤m⊔n (depthO a) (depthO b)) le)
        | pO-ok n b ts          (≤-trans (m≤n⊔m (depthO a) (depthO b)) le)
        = refl
pE-ok n (prE a) ts le rewrite pO-ok n a ts le = refl

------------------------------------------------------------------------
-- SEQUENCES: the one place where printing is NOT injective.
--
-- `showC (c ⨾ d) = showC c ++ ";" ++ showC d` flattens the tree, so
-- `(a ; b) ; c` and `a ; (b ; c)` print identically -- and R-WHILE's grammar
-- (`CSeq. Com ::= Com ";" Com1`, left-recursive) reassociates to the left
-- while `_⨾_` here is infixr.  So the extracted text denotes the same
-- command only UP TO ASSOCIATIVITY.
--
-- That is harmless, and this is the proof: reassociating preserves the
-- semantics AND the exact step count, so every theorem about the Agda term
-- transfers to the term the implementation's parser builds.

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

private
  eqR : ∀ a b c → suc (a + suc (b + c)) ≡ suc (suc (a + b) + c)
  eqR = solve 3 (λ a b c → con 1 :+ (a :+ (con 1 :+ (b :+ c))) :=
                           con 1 :+ ((con 1 :+ (a :+ b)) :+ c)) refl

seq-assocʳ : ∀ {a b c σ τ k} → ((a ⨾ b) ⨾ c) ⊢ σ ⇒ τ ∣ k → (a ⨾ (b ⨾ c)) ⊢ σ ⇒ τ ∣ k
seq-assocʳ {a} {b} {c} {σ} {τ} (e-seq {k = ka} {l = kc} (e-seq {k = ka′} {l = kb} da db) dc) =
  subst (λ i → (a ⨾ (b ⨾ c)) ⊢ σ ⇒ τ ∣ i) (eqR ka′ kb kc) (e-seq da (e-seq db dc))

seq-assocˡ : ∀ {a b c σ τ k} → (a ⨾ (b ⨾ c)) ⊢ σ ⇒ τ ∣ k → ((a ⨾ b) ⨾ c) ⊢ σ ⇒ τ ∣ k
seq-assocˡ {a} {b} {c} {σ} {τ} (e-seq {k = ka} da (e-seq {k = kb} {l = kc} db dc)) =
  subst (λ i → ((a ⨾ b) ⨾ c) ⊢ σ ⇒ τ ∣ i) (sym (eqR ka kb kc)) (e-seq (e-seq da db) dc)
