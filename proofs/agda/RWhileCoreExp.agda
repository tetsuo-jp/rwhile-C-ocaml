{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Reflecting the implementation's Core IR expression/pattern NORMALIZATION
-- (src/Core.ml: norm_exp / norm_pat / eval_cexp) into Agda, and proving it
-- semantics-preserving.
--
-- Core.ml turns the surface expression/pattern language (with list sugar) into
-- a normalized core sub-language (cexp/cpat) by desugaring list literals to
-- cons-chains and rejecting extensions.  Here we model the SOURCE and CORE
-- expression/pattern languages, the normalizer, and both evaluators, and prove:
--
--   norm-correct      : evalC σ (norm e)  ≡ evalS σ e            (expressions)
--   read-norm-correct : readC σ (normP p) ≡ readS σ p           (patterns)
--
-- i.e. normalization preserves meaning, so the implementation's Core evaluator
-- (which runs on the normalized forms) computes the same thing as the surface
-- language — the property the `core-ir` differential tests check empirically.
------------------------------------------------------------------------

module RWhileCoreExp where

open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (yes; no)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import RWhileValStore using (Val; nil; cons; Store)

------------------------------------------------------------------------
-- helpers on values

eqV : Val → Val → Bool
eqV nil        nil        = true
eqV nil        (cons _ _) = false
eqV (cons _ _) nil        = false
eqV (cons a b) (cons c d) = eqV a c ∧ eqV b d

bval : Bool → Val
bval true  = cons nil nil      -- vtrue
bval false = nil               -- vfalse

isCons : Val → Bool
isCons (cons _ _) = true
isCons nil        = false

hdV : Val → Maybe Val
hdV (cons h _) = just h
hdV nil        = nothing
tlV : Val → Maybe Val
tlV (cons _ t) = just t
tlV nil        = nothing

------------------------------------------------------------------------
-- SOURCE expressions (with list sugar) and CORE expressions (normalized)

data SExp : Set where
  sVar  : ℕ → SExp
  sVal  : Val → SExp
  sCons : SExp → SExp → SExp
  sHd   : SExp → SExp
  sTl   : SExp → SExp
  sEq   : SExp → SExp → SExp
  sPair : SExp → SExp
  sList : List SExp → SExp        -- the surface sugar

data CExp : Set where
  xVar  : ℕ → CExp
  xVal  : Val → CExp
  xCons : CExp → CExp → CExp
  xHd   : CExp → CExp
  xTl   : CExp → CExp
  xEq   : CExp → CExp → CExp
  xPair : CExp → CExp             -- NO list constructor

------------------------------------------------------------------------
-- evaluators (read-only; mirror Core.ml eval_cexp and EvalRwhile evalExp)

-- evalS / evalSL mutual (explicit list recursion so termination is structural)
evalS  : Store → SExp → Maybe Val
evalSL : Store → List SExp → Maybe Val
evalS σ (sVar x)    = just (σ x)
evalS σ (sVal v)    = just v
evalS σ (sCons a b) = evalS σ a >>= λ va → evalS σ b >>= λ vb → just (cons va vb)
evalS σ (sHd e)     = evalS σ e >>= hdV
evalS σ (sTl e)     = evalS σ e >>= tlV
evalS σ (sEq a b)   = evalS σ a >>= λ va → evalS σ b >>= λ vb → just (bval (eqV va vb))
evalS σ (sPair e)   = evalS σ e >>= λ v → just (bval (isCons v))
evalS σ (sList es)  = evalSL σ es
evalSL σ []         = just nil
evalSL σ (e ∷ es)   = evalS σ e >>= λ v → evalSL σ es >>= λ vs → just (cons v vs)

evalC : Store → CExp → Maybe Val
evalC σ (xVar x)    = just (σ x)
evalC σ (xVal v)    = just v
evalC σ (xCons a b) = evalC σ a >>= λ va → evalC σ b >>= λ vb → just (cons va vb)
evalC σ (xHd e)     = evalC σ e >>= hdV
evalC σ (xTl e)     = evalC σ e >>= tlV
evalC σ (xEq a b)   = evalC σ a >>= λ va → evalC σ b >>= λ vb → just (bval (eqV va vb))
evalC σ (xPair e)   = evalC σ e >>= λ v → just (bval (isCons v))

------------------------------------------------------------------------
-- normalization (mirrors Core.ml norm_exp: list sugar -> cons-chain)

norm  : SExp → CExp
normL : List SExp → CExp
norm (sVar x)    = xVar x
norm (sVal v)    = xVal v
norm (sCons a b) = xCons (norm a) (norm b)
norm (sHd e)     = xHd (norm e)
norm (sTl e)     = xTl (norm e)
norm (sEq a b)   = xEq (norm a) (norm b)
norm (sPair e)   = xPair (norm e)
norm (sList es)  = normL es
normL []         = xVal nil
normL (e ∷ es)   = xCons (norm e) (normL es)

------------------------------------------------------------------------
-- THEOREM: normalization preserves expression semantics.

norm-correct   : ∀ σ e  → evalC σ (norm e)  ≡ evalS σ e
norm-correct-l : ∀ σ es → evalC σ (normL es) ≡ evalSL σ es

norm-correct σ (sVar x)    = refl
norm-correct σ (sVal v)    = refl
norm-correct σ (sCons a b) rewrite norm-correct σ a | norm-correct σ b = refl
norm-correct σ (sHd e)     rewrite norm-correct σ e = refl
norm-correct σ (sTl e)     rewrite norm-correct σ e = refl
norm-correct σ (sEq a b)   rewrite norm-correct σ a | norm-correct σ b = refl
norm-correct σ (sPair e)   rewrite norm-correct σ e = refl
norm-correct σ (sList es)  = norm-correct-l σ es

norm-correct-l σ []       = refl
norm-correct-l σ (e ∷ es) rewrite norm-correct σ e | norm-correct-l σ es = refl

------------------------------------------------------------------------
-- PATTERNS: source (with list sugar) and core (normalized), pattern READ
-- (consuming variables), and the normalization-correctness theorem.

setNil : ℕ → Store → Store
setNil x σ y with x ≟ y
... | yes _ = nil
... | no  _ = σ y

data SPat : Set where
  pVar  : ℕ → SPat
  pVal  : Val → SPat
  pCons : SPat → SPat → SPat
  pList : List SPat → SPat

data CPat : Set where
  cVar  : ℕ → CPat
  cVal  : Val → CPat
  cCons : CPat → CPat → CPat

-- read a pattern: returns the value read and the store with the pattern's
-- variables cleared (mirrors EvalRwhile.evalPat / Core.read_cpat).
readC : Store → CPat → (Val × Store)
readC σ (cVar x)    = (σ x , setNil x σ)
readC σ (cVal v)    = (v , σ)
readC σ (cCons p q) = let (d1 , σ1) = readC σ p in
                      let (d2 , σ2) = readC σ1 q in (cons d1 d2 , σ2)

readS  : Store → SPat → (Val × Store)
readSL : Store → List SPat → (Val × Store)
readS σ (pVar x)    = (σ x , setNil x σ)
readS σ (pVal v)    = (v , σ)
readS σ (pCons p q) = let (d1 , σ1) = readS σ p in
                      let (d2 , σ2) = readS σ1 q in (cons d1 d2 , σ2)
readS σ (pList ps)  = readSL σ ps
readSL σ []         = (nil , σ)
readSL σ (p ∷ ps)   = let (d1 , σ1) = readS σ p in
                      let (d2 , σ2) = readSL σ1 ps in (cons d1 d2 , σ2)

normP  : SPat → CPat
normPL : List SPat → CPat
normP (pVar x)    = cVar x
normP (pVal v)    = cVal v
normP (pCons p q) = cCons (normP p) (normP q)
normP (pList ps)  = normPL ps
normPL []         = cVal nil
normPL (p ∷ ps)   = cCons (normP p) (normPL ps)

-- THEOREM: pattern normalization preserves the read semantics.
read-norm-correct   : ∀ σ p  → readC σ (normP p)  ≡ readS σ p
read-norm-correct-l : ∀ σ ps → readC σ (normPL ps) ≡ readSL σ ps

read-norm-correct σ (pVar x)    = refl
read-norm-correct σ (pVal v)    = refl
read-norm-correct σ (pCons p q) with readS σ p | read-norm-correct σ p
... | (d1 , σ1) | refl with readS σ1 q | read-norm-correct σ1 q
...   | (d2 , σ2) | refl = refl
read-norm-correct σ (pList ps)  = read-norm-correct-l σ ps

read-norm-correct-l σ []        = refl
read-norm-correct-l σ (p ∷ ps) with readS σ p | read-norm-correct σ p
... | (d1 , σ1) | refl with readSL σ1 ps | read-norm-correct-l σ1 ps
...   | (d2 , σ2) | refl = refl
