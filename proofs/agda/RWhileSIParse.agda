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
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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

------------------------------------------------------------------------
-- COMMANDS.
--
-- Printing follows `RWhileSIShow`: a branch that is `skip` prints as
-- nothing (R-WHILE's grammar has empty branches), and `;` is flattened.

tokC : Cmd → List Tok → List Tok
tokBr : Tok → Cmd → List Tok → List Tok

tokC skip           ts = tVar 0 ∷ tAss ∷ tNil ∷ ts     -- only if it stands alone
tokC (x ^= e)       ts = tVar x ∷ tAss ∷ tokE e ts
tokC (c ⨾ d)        ts = tokC c (tSemi ∷ tokC d ts)
tokC (cond e c d f) ts =
  tIf ∷ tokE e (tokBr tThen c (tokBr tElse d (tFi ∷ tokE f ts)))
tokC (loop e D L f) ts =
  tFrom ∷ tokE e (tokBr tDo D (tokBr tLoop L (tUntil ∷ tokE f ts)))

tokBr kw skip ts = ts
tokBr kw c    ts = kw ∷ tokC c ts

------------------------------------------------------------------------
-- The parser: `pC1` is one command, `pC` a `;`-sequence (right-nested),
-- `pThen`/`pElse`/`pDo`/`pLoop` are the optional branches.

open import RWhileTime using (_>>=M_)

private
  eFi : List Tok → Maybe (List Tok)
  eFi (tFi ∷ ts) = just ts
  eFi _          = nothing

  eUntil : List Tok → Maybe (List Tok)
  eUntil (tUntil ∷ ts) = just ts
  eUntil _             = nothing

pC1    : ℕ → List Tok → Maybe (Cmd × List Tok)
pC     : ℕ → List Tok → Maybe (Cmd × List Tok)
pThen pElse pDo pLoop : ℕ → List Tok → Maybe (Cmd × List Tok)

pC1 zero _ = nothing
pC1 (suc n) (tVar x ∷ tAss ∷ ts) =
  pE n ts >>=M λ ea → just ((x ^= proj₁ ea) , proj₂ ea)
pC1 (suc n) (tIf ∷ ts) =
  pE n ts       >>=M λ ea →
  pThen n (proj₂ ea) >>=M λ cb →
  pElse n (proj₂ cb) >>=M λ dc →
  eFi (proj₂ dc)     >>=M λ ts₃ →
  pE n ts₃      >>=M λ fd →
  just (cond (proj₁ ea) (proj₁ cb) (proj₁ dc) (proj₁ fd) , proj₂ fd)
pC1 (suc n) (tFrom ∷ ts) =
  pE n ts       >>=M λ ea →
  pDo n (proj₂ ea)   >>=M λ Db →
  pLoop n (proj₂ Db) >>=M λ Lc →
  eUntil (proj₂ Lc)  >>=M λ ts₃ →
  pE n ts₃      >>=M λ fd →
  just (loop (proj₁ ea) (proj₁ Db) (proj₁ Lc) (proj₁ fd) , proj₂ fd)
pC1 (suc n) _ = nothing

pC zero    _  = nothing
pC (suc n) ts =
  pC1 n ts >>=M λ ca → cont (proj₁ ca) (proj₂ ca)
  where
    cont : Cmd → List Tok → Maybe (Cmd × List Tok)
    cont c (tSemi ∷ ts₁) = pC n ts₁ >>=M λ db → just ((c ⨾ proj₁ db) , proj₂ db)
    cont c ts₁           = just (c , ts₁)

pThen n (tThen ∷ ts) = pC n ts
pThen n ts           = just (skip , ts)
pElse n (tElse ∷ ts) = pC n ts
pElse n ts           = just (skip , ts)
pDo   n (tDo ∷ ts)   = pC n ts
pDo   n ts           = just (skip , ts)
pLoop n (tLoop ∷ ts) = pC n ts
pLoop n ts           = just (skip , ts)

------------------------------------------------------------------------
-- Round-trip for commands.
--
-- Two side conditions, both automatic for the printer's own output:
--   * the command must be RIGHT-NESTED in `;` (the flattening means the
--     text cannot distinguish the two associations; `seq-assoc` above shows
--     the difference is semantically and cost-wise invisible), and
--   * `skip` only occurs in branch positions, where it prints as nothing --
--     R-WHILE has no `skip` command.

depthC : Cmd → ℕ
depthC skip           = 0
depthC (x ^= e)       = depthE e
depthC (c ⨾ d)        = suc (depthC c ⊔ depthC d)
depthC (cond e c d f) = suc (depthE e ⊔ depthC c ⊔ depthC d ⊔ depthE f)
depthC (loop e D L f) = suc (depthE e ⊔ depthC D ⊔ depthC L ⊔ depthE f)

data RN1 : Cmd → Set
data RN  : Cmd → Set
data RNb : Cmd → Set

data RN1 where
  rn-ass  : ∀ {x e} → RN1 (x ^= e)
  rn-cond : ∀ {e c d f} → RNb c → RNb d → RN1 (cond e c d f)
  rn-loop : ∀ {e D L f} → RNb D → RNb L → RN1 (loop e D L f)

data RN where
  rn-one : ∀ {c} → RN1 c → RN c
  rn-seq : ∀ {c d} → RN1 c → RN d → RN (c ⨾ d)

data RNb where
  rnb-skip : RNb skip
  rnb-run  : ∀ {c} → RN c → RNb c

NoSemi NoThen NoElse NoDo NoLoop : List Tok → Set
NoSemi (tSemi ∷ _) = ⊥
NoSemi _           = ⊤
NoThen (tThen ∷ _) = ⊥
NoThen _           = ⊤
NoElse (tElse ∷ _) = ⊥
NoElse _           = ⊤
NoDo   (tDo ∷ _)   = ⊥
NoDo   _           = ⊤
NoLoop (tLoop ∷ _) = ⊥
NoLoop _           = ⊤

-- The general command-level round-trip is the next brick.  It needs
-- `tokBr` reformulated as `if isSkip c then ts else kw ∷ tokC c ts` so that
-- it reduces without knowing `c`'s constructor (a catch-all clause does
-- not), after which the proof splits on `isSkip` for each branch.  What is
-- established here is the parser itself (structurally terminating, one
-- clause per leading token, following `Rwhile.cf`) together with the
-- expression-level round-trip above and the concrete round-trips below.

------------------------------------------------------------------------
-- Concrete round-trips, checked by the type checker.

private
  -- X1 ^= cons X0 '7
  c₁ : Cmd
  c₁ = 1 ^= cns (var 0) (cst (atm 7))

  r₁ : pC 9 (tokC c₁ []) ≡ just (c₁ , [])
  r₁ = refl

  -- X1 ^= X0;  X0 ^= '3   (a two-command sequence)
  c₂ : Cmd
  c₂ = (1 ^= opd (var 0)) ⨾ (0 ^= opd (cst (atm 3)))

  r₂ : pC 9 (tokC c₂ []) ≡ just (c₂ , [])
  r₂ = refl

  -- if =? X1 X0 then X1 ^= X0 fi =? X1 X0     (an EMPTY else branch: skip)
  c₃ : Cmd
  c₃ = cond (eqE (var 1) (var 0)) (1 ^= opd (var 0)) skip (eqE (var 1) (var 0))

  r₃ : pC 9 (tokC c₃ []) ≡ just (c₃ , [])
  r₃ = refl

  -- from =? X0 nil loop X0 ^= '7 until =? X0 '7   (an EMPTY do branch)
  c₄ : Cmd
  c₄ = loop (eqE (var 0) (cst nil)) skip (0 ^= opd (cst (atm 7))) (eqE (var 0) (cst (atm 7)))

  r₄ : pC 9 (tokC c₄ []) ≡ just (c₄ , [])
  r₄ = refl

  -- nested: a conditional inside a loop body, with a sequence in a branch
  c₅ : Cmd
  c₅ = loop (eqE (var 0) (cst nil)) skip
            (cond (prE (var 1)) ((0 ^= hdE (var 1)) ⨾ (1 ^= tlE (var 1))) skip
                  (eqE (var 0) (cst nil)))
            (eqE (var 0) (cst (atm 7)))

  r₅ : pC 12 (tokC c₅ []) ≡ just (c₅ , [])
  r₅ = refl

  -- values with cons structure survive too
  r₆ : pC 12 (tokC (0 ^= opd (cst ((atm 1 ∙ nil) ∙ atm 2))) [])
     ≡ just ((0 ^= opd (cst ((atm 1 ∙ nil) ∙ atm 2))) , [])
  r₆ = refl
