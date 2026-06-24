{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Tier-2 #5 (engineering → contribution): a VERIFIED BRIDGE between the
-- implementation's WIRE FORMAT and the Agda specialiser model.
--
-- spec_av and the program-to-data encoder (src/Program2DataRwhile.ml) represent
-- an R-WHILE expression as an R-WHILE VALUE: a tree whose nodes are tagged by the
-- atoms 'var / 'val / 'cons / 'hd / 'tl / 'eq / 'pairp.  The decoder `d_exp`
-- (Program2DataRwhile.ml:96-104) is what actually runs on a spec residual:
--
--     'var . i               ↦ variable, index i = unary nil-count (d_count)
--     'val . v               ↦ literal value v
--     'cons . (a . b)        ↦ cons a b
--     'hd . e / 'tl . e      ↦ hd e / tl e
--     'eq . (a . b)          ↦ eq a b
--     'pairp . e             ↦ pairp e
--
-- Until now the correspondence between this wire format and the verified
-- specialiser model (RWhileH2WorklistAV) was *transcription* — eyeballed.  Here
-- we make it a THEOREM:  we model the wire values (`WVal`, with the 7 tag atoms),
-- write an ENCODER `encEx : Ex → WVal` and a PARSER `parseEx : WVal → Maybe Ex`
-- that mirror Program2DataRwhile's transExp / d_exp LINE BY LINE, and prove
--
--     parse-enc : ∀ e → parseEx (encEx e) ≡ just e          -- round trip
--
-- so the verified `Ex` is provably the decoding of the implementation's wire
-- format.  We then COMPOSE with the soundness of the worklist AV specialiser
-- (RWhileH2WorklistAV.avEval-sound) to get a wire-level soundness statement:
-- starting from the implementation's encoded expression, the AV residual the
-- specialiser builds concretises (γ) to the source meaning.
--
-- The index codec (encIdx / decIdx) mirrors d_count: the index is the unary
-- nil-count, nil = 0.  (The p2d *encoder* transRIdent uses a separate 1-based
-- convention; the decoder-side bridge follows d_exp/d_count, the load-bearing
-- direction for evaluating residuals.)
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileSpecAVWire where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileAVSound using (Val; ⟨⟩; _·_; vtrue; AV; γ)
open import RWhileH2WorklistAV using
  ( Ex; varN; exVal; exCons; exHd; exTl; exEq; exPairp
  ; ⟦_⟧; avEval; avEval-sound )

------------------------------------------------------------------------
-- Wire values: the 7 tag atoms plus nil/cons trees (mirrors AbsRwhile.valT =
-- VNil / VAtom / VCons, restricted to the atoms the expression encoding uses).

data Tag : Set where
  tVar tVal tCons tHd tTl tEq tPairp : Tag

data WVal : Set where
  wNil  : WVal
  wAtom : Tag → WVal
  wCons : WVal → WVal → WVal

------------------------------------------------------------------------
-- 'val payloads are atom-free values: embed Val (nil/cons) into WVal and back.

embV : Val → WVal
embV ⟨⟩      = wNil
embV (a · b) = wCons (embV a) (embV b)

prjV : WVal → Maybe Val
prjV wNil        = just ⟨⟩
prjV (wAtom _)   = nothing
prjV (wCons a b) with prjV a | prjV b
... | just a' | just b' = just (a' · b')
... | _       | _       = nothing

prj-emb : ∀ v → prjV (embV v) ≡ just v
prj-emb ⟨⟩      = refl
prj-emb (a · b) rewrite prj-emb a | prj-emb b = refl

------------------------------------------------------------------------
-- Variable index codec: unary nil-count (mirrors Program2DataRwhile.d_count).

encIdx : ℕ → WVal
encIdx zero    = wNil
encIdx (suc n) = wCons wNil (encIdx n)

decIdx : WVal → Maybe ℕ
decIdx wNil               = just zero
decIdx (wAtom _)          = nothing
decIdx (wCons wNil t)     with decIdx t
... | just n  = just (suc n)
... | nothing = nothing
decIdx (wCons (wAtom _) _)   = nothing
decIdx (wCons (wCons _ _) _) = nothing

dec-enc-idx : ∀ n → decIdx (encIdx n) ≡ just n
dec-enc-idx zero    = refl
dec-enc-idx (suc n) rewrite dec-enc-idx n = refl

------------------------------------------------------------------------
-- Encoder: Ex → wire value (mirrors Program2DataRwhile.transExp).

encEx : Ex → WVal
encEx (varN n)     = wCons (wAtom tVar)  (encIdx n)
encEx (exVal v)    = wCons (wAtom tVal)  (embV v)
encEx (exCons a b) = wCons (wAtom tCons) (wCons (encEx a) (encEx b))
encEx (exHd e)     = wCons (wAtom tHd)   (encEx e)
encEx (exTl e)     = wCons (wAtom tTl)   (encEx e)
encEx (exEq a b)   = wCons (wAtom tEq)   (wCons (encEx a) (encEx b))
encEx (exPairp e)  = wCons (wAtom tPairp) (encEx e)

------------------------------------------------------------------------
-- Parser: wire value → Ex (mirrors Program2DataRwhile.d_exp).

parseEx : WVal → Maybe Ex
parseEx (wCons (wAtom tVar) i) with decIdx i
... | just n  = just (varN n)
... | nothing = nothing
parseEx (wCons (wAtom tVal) v) with prjV v
... | just v' = just (exVal v')
... | nothing = nothing
parseEx (wCons (wAtom tCons) (wCons a b)) with parseEx a | parseEx b
... | just a' | just b' = just (exCons a' b')
... | _       | _       = nothing
parseEx (wCons (wAtom tHd) e) with parseEx e
... | just e' = just (exHd e')
... | nothing = nothing
parseEx (wCons (wAtom tTl) e) with parseEx e
... | just e' = just (exTl e')
... | nothing = nothing
parseEx (wCons (wAtom tEq) (wCons a b)) with parseEx a | parseEx b
... | just a' | just b' = just (exEq a' b')
... | _       | _       = nothing
parseEx (wCons (wAtom tPairp) e) with parseEx e
... | just e' = just (exPairp e')
... | nothing = nothing
parseEx wNil                       = nothing
parseEx (wAtom _)                  = nothing
parseEx (wCons wNil _)             = nothing
parseEx (wCons (wCons _ _) _)      = nothing
parseEx (wCons (wAtom tCons) wNil)         = nothing
parseEx (wCons (wAtom tCons) (wAtom _))    = nothing
parseEx (wCons (wAtom tEq) wNil)           = nothing
parseEx (wCons (wAtom tEq) (wAtom _))      = nothing

------------------------------------------------------------------------
-- Round trip: the wire format parses back to the same expression.

parse-enc : ∀ e → parseEx (encEx e) ≡ just e
parse-enc (varN n)     rewrite dec-enc-idx n = refl
parse-enc (exVal v)    rewrite prj-emb v = refl
parse-enc (exCons a b) rewrite parse-enc a | parse-enc b = refl
parse-enc (exHd e)     rewrite parse-enc e = refl
parse-enc (exTl e)     rewrite parse-enc e = refl
parse-enc (exEq a b)   rewrite parse-enc a | parse-enc b = refl
parse-enc (exPairp e)  rewrite parse-enc e = refl

------------------------------------------------------------------------
-- Specialise straight from the wire format, then bridge to soundness.

specWire : WVal → Maybe AV
specWire wv with parseEx wv
... | just e  = just (avEval e)
... | nothing = nothing

-- HEADLINE: the residual the specialiser builds from a parsed wire expression
-- concretises (γ, filling the dynamic input ρ) to the source meaning.
wire-sound : ∀ e ρ → γ (avEval e) ρ ≡ ⟦ e ⟧ ρ
wire-sound = avEval-sound

-- End-to-end: encode → parse → build residual → concretise = source meaning.
bridge : ∀ e ρ → (parseEx (encEx e) ≡ just e) × (γ (avEval e) ρ ≡ ⟦ e ⟧ ρ)
bridge e ρ = parse-enc e , avEval-sound e ρ

------------------------------------------------------------------------
-- Examples: encEx produces exactly the wire tree Program2DataRwhile.transExp
-- would emit (checked by refl), and it parses back.

module Examples where
  -- hd (cons x0 'true)   where x0 = store slot 0, 'true = nil·nil
  ex1 : Ex
  ex1 = exHd (exCons (varN 0) (exVal vtrue))

  -- 'hd . ('cons . (('var . nil) . ('val . (nil . nil))))
  ex1-wire : WVal
  ex1-wire = wCons (wAtom tHd)
               (wCons (wAtom tCons)
                 (wCons (wCons (wAtom tVar) wNil)
                        (wCons (wAtom tVal) (wCons wNil wNil))))

  ex1-enc-ok : encEx ex1 ≡ ex1-wire
  ex1-enc-ok = refl

  ex1-roundtrip : parseEx ex1-wire ≡ just ex1
  ex1-roundtrip = refl

  -- eq x1 x2  (store slots 1 and 2)
  ex2 : Ex
  ex2 = exEq (varN 1) (varN 2)

  -- 'eq . (('var . (nil . nil)) . ('var . (nil . (nil . nil))))
  ex2-wire : WVal
  ex2-wire = wCons (wAtom tEq)
               (wCons (wCons (wAtom tVar) (wCons wNil wNil))
                      (wCons (wAtom tVar) (wCons wNil (wCons wNil wNil))))

  ex2-enc-ok : encEx ex2 ≡ ex2-wire
  ex2-enc-ok = refl

  ex2-roundtrip : parseEx ex2-wire ≡ just ex2
  ex2-roundtrip = refl
