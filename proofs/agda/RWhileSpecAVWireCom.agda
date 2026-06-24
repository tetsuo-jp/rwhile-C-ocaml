{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Tier-2 #5 (verified bridge, command layer): extend RWhileSpecAVWire from
-- EXPRESSIONS to PATTERNS, COMMANDS and whole PROGRAMS.
--
-- Program2DataRwhile encodes the full R-WHILE AST as an R-WHILE value:
--
--   transPat / d_pat (Program2DataRwhile.ml:37-45,106-110):
--     'var . i               variable (index = unary nil-count)
--     'val . v               literal value
--     'cons . (p . q)        cons pattern
--
--   transCom / d_com (Program2DataRwhile.ml:47-61,112-123):
--     'seq . (c . c)                              sequencing
--     'ass . (('var . i) . e)                     reversible assignment
--     'rep . (p . q)                              pattern replacement
--     'cond . (e . (t . (d . (f . nil))))         conditional (test/then/else/assert)
--     'loop . (e . (d . (l . (f . nil))))         loop (entry/do/loop/exit)
--
--   transProgram / data2program (Program2DataRwhile.ml:79-83,125-129):
--     (('var . i) . (c . ('var . j)))             read i; c; write j
--
-- We mirror each clause LINE BY LINE with encoders / parsers and prove the round
-- trips parsePat (encPat p) ≡ just p, parseCom (encCom c) ≡ just c,
-- parseProg (encProg p) ≡ just p — so the WHOLE program AST ↔ wire format is a
-- THEOREM (the syntactic half of a meaning-preserving translation, completing the
-- expression bridge of RWhileSpecAVWire).  Expressions embedded in commands reuse
-- encEx / parseEx, hence the worklist AV specialiser's γ-soundness (wire-sound)
-- applies to every expression inside a parsed command (`ass-exp-sound`).
--
-- The remaining (research-scale) item is the SEMANTIC half for commands: a
-- command-level operational semantics + AV specialiser with an operational
-- equivalence — see SPEC_AV_CORRESPONDENCE.md §5.  `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileSpecAVWireCom where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileAVSound using (Val; γ)
open import RWhileH2WorklistAV using (Ex; ⟦_⟧; avEval)
open import RWhileSpecAVWire using
  ( WVal; wNil; wAtom; wCons
  ; Tag; tVar; tVal; tCons; tSeq; tAss; tRep; tCond; tLoop
  ; embV; prjV; prj-emb
  ; encIdx; decIdx; dec-enc-idx
  ; encEx; parseEx; parse-enc; wire-sound )

------------------------------------------------------------------------
-- Patterns (mirror transPat / d_pat).

data Pat : Set where
  pVar  : ℕ → Pat
  pVal  : Val → Pat
  pCons : Pat → Pat → Pat

encPat : Pat → WVal
encPat (pVar n)    = wCons (wAtom tVar)  (encIdx n)
encPat (pVal v)    = wCons (wAtom tVal)  (embV v)
encPat (pCons a b) = wCons (wAtom tCons) (wCons (encPat a) (encPat b))

parsePat : WVal → Maybe Pat
parsePat (wCons (wAtom tVar) i) with decIdx i
... | just n  = just (pVar n)
... | nothing = nothing
parsePat (wCons (wAtom tVal) v) with prjV v
... | just v' = just (pVal v')
... | nothing = nothing
parsePat (wCons (wAtom tCons) (wCons a b)) with parsePat a | parsePat b
... | just a' | just b' = just (pCons a' b')
... | _       | _       = nothing
parsePat _ = nothing

parse-enc-pat : ∀ p → parsePat (encPat p) ≡ just p
parse-enc-pat (pVar n)    rewrite dec-enc-idx n = refl
parse-enc-pat (pVal v)    rewrite prj-emb v = refl
parse-enc-pat (pCons a b) rewrite parse-enc-pat a | parse-enc-pat b = refl

------------------------------------------------------------------------
-- Commands (mirror transCom / d_com).

data Com : Set where
  cSeq  : Com → Com → Com
  cAss  : ℕ → Ex → Com               -- 'ass . (('var . i) . e)
  cRep  : Pat → Pat → Com
  cCond : Ex → Com → Com → Ex → Com  -- test / then / else / assert
  cLoop : Ex → Com → Com → Ex → Com  -- entry / do / loop / exit

encCom : Com → WVal
encCom (cSeq a b)      = wCons (wAtom tSeq)  (wCons (encCom a) (encCom b))
encCom (cAss n e)      = wCons (wAtom tAss)  (wCons (wCons (wAtom tVar) (encIdx n)) (encEx e))
encCom (cRep p q)      = wCons (wAtom tRep)  (wCons (encPat p) (encPat q))
encCom (cCond e t d f) = wCons (wAtom tCond) (wCons (encEx e) (wCons (encCom t) (wCons (encCom d) (wCons (encEx f) wNil))))
encCom (cLoop e d l f) = wCons (wAtom tLoop) (wCons (encEx e) (wCons (encCom d) (wCons (encCom l) (wCons (encEx f) wNil))))

parseCom : WVal → Maybe Com
parseCom (wCons (wAtom tSeq) (wCons a b)) with parseCom a | parseCom b
... | just a' | just b' = just (cSeq a' b')
... | _       | _       = nothing
parseCom (wCons (wAtom tAss) (wCons (wCons (wAtom tVar) i) e)) with decIdx i | parseEx e
... | just n  | just e' = just (cAss n e')
... | _       | _       = nothing
parseCom (wCons (wAtom tRep) (wCons p q)) with parsePat p | parsePat q
... | just p' | just q' = just (cRep p' q')
... | _       | _       = nothing
parseCom (wCons (wAtom tCond) (wCons e (wCons t (wCons d (wCons f wNil)))))
  with parseEx e | parseCom t | parseCom d | parseEx f
... | just e' | just t' | just d' | just f' = just (cCond e' t' d' f')
... | _       | _       | _       | _       = nothing
parseCom (wCons (wAtom tLoop) (wCons e (wCons d (wCons l (wCons f wNil)))))
  with parseEx e | parseCom d | parseCom l | parseEx f
... | just e' | just d' | just l' | just f' = just (cLoop e' d' l' f')
... | _       | _       | _       | _       = nothing
parseCom _ = nothing

parse-enc-com : ∀ c → parseCom (encCom c) ≡ just c
parse-enc-com (cSeq a b)      rewrite parse-enc-com a | parse-enc-com b = refl
parse-enc-com (cAss n e)      rewrite dec-enc-idx n | parse-enc e = refl
parse-enc-com (cRep p q)      rewrite parse-enc-pat p | parse-enc-pat q = refl
parse-enc-com (cCond e t d f) rewrite parse-enc e | parse-enc-com t | parse-enc-com d | parse-enc f = refl
parse-enc-com (cLoop e d l f) rewrite parse-enc e | parse-enc-com d | parse-enc-com l | parse-enc f = refl

------------------------------------------------------------------------
-- Whole programs (mirror transProgram / data2program).

data Prog : Set where
  prog : ℕ → Com → ℕ → Prog          -- read i ; c ; write j

encProg : Prog → WVal
encProg (prog i c j) =
  wCons (wCons (wAtom tVar) (encIdx i))
        (wCons (encCom c) (wCons (wAtom tVar) (encIdx j)))

parseProg : WVal → Maybe Prog
parseProg (wCons (wCons (wAtom tVar) i) (wCons c (wCons (wAtom tVar) j)))
  with decIdx i | parseCom c | decIdx j
... | just i' | just c' | just j' = just (prog i' c' j')
... | _       | _       | _       = nothing
parseProg _ = nothing

parse-enc-prog : ∀ p → parseProg (encProg p) ≡ just p
parse-enc-prog (prog i c j) rewrite dec-enc-idx i | parse-enc-com c | dec-enc-idx j = refl

------------------------------------------------------------------------
-- Bridge to soundness: every expression embedded in a command parses to a
-- γ-sound AV residual (the worklist specialiser's wire-sound, reused).  This is
-- the semantic content carried by commands; full command-level operational
-- equivalence is the remaining research item (SPEC_AV_CORRESPONDENCE.md §5).

-- assignment 'ass n e: the residual built from its expression is γ-sound.
ass-exp-sound : ∀ (n : ℕ) e ρ → γ (avEval e) ρ ≡ ⟦ e ⟧ ρ
ass-exp-sound n e ρ = wire-sound e ρ

------------------------------------------------------------------------
-- Examples: encCom emits exactly the wire tree d_com decodes (checked by refl),
-- and the program round trip holds.

module Examples where
  open RWhileH2WorklistAV using (varN; exVal; exCons)
  open import RWhileAVSound using (vtrue)

  -- swap-ish: X ^= cons x1 x0   (assignment of a cons of two store slots to var 0)
  c0 : Com
  c0 = cAss 0 (exCons (varN 1) (varN 0))

  -- 'ass . (('var . nil) . ('cons . (('var . (nil.nil)) . ('var . nil))))
  c0-wire : WVal
  c0-wire = wCons (wAtom tAss)
              (wCons (wCons (wAtom tVar) wNil)
                     (wCons (wAtom tCons)
                       (wCons (wCons (wAtom tVar) (wCons wNil wNil))
                              (wCons (wAtom tVar) wNil))))

  c0-enc-ok : encCom c0 ≡ c0-wire
  c0-enc-ok = refl

  c0-roundtrip : parseCom c0-wire ≡ just c0
  c0-roundtrip = parse-enc-com c0

  -- a conditional with the trailing-nil terminator, exercising the 4-field shape.
  c1 : Com
  c1 = cCond (exVal vtrue) (cRep (pVar 0) (pVal vtrue)) (cRep (pVar 0) (pVal vtrue)) (exVal vtrue)

  c1-roundtrip : parseCom (encCom c1) ≡ just c1
  c1-roundtrip = parse-enc-com c1

  -- whole program: read 1; (X ^= cons x1 x0); write 0
  p0 : Prog
  p0 = prog 1 c0 0

  p0-roundtrip : parseProg (encProg p0) ≡ just p0
  p0-roundtrip = parse-enc-prog p0
