{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Printing the formalised core in R-WHILE's CONCRETE SYNTAX.
--
-- This is the other half of the differential story (`RWhileSIP2D` checks
-- the encoding, this checks the language): a `Cmd` of this development is
-- printed as text that `src/ri` parses and runs, so the verified
-- interpreter `SI` can be extracted and measured against its proved bound
-- (see `ExtractSI.agda`).
--
-- Two syntactic accommodations, both forced by the implementation's grammar:
--   * variables are the 19 interpreter registers, printed `X0 .. X18`
--     (`Rwhile.cf`: RIdent = upper (letter|digit|'-'|'\'')*)
--   * `skip` is not in the implementation's language; it only ever occurs
--     in a branch position here, and the grammar has EMPTY branches
--     (BThenNone / BElseNone / BDoNone / BLoopNone), so it prints as nothing
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIShow where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime

showVal : V → String
showVal nil     = "nil"
showVal (atm n) = "'" ++ show n
showVal (a ∙ b) = "(" ++ showVal a ++ " . " ++ showVal b ++ ")"

showO : Opd → String
showO (var x) = "X" ++ show x
showO (cst v) = showVal v

showE : Exp → String
showE (opd a)   = showO a
showE (cns a b) = "cons " ++ showO a ++ " " ++ showO b
showE (hdE a)   = "hd " ++ showO a
showE (tlE a)   = "tl " ++ showO a
showE (eqE a b) = "=? " ++ showO a ++ " " ++ showO b
showE (prE a)   = "pair? " ++ showO a

-- `skip` in a branch position prints as the empty branch
showC   : Cmd → String
showBr  : String → Cmd → String     -- keyword, branch

showC skip           = "X0 ^= nil"          -- (only if it ever stands alone)
showC (x ^= e)       = "X" ++ show x ++ " ^= " ++ showE e
showC (c ⨾ d)        = showC c ++ ";\n" ++ showC d
showC (cond e c d f) = "if " ++ showE e ++ showBr "then" c ++ showBr "else" d
                     ++ " fi " ++ showE f
showC (loop e D L f) = "from " ++ showE e ++ showBr "do" D ++ showBr "loop" L
                     ++ " until " ++ showE f

showBr kw skip = ""
showBr kw c    = " " ++ kw ++ " " ++ showC c ++ " "

-- a whole program: the interpreter reads its todo stack and writes the done
-- stack, i.e. `read Cd; SI; write Dn`
showProg : Cmd → String
showProg c = "read X0;\n" ++ showC c ++ ";\nwrite X1\n"

------------------------------------------------------------------------
-- Tests: the printer's output for small commands, checked by the type
-- checker (the same programs appear in `RWhileSIP2D`'s p2d tests).

private
  t₁ : showC (1 ^= opd (var 0)) ≡ "X1 ^= X0"
  t₁ = refl

  t₂ : showC (1 ^= cns (var 0) (cst (atm 7))) ≡ "X1 ^= cons X0 '7"
  t₂ = refl

  t₃ : showC (1 ^= prE (var 0)) ≡ "X1 ^= pair? X0"
  t₃ = refl

  t₄ : showC (cond (eqE (var 1) (var 0)) (1 ^= opd (var 0)) skip (eqE (var 1) (var 0)))
     ≡ "if =? X1 X0 then X1 ^= X0  fi =? X1 X0"
  t₄ = refl

  t₅ : showC (loop (eqE (var 1) (cst nil)) skip (0 ^= opd (cst (atm 7)))
                   (eqE (var 1) (cst (atm 7))))
     ≡ "from =? X1 nil loop X0 ^= '7  until =? X1 '7"
  t₅ = refl
