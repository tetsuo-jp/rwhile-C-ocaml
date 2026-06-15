{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Extraction demo: compile the VERIFIED reversible update `rupdF`
-- (proved equivalent to the relational RAss in RWhileExecConcrete, --safe)
-- into a native binary via Agda's GHC backend.
--
-- This demonstrates the "replace the implementation by extraction" route:
-- the same Agda code that carries the reversibility/determinism proofs is
-- ordinary runnable code.  Here we toggle variable 0 with the value (nil.nil)
-- and then toggle it AGAIN; reversibility means we get back to nil.
--
--   agda --compile Extract.agda && ./Extract
------------------------------------------------------------------------

module Extract where

open import Data.Nat using (ℕ; zero)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; _++_)
open import IO using (run; putStrLn; _>>_)
open import Agda.Builtin.IO using (IO)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (0ℓ)

open import RWhileValStore using (Val; nil; cons; Store)
open import RWhileExecConcrete using (rupdF)

showV : Val → String
showV nil        = "nil"
showV (cons a b) = "(" ++ showV a ++ " . " ++ showV b ++ ")"

-- initial store: every variable is nil
σ0 : Store
σ0 _ = nil

V : Val
V = cons nil nil          -- the value to XOR-assign into variable 0

at0 : Maybe Store → String
at0 (just σ) = showV (σ zero)
at0 nothing  = "<stuck>"

-- toggle variable 0 by V, twice (reversible: should return to nil)
toggle2 : Store → Maybe Store
toggle2 σ with rupdF zero V σ
... | just σ1 = rupdF zero V σ1
... | nothing = nothing

main : IO (⊤ {0ℓ})
main =
  run (putStrLn ("V0 initially            = " ++ showV (σ0 zero)) >>
       putStrLn ("V0 after  x ^= (nil.nil) = " ++ at0 (rupdF zero V σ0)) >>
       putStrLn ("V0 after  toggling twice = " ++ at0 (toggle2 σ0)))
