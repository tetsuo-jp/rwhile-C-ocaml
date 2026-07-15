{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Extraction of the C1–C3 development: compile the VERIFIED wire-AST
-- semantics (RWhileWireSem), command-level AV specialiser (RWhileSpecCom)
-- and residualising hierarchy (RWhileSpecProg) to a native binary that,
-- at runtime, drives the whole third-projection chain on the swap
-- program:
--
--   cogen  = run specP (specP . ('S . specP))      (self-application)
--   comp   = run cogen  ('S . swapP)               (the compiler)
--   resid  = run comp   ('S . 'true)               (the VERIFIED residual)
--   result = run resid  d                          (= [swapP]((s . d)))
--
-- Every step it prints is covered by a machine-checked theorem
-- (fp3-cogen / fp2-compile / fp1-target = spec-contract), so this binary
-- is the "same code that carries the proofs" demonstrator — the
-- extraction half of C4a (the OCaml `wire-spec` group is the other
-- half: the 3-way differential against the real spec_av).
--
--   ./build-extract.sh ExtractSpecProg && ./ExtractSpecProg
------------------------------------------------------------------------

module ExtractSpecProg where

open import Data.String using (String; _++_)
open import Agda.Builtin.IO using (IO)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (0ℓ)
open import IO using (run; putStrLn; _>>_)
open import Data.Maybe using (Maybe; just; nothing)
open import RWhileAVSound using
  (Val; ⟨⟩; _·_; vtrue; Code; cVar; cVal; cHd; cTl; cCons; cEq; cPairp)
open import RWhileSpecAVWireCom using (Prog)
open import RWhileSpecProg
  using (U; val; wp; code; pair; tagS; papp; specP; comp3; comp2)
  renaming (run to runU)
open RWhileSpecProg.Witness using (swapP)

showV : Val → String
showV ⟨⟩      = "nil"
showV (a · b) = "(" ++ showV a ++ " . " ++ showV b ++ ")"

showC : Code → String
showC cVar        = "d"
showC (cVal v)    = "'" ++ showV v
showC (cHd c)     = "hd " ++ showC c
showC (cTl c)     = "tl " ++ showC c
showC (cCons a b) = "(cons " ++ showC a ++ " " ++ showC b ++ ")"
showC (cEq a b)   = "(=? " ++ showC a ++ " " ++ showC b ++ ")"
showC (cPairp c)  = "(pair? " ++ showC c ++ ")"

showU : U → String
showU (val v)    = showV v
showU (wp _)     = "<swapP>"
showU (code c)   = "code[" ++ showC c ++ "]"
showU (pair a b) = "(" ++ showU a ++ " . " ++ showU b ++ ")"
showU (tagS a)   = "('S . " ++ showU a ++ ")"
showU (papp p s) = "papp[" ++ showU p ++ " | " ++ showU s ++ "]"
showU specP      = "specP"

showM : Maybe U → String
showM (just u) = showU u
showM nothing  = "FAIL"

s0 : Val
s0 = vtrue                       -- the static input baked into the residual

d0 : Val
d0 = ⟨⟩ · (⟨⟩ · ⟨⟩)              -- a dynamic input

main : IO (⊤ {0ℓ})
main =
  run (putStrLn ("static  s = " ++ showV s0) >>
       putStrLn ("dynamic d = " ++ showV d0) >>
       putStrLn ("cogen = run specP (specP.('S.specP))  = "
                 ++ showM (runU 1 specP (pair specP (tagS specP)))) >>
       putStrLn ("fp3:  run cogen ('S.swapP) (compiler) = "
                 ++ showM (runU 2 comp3 (tagS (wp swapP)))) >>
       putStrLn ("fp2:  run compiler ('S.s)  (residual) = "
                 ++ showM (runU 12 (comp2 swapP) (tagS (val s0)))) >>
       putStrLn ("fp1:  run residual d                  = "
                 ++ showM (runU 1 (code (cCons cVar (cVal s0))) (val d0))) >>
       putStrLn ("      run source (s.d)  (must agree)  = "
                 ++ showM (runU 12 (wp swapP) (val (s0 · d0)))))
