{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Extraction of the FIRST FUTAMURA PROJECTION: compile the verified
-- specialiser `mix` (RWhileFutamura, --safe) to a native binary that
-- compiles a source op-program to a residual and runs both, demonstrating
-- fp1 (run (mix src) ≡ int src) at runtime.
--
--   ./build-extract.sh ExtractFutamura && ./ExtractFutamura
------------------------------------------------------------------------

module ExtractFutamura where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import Agda.Builtin.IO using (IO)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (0ℓ)
open import IO using (run; putStrLn; _>>_)

open import RWhileValStore using (Val; nil; cons)
open import RWhileFutamura using (Op; `swap; `id; Prim; doSwap; mix; int)
                           renaming (run to runC)

showV : Val → String
showV nil        = "nil"
showV (cons a b) = "(" ++ showV a ++ "." ++ showV b ++ ")"

showPair : Val × Val → String
showPair (a , b) = "(" ++ showV a ++ " , " ++ showV b ++ ")"

showOp : Op → String
showOp `swap = "swap"
showOp `id   = "id"

showOps : List Op → String
showOps []       = ""
showOps (o ∷ []) = showOp o
showOps (o ∷ os) = showOp o ++ "," ++ showOps os

showComp : List Prim → String
showComp []           = ""
showComp (doSwap ∷ []) = "doSwap"
showComp (doSwap ∷ cs) = "doSwap," ++ showComp cs

src : List Op
src = `swap ∷ `id ∷ `swap ∷ `id ∷ []     -- a source program

dat : Val × Val
dat = (nil , cons nil nil)

main : IO (⊤ {0ℓ})
main =
  run (putStrLn ("source program     [" ++ showOps src ++ "]  (len " ++ show (length src) ++ ")") >>
       putStrLn ("compiled residual  [" ++ showComp (mix src) ++ "]  (len " ++ show (length (mix src)) ++ ")  -- dispatch & id removed") >>
       putStrLn ("data                " ++ showPair dat) >>
       putStrLn ("int src dat       = " ++ showPair (int src dat)) >>
       putStrLn ("runC (mix src) dat = " ++ showPair (runC (mix src) dat) ++ "   (equal, by the proved fp1)"))
