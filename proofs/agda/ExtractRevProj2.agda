{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Extraction of the SECOND REVERSIBLE projection: compile the verified
-- development RWhileRevProj2 (--safe) to a native binary that, at runtime,
--
--   * runs the program-preserving reversible interpreter (echoes the source
--     = the garbage),
--   * runs the compiler  comp'' = spec specP rintP  on a source, obtaining the
--     fp1 target (fp2 : run compiler src ≡ target src, proved),
--   * runs that generated target on data and recovers the result with snd
--     (rev-proj2, proved),
--   * and runs cogen to regenerate the compiler (fp3, proved).
--
--   ./build-extract.sh ExtractRevProj2 && ./ExtractRevProj2
------------------------------------------------------------------------

module ExtractRevProj2 where

open import Data.String using (String; _++_)
open import Agda.Builtin.IO using (IO)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (0ℓ)
open import IO using (run; putStrLn; _>>_)

open import RWhileRevProj2
  using (U; ⟨_,_⟩; aSwap; aId; rintP; specP; clos;
         sem; sndU; spec; compiler; target; cogen)
  renaming (run to runU)

showU : U → String
showU ⟨ a , b ⟩ = "(" ++ showU a ++ " . " ++ showU b ++ ")"
showU aSwap     = "swap"
showU aId       = "id"
showU rintP     = "rint"
showU specP     = "spec"
showU (clos p s) = "clos[" ++ showU p ++ " | " ++ showU s ++ "]"

src : U
src = aSwap                       -- the source program (one reversible op)

dat : U
dat = ⟨ aId , aSwap ⟩             -- input data, a pair (a . b)

main : IO (⊤ {0ℓ})
main =
  run (putStrLn ("source program   src  = " ++ showU src) >>
       putStrLn ("data             dat  = " ++ showU dat) >>
       putStrLn ("rint echoes src:  run rint (src.dat) = " ++ showU (runU rintP ⟨ src , dat ⟩)
                  ++ "   -- (src . result): src is the garbage") >>
       putStrLn ("compiler  comp'' = spec spec rint     = " ++ showU compiler) >>
       putStrLn ("fp2: run comp'' src (= target)        = " ++ showU (runU compiler src)) >>
       putStrLn ("run (run comp'' src) dat              = " ++ showU (runU (runU compiler src) dat)
                  ++ "   -- generated target, program preserved") >>
       putStrLn ("snd (...) = result of [src](dat)      = " ++ showU (sndU (runU (runU compiler src) dat))) >>
       putStrLn ("---- third reversible projection (full chain from cogen) ----") >>
       putStrLn ("cogen = spec spec spec                = " ++ showU cogen) >>
       putStrLn ("fp3: run cogen rint (= comp'')        = " ++ showU (runU cogen rintP)) >>
       putStrLn ("  then [comp''] src (= target)        = " ++ showU (runU (runU cogen rintP) src)) >>
       putStrLn ("  then run target dat                 = " ++ showU (runU (runU (runU cogen rintP) src) dat)
                  ++ "   -- program preserved") >>
       putStrLn ("  snd (...) = result of [src](dat)    = " ++ showU (sndU (runU (runU (runU cogen rintP) src) dat))))
