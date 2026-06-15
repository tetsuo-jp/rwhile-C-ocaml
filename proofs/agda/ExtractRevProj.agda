{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- RUN the SECOND reversible projection natively.
--
-- comp'' = ⟦rspec⟧(rspec.rint) is computed by self-applying the (verified,
-- --safe) specialiser to the reversible interpreter, then run on a source to
-- get a target, then run on data — showing the reversible simulation.
--
--   ./build-extract.sh ExtractRevProj && ./ExtractRevProj
------------------------------------------------------------------------

module ExtractRevProj where

open import Data.String using (String; _++_)
open import Agda.Builtin.IO using (IO)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (0ℓ)
open import IO using (putStrLn; _>>_) renaming (run to ioRun)

open import RWhileRevProjInst
  using (U; pair; papp; mkpapp; rintP; swapS; idS; ★; run; snd; srcRun; comp; tgt)

showU : U → String
showU (pair a b) = "(" ++ showU a ++ "." ++ showU b ++ ")"
showU (papp p s) = "papp(" ++ showU p ++ "," ++ showU s ++ ")"
showU mkpapp     = "rspec"
showU rintP      = "rint"
showU swapS      = "swap"
showU idS        = "id"
showU ★          = "*"

src : U
src = swapS

dat : U                              -- a pair of two distinct values
dat = pair ★ (pair ★ ★)

comp'' : U                           -- the SECOND reversible projection
comp'' = comp                        -- = ⟦rspec⟧(rspec.rint) = run mkpapp (pair mkpapp rintP)

target : U                           -- ⟦comp''⟧(src)
target = run comp'' src

result : U                           -- ⟦target⟧(dat) = (program . result)
result = run target dat

main : IO (⊤ {0ℓ})
main =
  ioRun (putStrLn ("rspec (specialiser)  = " ++ showU mkpapp) >>
         putStrLn ("rint  (rev. interp)  = " ++ showU rintP) >>
         putStrLn ("comp'' = run rspec (rspec.rint)   = " ++ showU comp'') >>
         putStrLn ("source program src   = " ++ showU src) >>
         putStrLn ("target = comp''(src) = " ++ showU target) >>
         putStrLn ("data                 = " ++ showU dat) >>
         putStrLn ("target(data)         = " ++ showU result ++ "   (program . result)") >>
         putStrLn ("snd target(data)     = " ++ showU (snd result) ++ "   = the reversible simulation") >>
         putStrLn ("srcSem swap data     = " ++ showU (srcRun swapS dat) ++ "   (matches snd ✓)"))
