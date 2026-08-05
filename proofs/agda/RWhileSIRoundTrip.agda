{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE ROUND-TRIP, AT THE INTERPRETER.
--
-- The text `extract-si.sh` writes out parses back to `nf SI`, which runs
-- exactly like `SI` (same stores, same step counts).  So the extracted
-- artifact really is the verified interpreter, not merely something that
-- looks like it.
--
-- Engineering note: stating this with `rewrite` costs 26.7 GB / 154 s,
-- because `rewrite` has to FIND the occurrences of `tokC (nf SI) []` by
-- matching against a 37 000-token term.  Passing the motive explicitly to
-- `subst` costs 0.43 GB / 4.6 s -- a 62x difference for the same theorem.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIRoundTrip where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import RWhileTime
open import RWhileSIParse
open import RWhileSINorm
open import RWhileSISim using (SI)

-- the interpreter's normal form is right-nested (decided by evaluation)
RN-nfSI : RN (nf SI)
RN-nfSI = RN! (nf SI)

-- ... so the printed text reads back as exactly that term
si-text : pC (suc (depthC (nf SI))) (tokC SI []) ≡ just (nf SI , [])
si-text = subst (λ ts → pC (suc (depthC (nf SI))) ts ≡ just (nf SI , []))
                (nf-tok SI []) (round-trip (nf SI) RN-nfSI)

-- ... and that term runs exactly like SI
si-text-runs : ∀ {σ τ k} → SI ⊢ σ ⇒ τ ∣ k → nf SI ⊢ σ ⇒ τ ∣ k
si-text-runs = nf-⇒
