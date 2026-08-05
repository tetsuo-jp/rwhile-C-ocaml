{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- One-off instantiation of the round-trip theorem AT THE INTERPRETER.
--
-- Kept out of `check.sh` (its file name does not match `RWhile*.agda`)
-- because discharging `RN (nf SI)` by evaluation costs 26.7 GB / 254 s.
-- Re-verify with:   agda --safe ExtractRoundTrip.agda
--
-- What it says: the text `extract-si.sh` writes parses back to `nf SI`,
-- which runs exactly like `SI` (same stores, same step counts).
------------------------------------------------------------------------

module ExtractRoundTrip where

open import Data.Nat using (suc)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import RWhileTime
open import RWhileSIParse
open import RWhileSINorm
open import RWhileSISim using (SI)

RN-nfSI : RN (nf SI)
RN-nfSI = RN! (nf SI)

si-text : pC (suc (depthC (nf SI))) (tokC SI []) ≡ just (nf SI , [])
si-text rewrite sym (nf-tok SI []) = round-trip (nf SI) RN-nfSI

si-text-runs : ∀ {σ τ k} → SI ⊢ σ ⇒ τ ∣ k → nf SI ⊢ σ ⇒ τ ∣ k
si-text-runs = nf-⇒
