{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- program2data / data2program for the residual Code language, with the
-- round-trip  data2program ∘ program2data ≡ id  (gap G4, prerequisite of H2).
--
-- The reversible projections turn programs into data and back (the self-
-- interpreter's p2d, src/Program2DataRwhile.ml).  For the self-application
-- obligation H2 (RWhileFutamura2.spec-impl) one must be able to *feed a program
-- as input* — i.e. encode a residual `Code` as a `Val` and decode it again.
-- Here we give such an encoding for the AV residual language (RWhileAVSound's
-- `Code`) and machine-check that decoding undoes encoding.
--
-- Encoding: each constructor gets a distinct header tree Hk (a left spine of k
-- nils) in head position, with the payload(s) in the tail.  Headers are pairwise
-- distinct trees, so `d2p` decodes by matching the literal header; malformed
-- values fall through to a default.  `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileP2D where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂)
open import RWhileAVSound using (Val; ⟨⟩; _·_; Code; cVar; cVal; cHd; cTl; cCons; cEq; cPairp)

------------------------------------------------------------------------
-- program2data: encode a residual Code as a Val.
-- Header Hk = a left spine of k nils; payload(s) in the tail.

program2data : Code → Val
program2data cVar        = ⟨⟩ · ⟨⟩                                                        -- H0 · ⟨⟩
program2data (cVal v)    = (⟨⟩ · ⟨⟩) · v                                                  -- H1 · v
program2data (cHd c)     = ((⟨⟩ · ⟨⟩) · ⟨⟩) · program2data c                              -- H2 · ⌜c⌝
program2data (cTl c)     = (((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · program2data c                       -- H3 · ⌜c⌝
program2data (cCons a b) = ((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · (program2data a · program2data b)        -- H4 · ⟨⌜a⌝,⌜b⌝⟩
program2data (cEq a b)   = (((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · (program2data a · program2data b) -- H5 · ⟨⌜a⌝,⌜b⌝⟩
program2data (cPairp c)  = ((((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · program2data c -- H6 · ⌜c⌝

------------------------------------------------------------------------
-- data2program: decode by matching the literal header tree; default = cVar.

data2program : Val → Code
data2program (⟨⟩ · ⟨⟩)                                                       = cVar
data2program ((⟨⟩ · ⟨⟩) · v)                                                 = cVal v
data2program (((⟨⟩ · ⟨⟩) · ⟨⟩) · t)                                          = cHd (data2program t)
data2program ((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · t)                                   = cTl (data2program t)
data2program (((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · (a · b))                      = cCons (data2program a) (data2program b)
data2program ((((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · (a · b))               = cEq (data2program a) (data2program b)
data2program (((((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · t)              = cPairp (data2program t)
data2program _                                                               = cVar

------------------------------------------------------------------------
-- Round-trip: decoding undoes encoding (G4 core).

d2p∘p2d : ∀ c → data2program (program2data c) ≡ c
d2p∘p2d cVar        = refl
d2p∘p2d (cVal v)    = refl
d2p∘p2d (cHd c)     = cong cHd (d2p∘p2d c)
d2p∘p2d (cTl c)     = cong cTl (d2p∘p2d c)
d2p∘p2d (cCons a b) = cong₂ cCons (d2p∘p2d a) (d2p∘p2d b)
d2p∘p2d (cEq a b)   = cong₂ cEq (d2p∘p2d a) (d2p∘p2d b)
d2p∘p2d (cPairp c)  = cong cPairp (d2p∘p2d c)

-- Corollary: the encoding is injective (the property the paper's rspec needs:
-- a program is uniquely recoverable from its data form).
p2d-injective : ∀ {x y} → program2data x ≡ program2data y → x ≡ y
p2d-injective {x} {y} eq =
  trans (sym (d2p∘p2d x)) (trans (cong data2program eq) (d2p∘p2d y))
