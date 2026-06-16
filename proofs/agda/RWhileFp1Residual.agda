{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- fp1 at PROOF level: the ACTUAL residual that R-WHILE's spec_av produces
-- for [spec_av]((ri_min . swap)) is proved correct for ALL inputs.
--
-- The residual (decoded from the real run; src/spec_av.rwhile) is the
-- straight-line reversible program
--
--     read V2;
--       V0 <= V2;                          -- move input to V0
--       cons V3 V4 <= V0;                  -- split (a.b): V3=a, V4=b, V0:=nil
--       V2 <= cons 'swap (cons V4 V3);     -- rebuild (swap . (b.a))
--     write V2
--
-- We model its three pattern-replacements faithfully (read consumes its source
-- variables; a cons-write splits a cons value; a cons-read rebuilds) over a
-- four-variable store, and prove:
--
--     fp1-swap-correct : ∀ a b →
--         output (run residual (input (cons a b))) ≡ cons swap (cons b a)
--                                                  = (src . ⟦swap⟧ (a.b))
--
-- i.e. for EVERY pair input the residual reversibly simulates swap (snd = the
-- swapped pair, fst = the source tag).  Unlike the `core-ir`/exhaustive tests
-- (finitely many inputs), this is a proof for all a,b.  It certifies the
-- concrete fp1 output of spec_av (not spec_av itself).
------------------------------------------------------------------------

module RWhileFp1Residual where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Values: binary trees with atoms (nil = `at 0`, the source tag swap = `at 1`).
data V : Set where
  at   : ℕ → V
  cons : V → V → V

nilV : V
nilV = at 0
swap : V
swap = at 1

-- A four-variable store (V0, V2, V3, V4 — exactly the residual's variables).
record St : Set where
  constructor st
  field V0 V2 V3 V4 : V
open St

input : V → St
input d = st nilV d nilV nilV

output : St → V
output s = V2 s

-- the three pattern-replacements of the residual, modelled faithfully.
rep1 : St → St                              -- V0 <= V2  (read V2, write V0)
rep1 s = st (V2 s) nilV (V3 s) (V4 s)

rep2 : St → St                              -- cons V3 V4 <= V0  (split V0)
rep2 s with V0 s
... | cons a b = st nilV (V2 s) a b
... | at _     = s                          -- (non-cons: swap is undefined; unused here)

rep3 : St → St                              -- V2 <= cons 'swap (cons V4 V3)
rep3 s = st (V0 s) (cons swap (cons (V4 s) (V3 s))) nilV nilV

residual : St → St
residual s = rep3 (rep2 (rep1 s))

------------------------------------------------------------------------
-- THEOREM: the residual reversibly simulates swap on every pair input.

fp1-swap-correct : ∀ a b → output (residual (input (cons a b))) ≡ cons swap (cons b a)
fp1-swap-correct a b = refl

------------------------------------------------------------------------
-- ri_min `id` residual:  V0 <= V2;  V0 ^= nil;  V2 <= cons 'id V0
-- (the `^= nil` is XOR with nil = identity, so it is modelled as a no-op).

idT : V
idT = at 2

res-id : St → St
res-id s = let s1 = rep1 s in              -- V0 := input, V2 := nil
           st nilV (cons idT (V0 s1)) (V3 s1) (V4 s1)   -- V2 <= cons 'id V0

fp1-id-correct : ∀ d → output (res-id (input d)) ≡ cons idT d
fp1-id-correct d = refl

------------------------------------------------------------------------
-- ri_seq single-swap residuals (net), parameterised by the op-list tag `prog`:
--   V0 <= V2;  (^= nil)*;  cons V4 V3 <= V0;  (^= nil)*;  V2 <= cons prog (cons V3 V4)
-- (the `^= nil` ops are identities; variable renaming vs ri_min is irrelevant.)

split-build : V → St → St
split-build prog s with V0 s
... | cons a b = st nilV (cons prog (cons b a)) nilV nilV
... | at _     = s

res-seq-swap : V → St → St
res-seq-swap prog s = split-build prog (rep1 s)

fp1-seq-swap-correct : ∀ prog a b →
  output (res-seq-swap prog (input (cons a b))) ≡ cons prog (cons b a)
fp1-seq-swap-correct prog a b = refl

-- concrete op-list tags ([swap] and [id,swap], both net to one data swap)
seq-swap-tag   : V
seq-swap-tag   = cons swap nilV                  -- [swap]
seq-idswap-tag : V
seq-idswap-tag = cons idT (cons swap nilV)        -- [id,swap]

fp1-ri_seq-swap   : ∀ a b →
  output (res-seq-swap seq-swap-tag   (input (cons a b))) ≡ cons seq-swap-tag   (cons b a)
fp1-ri_seq-swap   a b = refl
fp1-ri_seq-idswap : ∀ a b →
  output (res-seq-swap seq-idswap-tag (input (cons a b))) ≡ cons seq-idswap-tag (cons b a)
fp1-ri_seq-idswap a b = refl
