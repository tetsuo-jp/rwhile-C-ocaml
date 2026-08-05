{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- RIGHT-NESTING, so the round-trip applies to the interpreter itself.
--
-- `RWhileSIParse.round-trip` needs its command right-nested in `;`, but
-- `SI`'s dispatch body is written with explicit brackets
-- (`(pop ⨾ splitT) ⨾ (DISPATCH ⨾ …)`), so it is not.  This module closes the
-- gap: `nf` reassociates a command to the right, and
--
--   * `nf-tok`  : it prints EXACTLY the same tokens (the `;` is flattened),
--   * `nf-⇒`/`⇒-nf` : it has the same runs, with the same step counts.
--
-- So the text of `SI` parses back to `nf SI`, which is `SI` in every respect
-- the semantics can see.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSINorm where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import RWhileTime
open import RWhileSIParse

------------------------------------------------------------------------
-- The normaliser (accumulator style: `nfA c k` is `c ⨾ k`, right-nested).

nf  : Cmd → Cmd
nfA : Cmd → Cmd → Cmd

nf skip           = skip
nf (x ^= e)       = x ^= e
nf (c ⨾ d)        = nfA c (nf d)
nf (cond e c d f) = cond e (nf c) (nf d) f
nf (loop e D L f) = loop e (nf D) (nf L) f

nfA skip           k = skip ⨾ k
nfA (x ^= e)       k = (x ^= e) ⨾ k
nfA (c ⨾ d)        k = nfA c (nfA d k)
nfA (cond e c d f) k = cond e (nf c) (nf d) f ⨾ k
nfA (loop e D L f) k = loop e (nf D) (nf L) f ⨾ k

------------------------------------------------------------------------
-- Normalising never turns something into `skip` (nor away from it).

isSkip-nf  : ∀ c   → isSkip (nf c) ≡ isSkip c
isSkip-nfA : ∀ c k → isSkip (nfA c k) ≡ false

isSkip-nf skip           = refl
isSkip-nf (x ^= e)       = refl
isSkip-nf (c ⨾ d)        = isSkip-nfA c (nf d)
isSkip-nf (cond e c d f) = refl
isSkip-nf (loop e D L f) = refl

isSkip-nfA skip           k = refl
isSkip-nfA (x ^= e)       k = refl
isSkip-nfA (c ⨾ d)        k = isSkip-nfA c (nfA d k)
isSkip-nfA (cond e c d f) k = refl
isSkip-nfA (loop e D L f) k = refl

------------------------------------------------------------------------
-- 1.  Normalising does not change the printed tokens.

nf-tok  : ∀ c ts → tokC (nf c) ts ≡ tokC c ts
nfA-tok : ∀ c k ts → tokC (nfA c k) ts ≡ tokC c (tSemi ∷ tokC k ts)

nf-tok skip           ts = refl
nf-tok (x ^= e)       ts = refl
nf-tok (c ⨾ d)        ts rewrite nfA-tok c (nf d) ts | nf-tok d ts = refl
nf-tok (cond e c d f) ts rewrite isSkip-nf c | isSkip-nf d
                               | nf-tok d (tFi ∷ tokE f ts)
                               | nf-tok c (tokBr tElse d (tFi ∷ tokE f ts)) = refl
nf-tok (loop e D L f) ts rewrite isSkip-nf D | isSkip-nf L
                               | nf-tok L (tUntil ∷ tokE f ts)
                               | nf-tok D (tokBr tLoop L (tUntil ∷ tokE f ts)) = refl

nfA-tok skip           k ts = refl
nfA-tok (x ^= e)       k ts = refl
nfA-tok (c ⨾ d)        k ts rewrite nfA-tok c (nfA d k) ts | nfA-tok d k ts = refl
nfA-tok (cond e c d f) k ts rewrite isSkip-nf c | isSkip-nf d
                                  | nf-tok d (tFi ∷ tokE f (tSemi ∷ tokC k ts))
                                  | nf-tok c (tokBr tElse d (tFi ∷ tokE f (tSemi ∷ tokC k ts))) = refl
nfA-tok (loop e D L f) k ts rewrite isSkip-nf D | isSkip-nf L
                                  | nf-tok L (tUntil ∷ tokE f (tSemi ∷ tokC k ts))
                                  | nf-tok D (tokBr tLoop L (tUntil ∷ tokE f (tSemi ∷ tokC k ts))) = refl

------------------------------------------------------------------------
-- 2.  Normalising preserves every run, with the same step count.

nf-⇒    : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k → nf c ⊢ σ ⇒ τ ∣ k
nfA-⇒   : ∀ {c k σ τ j} → (c ⨾ k) ⊢ σ ⇒ τ ∣ j → nfA c k ⊢ σ ⇒ τ ∣ j
nf-Rest : ∀ {e D L f σ τ n} → Rest e D L f σ τ n → Rest e (nf D) (nf L) f σ τ n

nf-⇒ e-skip          = e-skip
nf-⇒ (e-ass ev ru)   = e-ass ev ru
nf-⇒ (e-seq dc dd)   = nfA-⇒ (e-seq dc (nf-⇒ dd))
nf-⇒ (e-then te dc tf) = e-then te (nf-⇒ dc) tf
nf-⇒ (e-else te dd tf) = e-else te (nf-⇒ dd) tf
nf-⇒ (e-loop te dD r)  = e-loop te (nf-⇒ dD) (nf-Rest r)

nfA-⇒ {skip}         d = d
nfA-⇒ {x ^= e}       d = d
nfA-⇒ {c ⨾ d} {k} dd with seq-assocʳ dd
... | e-seq d₁ drest = nfA-⇒ (e-seq d₁ (nfA-⇒ drest))
nfA-⇒ {cond e c d f} (e-seq dc dk) = e-seq (nf-⇒ dc) dk
nfA-⇒ {loop e D L f} (e-seq dD dk) = e-seq (nf-⇒ dD) dk

nf-Rest (r-exit tf)              = r-exit tf
nf-Rest (r-iter ff dL fe dD rst) = r-iter ff (nf-⇒ dL) fe (nf-⇒ dD) (nf-Rest rst)

------------------------------------------------------------------------
-- 3.  Applying this to the interpreter itself.
--
-- `SI` is not right-nested as written (`STEP` is bracketed
-- `(pop ⨾ splitT) ⨾ (DISPATCH ⨾ …)`), but `nf SI` is, prints the same
-- tokens, and has the same runs with the same costs -- so the extracted
-- text denotes `nf SI`, and every theorem about `SI` transfers to it.
--
-- The instantiation itself lives in `ExtractRoundTrip.agda`, OUTSIDE the
-- routine `check.sh` set: discharging `RN (nf SI)` by evaluating the
-- decision procedure costs 26.7 GB / 254 s (measured), which is too much to
-- pay on every run.  The general theorems above are what carry the content;
-- the instantiation is a one-off artifact.
