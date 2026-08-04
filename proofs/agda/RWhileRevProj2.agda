{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The SECOND (and third) REVERSIBLE projection, concretely and faithfully.
--
-- Unlike RWhileFutamura/RWhileFutamura2 (which prove the *classical*, clean
-- projection `run (mix src) ≡ int src`, i.e. the residual computes the result
-- DIRECTLY with no garbage), this file models the paper's REVERSIBLE
-- projection:
--
--   * the interpreter `rintP` is PROGRAM-PRESERVING — it echoes the source in
--     its output (the garbage):   run rintP ⟨ src , d ⟩ ≡ ⟨ src , sem src d ⟩
--     (this is the paper's eq:def_rint with proj = snd);
--   * the projection `proj = snd` recovers the result, discarding the garbage;
--   * the specialiser `spec` is REVERSIBLE (injective): `spec p s = clos p s`
--     RETAINS the pair (p , s) in a constructor, so (p , s) is recoverable from
--     the residual — exactly the paper's requirement that rspec be injective
--     (the static program/data must be reconstructible from the residual).
--
-- Both H1 (spec correctness) and H2 (spec self-applicability) hold by
-- computation (refl), so the SECOND projection
--      compiler = spec specP rintP ,   run compiler src ≡ target src
-- and the THIRD
--      cogen    = spec specP specP ,   run cogen rintP ≡ compiler
-- are proved, AND the generated programs are shown to be reversible
-- simulations of the source (snd ∘ run = sem).
--
-- HONEST SCOPE (same caveat as RWhileFutamura2Inst): `spec` here packs (p,s)
-- into a built-in closure constructor `clos` rather than residualising into a
-- straight-line R-WHILE program.  That keeps it self-applicable by
-- construction; a real R-WHILE rspec must residualise STRUCTURALLY (the open
-- engineering).  What is new vs. the existing Agda Futamura files: this is the
-- REVERSIBLE projection (program-preserving interpreter + garbage + snd +
-- injective specialiser), faithful to §3.3–§3.4, not the clean classical one.
------------------------------------------------------------------------

module RWhileRevProj2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- One universal type: programs = data = residuals (needed for self-application).
data U : Set where
  ⟨_,_⟩       : U → U → U   -- pairing / cons of (static . dynamic)
  aSwap aId   : U           -- two object-language op tags (also serve as leaf data)
  rintP specP : U           -- the reversible interpreter / the specialiser, AS programs
  clos        : U → U → U   -- specialised closure  (= spec p s); RETAINS p and s

-- Object-language semantics: the op `aSwap` swaps a pair; anything else = id.
sem : U → U → U
sem aSwap ⟨ a , b ⟩ = ⟨ b , a ⟩
sem _      d         = d

-- The projection proj = snd (second component of a pair; identity otherwise).
sndU : U → U
sndU ⟨ a , b ⟩ = b
sndU x         = x

-- The universal evaluator.  `clos` recurses on a structurally smaller program,
-- so `run` is total (accepted by --safe without TERMINATING).
run : U → U → U
run (clos p s)  d         = run p ⟨ s , d ⟩          -- H1 by definition
run specP       ⟨ p , s ⟩ = clos p s                  -- H2 by definition (self-applicable)
run specP       d         = d
run rintP       ⟨ src , d ⟩ = ⟨ src , sem src d ⟩     -- PROGRAM-PRESERVING interpreter
run rintP       d         = d
run ⟨ a , b ⟩   d         = d
run aSwap       d         = d
run aId         d         = d

------------------------------------------------------------------------
-- The specialiser and the three artefacts.

spec : U → U → U
spec p s = clos p s

target : U → U                 -- target src = the fp1 residual tgt''
target src = spec rintP src

compiler : U                   -- comp'' = spec specP rintP   (eq:rev_proj2)
compiler = spec specP rintP

cogen : U                      -- cogen' = spec specP specP   (eq:rev_proj3)
cogen = spec specP specP

------------------------------------------------------------------------
-- H1 / H2: the two facts the whole hierarchy rests on, both by refl.

H1 : ∀ p s d → run (spec p s) d ≡ run p ⟨ s , d ⟩
H1 p s d = refl

H2 : ∀ p s → run specP ⟨ p , s ⟩ ≡ spec p s
H2 p s = refl

------------------------------------------------------------------------
-- The interpreter is program-preserving: the source `src` is echoed in the
-- output (this echoed copy is the GARBAGE the reversible projection retains).

program-preserved : ∀ src d → run (target src) d ≡ ⟨ src , sem src d ⟩
program-preserved src d = refl

------------------------------------------------------------------------
-- FIRST reversible projection (proj = snd):  snd ∘ ⟦tgt''⟧ ≡ ⟦src⟧.

rev-proj1 : ∀ src d → sndU (run (target src) d) ≡ sem src d
rev-proj1 src d = refl

------------------------------------------------------------------------
-- SECOND reversible projection: the compiler maps each source to its fp1
-- target (fp2), and that generated target reversibly simulates the source.

fp2 : ∀ src → run compiler src ≡ target src
fp2 src = refl

rev-proj2 : ∀ src d → sndU (run (run compiler src) d) ≡ sem src d
rev-proj2 src d = refl

------------------------------------------------------------------------
-- THIRD reversible projection: cogen maps the interpreter to the compiler
-- (fp3), and the doubly-generated program still reversibly simulates.

fp3 : run cogen rintP ≡ compiler
fp3 = refl

rev-proj3 : ∀ src d → sndU (run (run (run cogen rintP) src) d) ≡ sem src d
rev-proj3 src d = refl

------------------------------------------------------------------------
-- Non-vacuity: concrete distinct programs, by pure computation (refl).
-- src = aSwap, data = ⟨ aId , aSwap ⟩:  the residual keeps the program aSwap
-- (garbage) and swaps the data; snd recovers the swapped pair.

_ : run (target aSwap) ⟨ aId , aSwap ⟩ ≡ ⟨ aSwap , ⟨ aSwap , aId ⟩ ⟩
_ = refl

_ : sndU (run (target aSwap) ⟨ aId , aSwap ⟩) ≡ ⟨ aSwap , aId ⟩
_ = refl

-- the compiler is a concrete, distinct program (= clos specP rintP):
compiler-is : compiler ≡ clos specP rintP
compiler-is = refl

-- cogen on the interpreter computes the compiler:
_ : run cogen rintP ≡ clos specP rintP
_ = refl
