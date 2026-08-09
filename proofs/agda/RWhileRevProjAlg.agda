{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE ALGEBRA OF THE *REVERSIBLE* PROJECTIONS, part 1: garbage in the TEXT.
--
-- The classical tower collapses at level 3 (RWhileFutamuraAlg).  A reversible
-- specialiser cannot simply throw the static input away — a reversible
-- program is injective, so the information has to go somewhere
-- (FINDINGS_reversible_projections §4).  The question ④ asks is whether the
-- collapse survives that.  There are two places to put the information, and
-- they behave DIFFERENTLY.  This module does the first:
--
--   (c)  garbage in the residual's TEXT, on a dead branch.
--        This is `examples/spec_av_rev.rwhile` (`EMBED-GARB`: the dropped
--        values are pushed on GARB and embedded as the else-branch of a
--        constantly-true `if`, so they are never executed).  Measured:
--        comp = 1739 nodes of which 1517 is garbage, and [comp] still
--        answers correctly (FINDINGS §5, §6).
--
--   (b)  garbage in the OUTPUT, as a pair — the textbook "keep the input"
--        trick.  That is RWhileRevProjAlgPP, and there the collapse FAILS on
--        the nose.
--
-- RESULT FOR (c).  The dead-branch embedding is semantically transparent, so
-- a garbage-carrying specialiser satisfies RWhileRevProjPaper's `def-spec`
-- VERBATIM (`Embed.def-spec` below derives it).  Everything therefore goes
-- through unchanged, garbage and all:
--
--     fp4-rev        run cogen rspec ≡ cogen            (on the nose)
--     tower-collapse ∀ n → tower n ≡ cogen
--     tower-proj     ∀ n src d → snd (run (run (run (tower n) rint) src) d)
--                                  ≡ srcSem src d
--
-- and the garbage does NOT pile up: the level-n artefact is
-- `emb (γ rspec rspec) (mix rspec rspec)` for EVERY n ≥ 0
-- (`Embed.tower-carries`) — one flat layer whose content is a closed term,
-- not a nest that deepens with the height.  The answer itself never sees it
-- (`Embed.answer`: the output of the fp1 residual is ⟨src , ⟦src⟧ d⟩, code
-- depth 1, whatever the height of the tower above).
--
-- So: for the artefact's own design (dead-path embedding) the classical
-- degeneracy is preserved exactly.  That is not a triviality about the proof
-- — the SAME question answered for design (b) comes out negative.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileRevProjAlg where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

import RWhileRevProjPaper

------------------------------------------------------------------------
-- 1.  The algebra, over the paper's two equations.
------------------------------------------------------------------------

module RevAlgebra
  (U      : Set)
  (run    : U → U → U)
  (⟨_,_⟩  : U → U → U)
  (snd    : U → U)
  (snd-β  : ∀ a b → snd ⟨ a , b ⟩ ≡ b)
  (srcSem : U → U → U)
  (rint   : U)
  (rspec  : U)
  (def-rint : ∀ p d → run rint ⟨ p , d ⟩ ≡ ⟨ p , srcSem p d ⟩)
  (def-spec : ∀ p s d → run (run rspec ⟨ p , s ⟩) d ≡ run p ⟨ s , d ⟩)
  where

  open RWhileRevProjPaper.RevProjection
         U run ⟨_,_⟩ snd snd-β srcSem rint rspec def-rint def-spec public

  ----------------------------------------------------------------------
  -- Composition of specialisations (two uses of def-spec; no self-application).
  spec-compose : ∀ p s t d →
    run (run rspec ⟨ run rspec ⟨ p , s ⟩ , t ⟩) d ≡ run p ⟨ s , ⟨ t , d ⟩ ⟩
  spec-compose p s t d =
    trans (def-spec (run rspec ⟨ p , s ⟩) t d) (def-spec p s ⟨ t , d ⟩)

  ----------------------------------------------------------------------
  -- cogen is the specialiser, curried: two applications of cogen = one
  -- application of rspec.  fp2/fp3 of the paper are the instances p := rint.
  cogen-curry : ∀ p s → run (run cogen p) s ≡ run rspec ⟨ p , s ⟩
  cogen-curry p s =
    trans (cong (λ c → run c s) (def-spec rspec rspec p)) (def-spec rspec p s)

  ----------------------------------------------------------------------
  -- THE DEGENERACY.  One line, exactly as in the classical case: `cogen` is
  -- defined as `run rspec ⟨rspec,rspec⟩`, and def-spec at (rspec,rspec,rspec)
  -- says running it on rspec recomputes that.
  fp4-rev : run cogen rspec ≡ cogen
  fp4-rev = def-spec rspec rspec rspec

  Φ : U → U
  Φ X = run X rspec

  cogen-fixpoint : Φ cogen ≡ cogen
  cogen-fixpoint = fp4-rev

  ----------------------------------------------------------------------
  -- The tower at arbitrary height.
  tower : ℕ → U
  tower zero    = cogen
  tower (suc n) = Φ (tower n)

  tower-collapse : ∀ n → tower n ≡ cogen
  tower-collapse zero    = refl
  tower-collapse (suc n) = trans (cong Φ (tower-collapse n)) fp4-rev

  tower-curry : ∀ n p s → run (run (tower n) p) s ≡ run rspec ⟨ p , s ⟩
  tower-curry n p s =
    trans (cong (λ c → run (run c p) s) (tower-collapse n)) (cogen-curry p s)

  -- the level-n artefact is still a compiler generator: one `snd` at the very
  -- end recovers the source semantics, for every height n.
  tower-proj : ∀ n src d →
    snd (run (run (run (tower n) rint) src) d) ≡ srcSem src d
  tower-proj n src d =
    trans (cong (λ t → snd (run t d)) (tower-curry n rint src)) (rev-proj1 src d)

------------------------------------------------------------------------
-- 2.  A GARBAGE-CARRYING SPECIALISER SATISFIES THE SAME EQUATIONS.
--
-- `emb g r` is `r` with the garbage `g` embedded on a branch that never runs
-- (spec_av_rev's `EMBED-GARB`), `mix p s` is the clean residual, and the
-- specialiser outputs the two glued together.  The embedding is the reason
-- rspec is injective (g is recoverable from the text) and the reason the
-- equations do not notice (the branch is dead).
------------------------------------------------------------------------

module Embed
  (U      : Set)
  (run    : U → U → U)
  (⟨_,_⟩  : U → U → U)
  (snd    : U → U)
  (snd-β  : ∀ a b → snd ⟨ a , b ⟩ ≡ b)
  (srcSem : U → U → U)
  (rint   : U)
  (rspec  : U)
  (emb    : U → U → U)                 -- emb garbage residual
  (γ      : U → U → U)                 -- the garbage produced for ⟨p,s⟩
  (mix    : U → U → U)                 -- the clean residual
  (def-rint : ∀ p d → run rint ⟨ p , d ⟩ ≡ ⟨ p , srcSem p d ⟩)
  (dead   : ∀ g r d → run (emb g r) d ≡ run r d)          -- the branch is dead
  (out    : ∀ p s → run rspec ⟨ p , s ⟩ ≡ emb (γ p s) (mix p s))
  (mix-eq : ∀ p s d → run (mix p s) d ≡ run p ⟨ s , d ⟩)
  where

  -- The paper's def-spec is DERIVED, not assumed: dead code is invisible to
  -- the semantics.
  def-spec : ∀ p s d → run (run rspec ⟨ p , s ⟩) d ≡ run p ⟨ s , d ⟩
  def-spec p s d =
    trans (cong (λ r → run r d) (out p s))
          (trans (dead (γ p s) (mix p s) d) (mix-eq p s d))

  open RevAlgebra U run ⟨_,_⟩ snd snd-β srcSem rint rspec def-rint def-spec public

  ----------------------------------------------------------------------
  -- What the artefacts actually contain.  Each is ONE flat embedding whose
  -- garbage is determined by that level's two arguments.
  tgt-carries : ∀ src → tgt src ≡ emb (γ rint src) (mix rint src)
  tgt-carries src = out rint src

  comp-carries : comp ≡ emb (γ rspec rint) (mix rspec rint)
  comp-carries = out rspec rint

  cogen-carries : cogen ≡ emb (γ rspec rspec) (mix rspec rspec)
  cogen-carries = out rspec rspec

  -- NO ACCUMULATION.  Every level of the tower is the same one-layer term;
  -- the garbage at the fixed point is the closed term γ rspec rspec and does
  -- not grow with the height.
  tower-carries : ∀ n → tower n ≡ emb (γ rspec rspec) (mix rspec rspec)
  tower-carries n = trans (tower-collapse n) cogen-carries

  -- … and the garbage never reaches the answer: the fp1 residual outputs the
  -- source together with the result, code depth 1, for any height above it.
  answer : ∀ src d → run (tgt src) d ≡ ⟨ src , srcSem src d ⟩
  answer src d = trans (def-spec rint src d) (def-rint src d)
