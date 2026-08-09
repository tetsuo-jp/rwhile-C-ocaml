{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE ALGEBRA OF THE *REVERSIBLE* PROJECTIONS, part 2: garbage in the OUTPUT
-- — and the classical degeneracy FAILS.
--
-- A reversible specialiser must be injective, so the static input cannot be
-- erased.  RWhileRevProjAlg covers the design the artefact uses (put it on a
-- dead branch of the residual's TEXT), where nothing changes.  This module
-- covers the other, equally standard design:
--
--     run rspec ⟨p,s⟩  ≡  ⟨ γ p s , mix p s ⟩
--
-- the specialiser EMITS the garbage next to the residual — the "keep the
-- input" trick that RWhileRevProjGen.input-preserving-inj shows always makes
-- a reversible version exist, and the same shape as the program-preserving
-- interpreter of RWhileJonesRev (`⟦q⟧ d ≡ ⌜p⌝ ⊗ ⟦p⟧ d`) but applied to the
-- SPECIALISER rather than to the interpreter.
--
-- WHAT CHANGES.
--
--   * `comp-run`     the compiler's output is ⟨ γ rint src , tgt src ⟩, not
--                    `tgt src`: the obligation the interpreter carries at
--                    level 1 is inherited by every level above it.
--   * `fp4-shape`    run cogen rspec ≡ ⟨ γ rspec rspec , cogen ⟩
--   * `fp4-fails`    hence  run cogen rspec ≢ cogen  — the classical
--                    degeneracy is FALSE on the nose.  The refutation is not
--                    a quirk of one model: it follows from the pairing being
--                    non-cyclic (`⟨a,b⟩ ≢ b`), which holds in every tree
--                    model, R-WHILE's included.
--   * `fp4-clean`    snd (run cogen rspec) ≡ cogen — it holds EXACTLY modulo
--                    one projection.  That is the corrected statement.
--   * `tower-collapse` the tower still collapses, but only if the projection
--                    is inserted at every level (tower (suc n) =
--                    snd (run (tower n) rspec)).  Without it, level 1 is
--                    already wrong (`raw-1-fails`) and level 2 is not even
--                    determined by the hypotheses: nothing here says what
--                    `run ⟨a,b⟩ d` is, because a pair is not a program.
--
-- WHAT DOES NOT CHANGE — the worry that the code NESTS is unfounded:
--
--   * `answer-shape` the fp1 residual still answers ⟨ src , ⟦src⟧ d ⟩, code
--                    depth 1, no matter how high the tower above it is;
--   * `cleanup-once` each level needs exactly one projection, and the
--                    garbage it discards is that level's own ⟨p,s⟩ — a flat
--                    layer, discharged immediately, never carried into the
--                    next.
--
-- So the honest summary of ④(ii) for the reversible case: the collapse is
-- preserved, the EQUATION is not.  Which of the two designs one is in
-- decides whether `run cogen rspec ≡ cogen` may be written without a `snd`.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileRevProjAlgPP where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

module OutGarbage
  (U      : Set)
  (run    : U → U → U)
  (⟨_,_⟩  : U → U → U)
  (snd    : U → U)
  (snd-β  : ∀ a b → snd ⟨ a , b ⟩ ≡ b)
  (srcSem : U → U → U)
  (rint   : U)                          -- program-preserving interpreter
  (rspec  : U)                          -- garbage-EMITTING specialiser
  (γ      : U → U → U)                  -- the garbage it emits for ⟨p,s⟩
  (mix    : U → U → U)                  -- the residual it emits
  (def-rint : ∀ p d → run rint ⟨ p , d ⟩ ≡ ⟨ p , srcSem p d ⟩)
  (out      : ∀ p s → run rspec ⟨ p , s ⟩ ≡ ⟨ γ p s , mix p s ⟩)
  (mix-eq   : ∀ p s d → run (mix p s) d ≡ run p ⟨ s , d ⟩)
  where

  ----------------------------------------------------------------------
  -- The artefacts.  Each is what you get AFTER the projection — the raw
  -- output of rspec is a pair, and a pair is not a program.
  tgt : U → U
  tgt src = mix rint src

  comp : U
  comp = mix rspec rint

  cogen : U
  cogen = mix rspec rspec

  -- they really are the cleaned outputs
  tgt-clean : ∀ src → snd (run rspec ⟨ rint , src ⟩) ≡ tgt src
  tgt-clean src = trans (cong snd (out rint src)) (snd-β (γ rint src) (mix rint src))

  cogen-def : snd (run rspec ⟨ rspec , rspec ⟩) ≡ cogen
  cogen-def = trans (cong snd (out rspec rspec)) (snd-β (γ rspec rspec) cogen)

  ----------------------------------------------------------------------
  -- 1.  Level 1 is unchanged: the residual reversibly simulates the source,
  --     and its output carries the source ONCE (code depth 1).
  answer-shape : ∀ src d → run (tgt src) d ≡ ⟨ src , srcSem src d ⟩
  answer-shape src d = trans (mix-eq rint src d) (def-rint src d)

  rev-proj1 : ∀ src d → snd (run (tgt src) d) ≡ srcSem src d
  rev-proj1 src d = trans (cong snd (answer-shape src d)) (snd-β src (srcSem src d))

  ----------------------------------------------------------------------
  -- 2.  Level 2 and 3: the garbage is INHERITED — each application of an
  --     artefact produces a pair, not a program.
  comp-run : ∀ src → run comp src ≡ ⟨ γ rint src , tgt src ⟩
  comp-run src = trans (mix-eq rspec rint src) (out rint src)

  comp-clean : ∀ src → snd (run comp src) ≡ tgt src
  comp-clean src =
    trans (cong snd (comp-run src)) (snd-β (γ rint src) (tgt src))

  cogen-run : ∀ p → run cogen p ≡ ⟨ γ rspec p , mix rspec p ⟩
  cogen-run p = trans (mix-eq rspec rspec p) (out rspec p)

  cogen-clean : ∀ p → snd (run cogen p) ≡ mix rspec p
  cogen-clean p =
    trans (cong snd (cogen-run p)) (snd-β (γ rspec p) (mix rspec p))

  cogen-comp : snd (run cogen rint) ≡ comp
  cogen-comp = cogen-clean rint

  ----------------------------------------------------------------------
  -- 3.  THE FOURTH PROJECTION.  Shape first, then the two verdicts.
  fp4-shape : run cogen rspec ≡ ⟨ γ rspec rspec , cogen ⟩
  fp4-shape = cogen-run rspec

  -- (i) it does NOT degenerate on the nose …
  NonCyclicʳ : Set
  NonCyclicʳ = ∀ a b → ¬ (⟨ a , b ⟩ ≡ b)

  fp4-fails : NonCyclicʳ → ¬ (run cogen rspec ≡ cogen)
  fp4-fails nc eq = nc (γ rspec rspec) cogen (trans (sym fp4-shape) eq)

  -- (ii) … and it degenerates exactly modulo the projection.
  fp4-clean : snd (run cogen rspec) ≡ cogen
  fp4-clean = cogen-clean rspec

  ----------------------------------------------------------------------
  -- 4.  The tower, with the projection inserted at every level.
  Φ : U → U
  Φ X = snd (run X rspec)

  tower : ℕ → U
  tower zero    = cogen
  tower (suc n) = Φ (tower n)

  tower-collapse : ∀ n → tower n ≡ cogen
  tower-collapse zero    = refl
  tower-collapse (suc n) = trans (cong Φ (tower-collapse n)) fp4-clean

  -- one projection per level, and the chain still computes the source
  -- semantics at any height.
  tower-proj : ∀ n src d →
    snd (run (snd (run (snd (run (tower n) rint)) src)) d) ≡ srcSem src d
  tower-proj n src d =
    trans (cong (λ c → snd (run (snd (run c src)) d))
                (trans (cong (λ t → snd (run t rint)) (tower-collapse n)) cogen-comp))
    (trans (cong (λ t → snd (run t d)) (comp-clean src))
           (rev-proj1 src d))

  -- Dropping the projection breaks the tower AT ONCE: level 1 of the raw
  -- tower is the pair, not cogen.  (Level 2 is worse than wrong: `run` on a
  -- pair is not determined by any hypothesis here — a pair is not a program.)
  raw : ℕ → U
  raw zero    = cogen
  raw (suc n) = run (raw n) rspec

  raw-1 : raw 1 ≡ ⟨ γ rspec rspec , cogen ⟩
  raw-1 = fp4-shape

  raw-1-fails : NonCyclicʳ → ¬ (raw 1 ≡ cogen)
  raw-1-fails = fp4-fails

  ----------------------------------------------------------------------
  -- 5.  THE GARBAGE IS FLAT, NOT NESTED.
  --
  -- At every level the discarded half is that level's own ⟨p,s⟩ image under
  -- γ — a term built from the two arguments of THAT application, never from
  -- the garbage of the level below.  `cleanup-once` is that statement: one
  -- `snd` restores the artefact of any level, with no residue.
  cleanup-once : ∀ p → snd (run (tower 0) p) ≡ mix rspec p
  cleanup-once = cogen-clean

  -- and, at every height, the ANSWER is still ⟨src , ⟦src⟧ d⟩: the code
  -- carried out of the tower has depth 1 and does not depend on n.
  answer-height-free : ∀ n src d →
    run (snd (run (snd (run (tower n) rint)) src)) d ≡ ⟨ src , srcSem src d ⟩
  answer-height-free n src d =
    trans (cong (λ t → run t d)
                (trans (cong (λ c → snd (run c src))
                             (trans (cong (λ t → snd (run t rint)) (tower-collapse n))
                                    cogen-comp))
                       (comp-clean src)))
          (answer-shape src d)
