{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The reversible projections of "2025_Reversible_Projection_IEICE_D"
-- (Okubo–Yokoyama), formalised in Agda — a fourth independent cross-check
-- alongside the paper's Isabelle/HOL, Rocq and Lean developments.
--
-- Following the paper: programs and data live in one universal type U with a
-- semantic function `run` (⟦·⟧ applied to an input).  The reversible
-- INTERPRETER `rint` keeps the program in its output (that is what makes it
-- injective/reversible):
--      run rint ⟨p,d⟩ ≃ ⟨ p , ⟦p⟧_S d ⟩                       (def-rint)
-- The SPECIALISER `rspec` is itself a program satisfying the mix equation
--      run (run rspec ⟨p,s⟩) d ≃ run p ⟨s,d⟩                   (def-spec)
-- (`rspec` being a program is exactly the self-application condition; the
-- second/third projections apply rspec to rspec.)
--
-- (≃, the paper's Kleene equality on the partial ⟦·⟧, is modelled here by
-- propositional equality on a total `run` — the defined fragment.  Partiality
-- via option is an orthogonal refinement, carried out in the paper's
-- Isabelle/Rocq/Lean scripts.)
--
-- The three reversible projections and their correctness (paper Thms.
-- rev_proj1/2/3) — each a short chain of `def-spec`/`def-rint` substitutions:
--   tgt''  = run rspec ⟨ rint  , src ⟩      snd∘⟦tgt''⟧            ≃ ⟦src⟧_S
--   comp'' = run rspec ⟨ rspec , rint ⟩     snd∘⟦⟦comp''⟧ src⟧     ≃ ⟦src⟧_S
--   cogen' = run rspec ⟨ rspec , rspec ⟩    snd∘⟦⟦⟦cogen'⟧ rint⟧ src⟧ ≃ ⟦src⟧_S
------------------------------------------------------------------------

module RWhileRevProjPaper where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

module RevProjection
  (U      : Set)                       -- one universal type: programs = data
  (run    : U → U → U)                 -- ⟦prog⟧ applied to an input
  (⟨_,_⟩  : U → U → U)                 -- pairing (program . data) / (static . dynamic)
  (snd    : U → U)                     -- the second projection  (paper's `snd`)
  (snd-β  : ∀ a b → snd ⟨ a , b ⟩ ≡ b)
  (srcSem : U → U → U)                 -- ⟦·⟧_S : source-language semantics
  (rint   : U)                         -- the reversible interpreter (a program)
  (rspec  : U)                         -- the specialiser (a program)
  (def-rint : ∀ p d → run rint ⟨ p , d ⟩ ≡ ⟨ p , srcSem p d ⟩)    -- keeps the program
  (def-spec : ∀ p s d → run (run rspec ⟨ p , s ⟩) d ≡ run p ⟨ s , d ⟩)
  where

  ----------------------------------------------------------------------
  -- The three generated artefacts.
  tgt : U → U                          -- 第1可逆射影：特殊化された可逆シミュレーション
  tgt src = run rspec ⟨ rint , src ⟩

  comp : U                             -- 第2可逆射影：コンパイラ
  comp = run rspec ⟨ rspec , rint ⟩

  cogen : U                            -- 第3可逆射影：コンパイラジェネレータ
  cogen = run rspec ⟨ rspec , rspec ⟩

  -- the reversible interpreter, after `snd`, recovers the source semantics
  rint-correct : ∀ p d → snd (run rint ⟨ p , d ⟩) ≡ srcSem p d
  rint-correct p d = trans (cong snd (def-rint p d)) (snd-β p (srcSem p d))

  ----------------------------------------------------------------------
  -- 第1可逆射影の正当性 (Thm rev_proj1):  snd ∘ ⟦tgt''⟧ ≃ ⟦src⟧_S
  rev-proj1 : ∀ src d → snd (run (tgt src) d) ≡ srcSem src d
  rev-proj1 src d = trans (cong snd (def-spec rint src d)) (rint-correct src d)

  ----------------------------------------------------------------------
  -- 第2可逆射影の正当性 (Thm rev_proj2):  comp'' is a compiler, and
  --   snd ∘ ⟦ ⟦comp''⟧ src ⟧ ≃ ⟦src⟧_S
  comp-tgt : ∀ src → run comp src ≡ tgt src        -- ⟦comp''⟧(src) = tgt''
  comp-tgt src = def-spec rspec rint src

  rev-proj2 : ∀ src d → snd (run (run comp src) d) ≡ srcSem src d
  rev-proj2 src d =
    trans (cong (λ x → snd (run x d)) (comp-tgt src)) (rev-proj1 src d)

  ----------------------------------------------------------------------
  -- 第3可逆射影の正当性 (Thm rev_proj3):  cogen' is a compiler generator,
  --   ⟦cogen'⟧(rint) = comp'', and  snd ∘ ⟦ ⟦ ⟦cogen'⟧ rint ⟧ src ⟧ ≃ ⟦src⟧_S
  cogen-comp : run cogen rint ≡ comp               -- ⟦cogen'⟧(rint) = comp''
  cogen-comp = def-spec rspec rspec rint

  rev-proj3 : ∀ src d → snd (run (run (run cogen rint) src) d) ≡ srcSem src d
  rev-proj3 src d =
    trans (cong (λ x → snd (run (run x src) d)) cogen-comp) (rev-proj2 src d)
