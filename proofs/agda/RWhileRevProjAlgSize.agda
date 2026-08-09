{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE COST SIDE OF THE COLLAPSE: climbing past level 3 buys nothing and is
-- not free.
--
-- RWhileFutamuraAlg/RWhileRevProjAlg prove the tower is CONSTANT from level 3
-- on (`tower n ≡ cogen`).  Everything measurable is a function of the
-- artefact, so the collapse transports to every meter at once — that is the
-- only honest general statement, and it is the one below:
--
--   `TowerMeter.meter-constant`  ∀ n → meter (tower n) ≡ meter cogen
--        for ANY ℕ-valued meter: `-steps`, `-work`, node count, garbage size.
--        Nothing about the meter is used; only that it is a function.
--
--   `Climb.climb-linear`  the cost of BUILDING the height-n tower is exactly
--        n × (the cost of one level), because every level costs the same one.
--   `Climb.climb-positive`  and if one level costs anything at all, the
--        height-n tower costs strictly more than cogen for a strictly equal
--        artefact.  "No fourth projection" is thus not just "nothing new" but
--        "nothing new, at a price linear in how long you keep asking".
--
--   `Growth.emb-strictly-bigger`  the dead-branch embedding of
--        RWhileRevProjAlg is semantically free (`dead`) but NOT free in size:
--        |emb g r| = 1 + |g| + |r| > |r|.  That is the measured 103 → 1739
--        nodes of FINDINGS §6 (and 1739 → 755 after N-sizing), stated as a
--        law.  What the collapse adds is that this one layer is all there is:
--        `size-tower` — every level of the tower has the SAME size.
--
-- HONEST SCOPE.  This is the abstract layer.  The concrete `-work` meter of
-- RWhileWork / RWhileProgPresWork lives in the timed R-WHILE core, over
-- commands and stores, and nothing here is connected to it: bridging the
-- abstract U-layer to the timed core is the open item ④ already records.
-- What is claimed is only what is proved: any meter is constant along the
-- tower, and the climb is linear.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileRevProjAlgSize where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤n+m; +-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

import RWhileRevProjAlgInst

------------------------------------------------------------------------
-- 1.  ANY meter is constant along the tower.
------------------------------------------------------------------------

module TowerMeter
  (U     : Set)
  (meter : U → ℕ)
  (tower : ℕ → U)
  (cogen : U)
  (collapse : ∀ n → tower n ≡ cogen)
  where

  meter-constant : ∀ n → meter (tower n) ≡ meter cogen
  meter-constant n = cong meter (collapse n)

------------------------------------------------------------------------
-- 2.  Climbing is linear, and strictly positive if a level costs anything.
------------------------------------------------------------------------

module Climb
  (U     : Set)
  (level : U → ℕ)                 -- what one climb costs, on any meter
  (tower : ℕ → U)
  (cogen : U)
  (collapse : ∀ n → tower n ≡ cogen)
  where

  level-cost : ∀ n → level (tower n) ≡ level cogen
  level-cost n = cong level (collapse n)

  climb : ℕ → ℕ
  climb zero    = 0
  climb (suc n) = level (tower n) + climb n

  climb-linear : ∀ n → climb n ≡ n * level cogen
  climb-linear zero    = refl
  climb-linear (suc n) rewrite level-cost n | climb-linear n = refl

  -- one level costs w > 0  ⇒  height n+1 costs > 0, for the SAME artefact.
  climb-positive : ∀ {w} n → level cogen ≡ suc w → 0 < climb (suc n)
  climb-positive {w} n eq
    rewrite climb-linear (suc n) | eq = s≤s z≤n

  -- … while the artefact obtained is literally cogen, at every height.
  nothing-gained : ∀ n → tower n ≡ cogen
  nothing-gained = collapse

------------------------------------------------------------------------
-- 3.  The dead-branch embedding: free for `run`, not free for `size`.
------------------------------------------------------------------------

module Growth
  (U    : Set)
  (emb  : U → U → U)
  (size : U → ℕ)
  (size-emb : ∀ g r → size (emb g r) ≡ suc (size g + size r))
  where

  emb-strictly-bigger : ∀ g r → size r < size (emb g r)
  emb-strictly-bigger g r
    rewrite size-emb g r = s≤s (m≤n+m (size r) (size g))

------------------------------------------------------------------------
-- 4.  Instantiated on the two concrete models of RWhileRevProjAlgInst.
------------------------------------------------------------------------

module DeadCodeSize where

  open RWhileRevProjAlgInst.DeadCode

  size : U → ℕ
  size (pr a b)  = suc (size a + size b)
  size (cls a b) = suc (size a + size b)
  size (gb g r)  = suc (size g + size r)
  size rspec     = 1
  size rint      = 1
  size swp       = 1
  size atom      = 1

  open Growth U gb size (λ g r → refl) public
  open TowerMeter U size tower cogen tower-collapse public
  open Climb U size tower cogen tower-collapse
    using (climb; climb-linear; climb-positive) public

  -- the artefact carries its garbage: 7 nodes against the 3 of the clean
  -- residual it behaves like (the toy's version of 1739 against 103).
  _ : size cogen ≡ 7
  _ = refl

  _ : size (cls rspec rspec) ≡ 3
  _ = refl

  _ : size (cls rspec rspec) < size cogen
  _ = emb-strictly-bigger (pr rspec rspec) (cls rspec rspec)

  -- but it does not grow with the height: every level is 7 nodes …
  _ : ∀ n → size (tower n) ≡ 7
  _ = meter-constant

  -- … and climbing to height n costs exactly 7n on this meter, for nothing.
  _ : ∀ n → climb n ≡ n * 7
  _ = climb-linear

  _ : ∀ n → 0 < climb (suc n)
  _ = λ n → climb-positive n refl

module OutPairSize where

  open RWhileRevProjAlgInst.OutPair

  open TowerMeter U size tower cogen tower-collapse public
  open Climb U size tower cogen tower-collapse
    using (climb; climb-linear; climb-positive) public

  -- here the artefact is the CLEAN residual (the garbage went to the output),
  -- so it is small — but each level has to pay a projection, and the pair it
  -- throws away is bigger than the artefact itself.
  _ : size cogen ≡ 3
  _ = refl

  _ : size (run cogen rspec) ≡ 7
  _ = refl

  _ : ∀ n → size (tower n) ≡ 3
  _ = meter-constant

  _ : ∀ n → climb n ≡ n * 3
  _ = climb-linear
