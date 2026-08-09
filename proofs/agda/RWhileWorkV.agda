{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE `-work` METER, AT THE LEVEL OF VALUES.
--
-- RWhileTime fixes the cost model of `./ri -steps`: one unit per EXECUTED
-- COMMAND NODE.  That meter is blind to the SIZE of the values a command
-- touches, and the repository's Jones-optimality claim is measured with the
-- OTHER meter, `./ri -work`.  This module is the base of the work meter, so
-- that the measurement and the proofs can be argued on one and the same
-- cost model.
--
-- THE COST MODEL (src/EvalRwhile.ml, lines 30-75, verbatim in intent):
-- `-work` counts the value NODES EXAMINED BY STRUCTURAL COMPARISON.
-- Comparison is the only primitive of R-WHILE whose cost is not constant --
-- cons/hd/tl build or project one node and a store slot is one pointer --
-- so it is the only place where the size of a value can show up in the
-- running time.  THREE sites are charged:
--
--   (1) `=? E F`                    (OCaml `EEq` -> `eq_work`)
--   (2) the clearing test of `X ^= E` (OCaml `rupdate`: is the new value
--       equal to the current one?)  -- and ONLY when the current value is
--       non-nil, because `rupdate` tests `vy = VNil` FIRST and that test is
--       free.  Setting a fresh (nil) slot therefore costs nothing.
--   (3) a literal pattern            (OCaml `inv_evalPat`'s `PVal` case)
--
-- Site (3) has no counterpart in this layer: the timed core has no pattern
-- replacement `<=` (see RWhileCRep for that layer), so `PVal` cannot occur.
-- Sites (1) and (2) are `expW` (RWhileWork) and `rupdW` (here).
--
-- NOT charged, each being O(1): testing a value against nil, `is_true`,
-- hd/tl/cons, `pair?`, and pattern-variable reads and writes.  In this layer
-- that is visible as: `expW` is literally `0` on every expression form but
-- `eqE`, and there is no other producer of work anywhere.
--
-- SHORT-CIRCUITING is modelled (`eqW-mismatch`): comparison stops at the
-- first mismatch, so an early mismatch costs one unit however large the
-- values are.  Without that the meter would be `nodes` in disguise.
--
-- The boolean answer and the cost come out of ONE traversal (`eqVW`), and
-- the boolean half is proved equal to RWhileTime's existing `eqV`
-- (`eqVW-≡`), so nothing downstream of `eqV` is disturbed.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileWorkV where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-mono-≤; ≤-refl; ≤-trans; m≤m+n)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import RWhileTime using (V; nil; atm; _∙_; eqℕ; eqℕ-refl; eqV; eqV-refl)

------------------------------------------------------------------------
-- 1.  `nodes` : the number of nodes of a value.  This is what a comparison
--     of a value WITH ITSELF costs (eqW-refl below), i.e. the worst case.
--     It is the OCaml `eq_work v v`, not `val_size` (which counts atoms
--     only); nil and an atom are one node each.

nodes : V → ℕ
nodes nil     = 1
nodes (atm _) = 1
nodes (a ∙ b) = suc (nodes a + nodes b)

nodes-pos : ∀ v → 1 ≤ nodes v
nodes-pos nil     = s≤s z≤n
nodes-pos (atm _) = s≤s z≤n
nodes-pos (_ ∙ _) = s≤s z≤n

------------------------------------------------------------------------
-- 2.  `eqW` : the cost of `=? u v`, charging one unit per PAIR OF NODES
--     EXAMINED and stopping at the first mismatch.
--
--     Read it against `eq_work` in src/EvalRwhile.ml:
--
--        let rec eq_work a b =
--          incr eval_work;                       <-- the `suc` / the `1`
--          match a, b with
--          | VNil, VNil -> true
--          | VAtom x, VAtom y -> x = y
--          | VCons (a1,a2), VCons (b1,b2) -> eq_work a1 b1 && eq_work a2 b2
--          | _ -> false                          <-- mismatch: stop here
--
--     The `&&` is the short circuit: the second component is examined only
--     if the first matched.

eqW : V → V → ℕ
eqW nil     nil     = 1
eqW nil     (atm _) = 1
eqW nil     (_ ∙ _) = 1
eqW (atm _) nil     = 1
eqW (atm _) (atm _) = 1
eqW (atm _) (_ ∙ _) = 1
eqW (_ ∙ _) nil     = 1
eqW (_ ∙ _) (atm _) = 1
eqW (a ∙ b) (c ∙ d) = suc (eqW a c + (if eqV a c then eqW b d else 0))

-- every comparison examines at least the two root nodes
eqW-pos : ∀ u v → 1 ≤ eqW u v
eqW-pos nil     nil     = ≤-refl
eqW-pos nil     (atm _) = ≤-refl
eqW-pos nil     (_ ∙ _) = ≤-refl
eqW-pos (atm _) nil     = ≤-refl
eqW-pos (atm _) (atm _) = ≤-refl
eqW-pos (atm _) (_ ∙ _) = ≤-refl
eqW-pos (_ ∙ _) nil     = ≤-refl
eqW-pos (_ ∙ _) (atm _) = ≤-refl
eqW-pos (_ ∙ _) (_ ∙ _) = s≤s z≤n

------------------------------------------------------------------------
-- 3.  The two facts that make the meter say something.

-- (a) Comparing a value with ITSELF walks all of it: the worst case is the
--     full node count.  This is what the reversible increment pays every
--     iteration (the clearing test of `X ^= E` succeeds).
eqW-refl : ∀ v → eqW v v ≡ nodes v
eqW-refl nil     = refl
eqW-refl (atm n) = refl
eqW-refl (a ∙ b) rewrite eqV-refl a | eqW-refl a | eqW-refl b = refl

-- (b) SHORT CIRCUIT.  If the heads already differ, the cost does not depend
--     on the tails at all -- however large they are.  (Contrast (a): with
--     `nodes` the cost would grow with the tails.)
eqW-mismatch : ∀ a c b d → eqV a c ≡ false
             → eqW (a ∙ b) (c ∙ d) ≡ suc (eqW a c)
eqW-mismatch a c b d h rewrite h = cong suc (+-identityʳ (eqW a c))

-- the concrete reading of (b): two arbitrarily large values whose first
-- atoms differ cost 2 units, not their size.
short-circuit : ∀ b d → eqW (atm 0 ∙ b) (atm 1 ∙ d) ≡ 2
short-circuit b d = refl

-- ... whereas the same-sized equal values cost their whole node count.
no-short-circuit : ∀ b → eqW (atm 0 ∙ b) (atm 0 ∙ b) ≡ suc (suc (nodes b))
no-short-circuit b rewrite eqW-refl b = refl

-- (c) The meter is bounded by the size of either argument (a comparison
--     never examines more nodes than the smaller value has).
eqW-≤-nodesˡ : ∀ u v → eqW u v ≤ nodes u
eqW-≤-nodesˡ nil     nil     = ≤-refl
eqW-≤-nodesˡ nil     (atm _) = ≤-refl
eqW-≤-nodesˡ nil     (_ ∙ _) = ≤-refl
eqW-≤-nodesˡ (atm _) nil     = ≤-refl
eqW-≤-nodesˡ (atm _) (atm _) = ≤-refl
eqW-≤-nodesˡ (atm _) (_ ∙ _) = ≤-refl
eqW-≤-nodesˡ (_ ∙ _) nil     = s≤s z≤n
eqW-≤-nodesˡ (_ ∙ _) (atm _) = s≤s z≤n
eqW-≤-nodesˡ (a ∙ b) (c ∙ d) =
  s≤s (+-mono-≤ (eqW-≤-nodesˡ a c) tail-≤)
  where
    tail-≤ : (if eqV a c then eqW b d else 0) ≤ nodes b
    tail-≤ with eqV a c
    ... | true  = eqW-≤-nodesˡ b d
    ... | false = z≤n

------------------------------------------------------------------------
-- 4.  ONE TRAVERSAL, TWO ANSWERS.  The implementation computes the boolean
--     and the cost together (`eq_work` returns the bool and increments the
--     counter).  `eqVW` does the same, and `eqVW-≡` proves that its two
--     projections are exactly RWhileTime's `eqV` and the `eqW` above -- so
--     the work meter is a decoration of the EXISTING equality test, not a
--     second, possibly divergent, notion of it.

combW : Bool × ℕ → Bool × ℕ → Bool × ℕ
combW (true  , m) (r , n) = r     , suc (m + n)
combW (false , m) _       = false , suc m

eqVW : V → V → Bool × ℕ
eqVW nil     nil     = true      , 1
eqVW nil     (atm _) = false     , 1
eqVW nil     (_ ∙ _) = false     , 1
eqVW (atm _) nil     = false     , 1
eqVW (atm m) (atm n) = eqℕ m n   , 1
eqVW (atm _) (_ ∙ _) = false     , 1
eqVW (_ ∙ _) nil     = false     , 1
eqVW (_ ∙ _) (atm _) = false     , 1
eqVW (a ∙ b) (c ∙ d) = combW (eqVW a c) (eqVW b d)

private
  combW-lem : ∀ p m q n
            → combW (p , m) (q , n)
              ≡ ((if p then q else false) , suc (m + (if p then n else 0)))
  combW-lem true  m q n = refl
  combW-lem false m q n = cong (λ z → false , suc z) (sym (+-identityʳ m))

eqVW-≡ : ∀ u v → eqVW u v ≡ (eqV u v , eqW u v)
eqVW-≡ nil     nil     = refl
eqVW-≡ nil     (atm _) = refl
eqVW-≡ nil     (_ ∙ _) = refl
eqVW-≡ (atm _) nil     = refl
eqVW-≡ (atm _) (atm _) = refl
eqVW-≡ (atm _) (_ ∙ _) = refl
eqVW-≡ (_ ∙ _) nil     = refl
eqVW-≡ (_ ∙ _) (atm _) = refl
eqVW-≡ (a ∙ b) (c ∙ d) rewrite eqVW-≡ a c | eqVW-≡ b d =
  combW-lem (eqV a c) (eqW a c) (eqV b d) (eqW b d)

-- the two halves, stated separately (this is the "eqW agrees with eqV" the
-- rest of the development relies on)
eqVW-bool : ∀ u v → proj₁ (eqVW u v) ≡ eqV u v
eqVW-bool u v = cong proj₁ (eqVW-≡ u v)

eqVW-cost : ∀ u v → proj₂ (eqVW u v) ≡ eqW u v
eqVW-cost u v = cong proj₂ (eqVW-≡ u v)

------------------------------------------------------------------------
-- 5.  THE CLEARING TEST of `X ^= E`.  Site (2) of the cost model.
--
--     src/EvalRwhile.ml `rupdate`:
--
--        Some (if vy = VNil then vx                  <-- FREE (nil test)
--              else if eq_work vx vy then VNil       <-- CHARGED
--              else if vx = VNil then vy             <-- (already charged)
--              else error)
--
--     so: assigning into a nil slot is free, and every other update pays a
--     comparison of the new value against the current one.  RWhileTime's
--     `rupd` splits on the CURRENT value first in exactly the same way
--     (`rupd nil v = just v`), so `rupdW` splits on the same argument.
--
--     NB the argument order: `rupd`/`rupdW` take the CURRENT value first.

rupdW : V → V → ℕ
rupdW nil     _ = 0
rupdW (atm m) v = eqW (atm m) v
rupdW (a ∙ b) v = eqW (a ∙ b) v

-- setting a fresh slot is free -- this is why the emit of p⁺ can build a
-- pair without paying for it (RWhileProgPresWork).
rupdW-fresh : ∀ v → rupdW nil v ≡ 0
rupdW-fresh _ = refl

-- clearing a slot costs the full node count of what was in it: this is the
-- per-iteration price of the reversible increment.
rupdW-self : ∀ v → ¬ (v ≡ nil) → rupdW v v ≡ nodes v
rupdW-self nil     h = ⊥-elim (h refl)
rupdW-self (atm n) _ = eqW-refl (atm n)
rupdW-self (a ∙ b) _ = eqW-refl (a ∙ b)

-- the pair case, the one p⁺ pays at `write` (used in RWhileProgWork)
rupdW-self-pair : ∀ u v → rupdW (u ∙ v) (u ∙ v) ≡ suc (nodes u + nodes v)
rupdW-self-pair u v = eqW-refl (u ∙ v)

-- an update never costs more than the value in the slot
rupdW-≤ : ∀ w v → rupdW w v ≤ nodes w
rupdW-≤ nil     v = z≤n
rupdW-≤ (atm m) v = eqW-≤-nodesˡ (atm m) v
rupdW-≤ (a ∙ b) v = eqW-≤-nodesˡ (a ∙ b) v
