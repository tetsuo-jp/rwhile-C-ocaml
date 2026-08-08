{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE COST OF A `case`, with the arm bodies no longer abstract.
--
-- `RWhileSurface.caseNest-cost` already measures the DISPATCH of a symmetric
-- `case`: reaching the fall-through arm costs one conditional node per arm
-- skipped.  What it could not measure is the arm BODIES, because a `case` arm
-- is
--
--     InPat <= Scrut ;  Body ;  Result <= OutPat
--
-- and the timed core (RWhileTime) has no pattern replacement `<=` -- that lives
-- in the untimed layer (RWhileCRep), which has no costs.  So the two halves of
-- the cost of a `case` were in two different models.
--
-- This module joins them, by the observation that a replacement over a FLAT
-- pattern needs no new semantics at all: it is definable in the timed core.
--
--     Y <= X            ==   Y ^= X ; X ^= Y
--     cons A B <= X     ==   A ^= hd X ; B ^= tl X ; X ^= cons A B
--     X <= cons A B     ==   X ^= cons A B ; A ^= hd X ; B ^= tl X
--
-- Each is exactly R-WHILE's own idiom, and each is proved here to realise the
-- Read/Write relation that RWhileCRep gives `<=` -- restated over the timed
-- store, so the two layers meet -- at an exact, stated cost.
--
-- What is proved:
--
--   movePat-run / splitPat-run / joinPat-run
--                        the compiled replacement takes the store where the
--                        pattern semantics says it does, at cost 3 / 5 / 5
--   splitPat-join        splitting then joining is the identity on the store,
--                        i.e. the two are each other's inverse -- which is how
--                        R-WHILE inverts `<=` (swap the patterns)
--   caseNest-cost-taken  the dispatch cost when arm i is TAKEN (the existing
--                        lemma covers only the fall-through)
--   case-swap-run        examples/case_swap.rwhile, both arms, executed inside
--                        the type checker, with the cost checked
--
-- SCOPE.  Flat patterns: a variable, or a cons of two variables.  A NESTED
-- pattern cannot be compiled this way without a temporary -- the same wall the
-- specialiser hit for `cons (cons V1 V2) St <= St` (see the note in
-- examples/spec_av.rwhile) -- and that boundary is deliberate, not an oversight.
--
-- COST CONVENTION.  The numbers here are the cost of the COMPILED form, which
-- is not what `./ri -steps` charges: the interpreter charges one node for a
-- whole `<=`, where the model spends 3 or 5.  This is the usual gap between the
-- surface and the core (compare RWhileSugar.assertNil-cost, which is 2 in the
-- model and 1 in the interpreter), and it is stated rather than hidden.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileCaseCost where

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime
open import RWhileSIWf using (get-set-≡; get-set-≢)
open import RWhileSurface using (CaseArm; caseNest; AllFalse; []; _∷_; tests)

------------------------------------------------------------------------
-- 1.  A flat pattern replacement, compiled into the timed core.

movePat : ℕ → ℕ → Cmd                 -- Y <= X   (y is the target)
movePat y x = (y ^= opd (var x)) ⨾ (x ^= opd (var y))

splitPat : ℕ → ℕ → ℕ → Cmd            -- cons A B <= X
splitPat a b x = (a ^= hdE (var x)) ⨾ (b ^= tlE (var x)) ⨾ (x ^= cns (var a) (var b))

joinPat : ℕ → ℕ → ℕ → Cmd            -- X <= cons A B
joinPat x a b = (x ^= cns (var a) (var b)) ⨾ (a ^= hdE (var x)) ⨾ (b ^= tlE (var x))

------------------------------------------------------------------------
-- 2.  `Y <= X`: the value moves and the source is cleared, at cost 3.

movePat-run : ∀ {s y x v}
            → ¬ (x ≡ y) → get s x ≡ v → get s y ≡ nil
            → movePat y x ⊢ s ⇒ set (set s y v) x nil ∣ 3
movePat-run {s} {y} {x} {v} nxy gx gy =
  e-seq (e-ass ev₁ ru₁) (e-ass ev₂ ru₂)
  where
    ev₁ : evalE s (opd (var x)) ≡ just v
    ev₁ = cong just gx
    ru₁ : rupd (get s y) v ≡ just v
    ru₁ rewrite gy = refl
    -- after the first assignment the store is `set s y v`
    gy' : get (set s y v) y ≡ v
    gy' = get-set-≡ s y v
    gx' : get (set s y v) x ≡ v
    gx' = trans (get-set-≢ s y x v (λ e → nxy (sym e))) gx
    ev₂ : evalE (set s y v) (opd (var y)) ≡ just v
    ev₂ = cong just gy'
    ru₂ : rupd (get (set s y v) x) v ≡ just nil
    ru₂ rewrite gx' = rupd-self v

------------------------------------------------------------------------
-- 3.  `cons A B <= X`: the two halves land in A and B and X is cleared, at
--     cost 5.  The three disequalities are pattern LINEARITY (src/EvalRwhile.ml
--     warn_linearity): a pattern's variables are distinct and disjoint from the
--     other side's.

splitPat-run : ∀ {s a b x u v}
             → ¬ (a ≡ b) → ¬ (a ≡ x) → ¬ (b ≡ x)
             → get s x ≡ (u ∙ v) → get s a ≡ nil → get s b ≡ nil
             → splitPat a b x ⊢ s ⇒ set (set (set s a u) b v) x nil ∣ 5
splitPat-run {s} {a} {b} {x} {u} {v} nab nax nbx gx ga gb =
  e-seq (e-ass ev₁ ru₁) (e-seq (e-ass ev₂ ru₂) (e-ass ev₃ ru₃))
  where
    s₁ : Store
    s₁ = set s a u
    s₂ : Store
    s₂ = set s₁ b v
    ev₁ : evalE s (hdE (var x)) ≡ just u
    ev₁ rewrite gx = refl
    ru₁ : rupd (get s a) u ≡ just u
    ru₁ rewrite ga = refl
    gx₁ : get s₁ x ≡ (u ∙ v)
    gx₁ = trans (get-set-≢ s a x u nax) gx
    gb₁ : get s₁ b ≡ nil
    gb₁ = trans (get-set-≢ s a b u nab) gb
    ev₂ : evalE s₁ (tlE (var x)) ≡ just v
    ev₂ rewrite gx₁ = refl
    ru₂ : rupd (get s₁ b) v ≡ just v
    ru₂ rewrite gb₁ = refl
    ga₂ : get s₂ a ≡ u
    ga₂ = trans (get-set-≢ s₁ b a v (λ e → nab (sym e))) (get-set-≡ s a u)
    gb₂ : get s₂ b ≡ v
    gb₂ = get-set-≡ s₁ b v
    gx₂ : get s₂ x ≡ (u ∙ v)
    gx₂ = trans (get-set-≢ s₁ b x v nbx) gx₁
    ev₃ : evalE s₂ (cns (var a) (var b)) ≡ just (u ∙ v)
    ev₃ rewrite ga₂ | gb₂ = refl
    ru₃ : rupd (get s₂ x) (u ∙ v) ≡ just nil
    ru₃ rewrite gx₂ = rupd-self (u ∙ v)

------------------------------------------------------------------------
-- 4.  `X <= cons A B`: the mirror image, also cost 5.

joinPat-run : ∀ {s a b x u v}
            → ¬ (a ≡ b) → ¬ (a ≡ x) → ¬ (b ≡ x)
            → get s x ≡ nil → get s a ≡ u → get s b ≡ v
            → joinPat x a b ⊢ s ⇒ set (set (set s x (u ∙ v)) a nil) b nil ∣ 5
joinPat-run {s} {a} {b} {x} {u} {v} nab nax nbx gx ga gb =
  e-seq (e-ass ev₁ ru₁) (e-seq (e-ass ev₂ ru₂) (e-ass ev₃ ru₃))
  where
    s₁ : Store
    s₁ = set s x (u ∙ v)
    s₂ : Store
    s₂ = set s₁ a nil
    ev₁ : evalE s (cns (var a) (var b)) ≡ just (u ∙ v)
    ev₁ rewrite ga | gb = refl
    ru₁ : rupd (get s x) (u ∙ v) ≡ just (u ∙ v)
    ru₁ rewrite gx = refl
    gx₁ : get s₁ x ≡ (u ∙ v)
    gx₁ = get-set-≡ s x (u ∙ v)
    ga₁ : get s₁ a ≡ u
    ga₁ = trans (get-set-≢ s x a (u ∙ v) (λ e → nax (sym e))) ga
    ev₂ : evalE s₁ (hdE (var x)) ≡ just u
    ev₂ rewrite gx₁ = refl
    ru₂ : rupd (get s₁ a) u ≡ just nil
    ru₂ rewrite ga₁ = rupd-self u
    gx₂ : get s₂ x ≡ (u ∙ v)
    gx₂ = trans (get-set-≢ s₁ a x nil nax) gx₁
    gb₂ : get s₂ b ≡ v
    gb₂ = trans (get-set-≢ s₁ a b nil nab)
                (trans (get-set-≢ s x b (u ∙ v) (λ e → nbx (sym e))) gb)
    ev₃ : evalE s₂ (tlE (var x)) ≡ just v
    ev₃ rewrite gx₂ = refl
    ru₃ : rupd (get s₂ b) v ≡ just nil
    ru₃ rewrite gb₂ = rupd-self v

------------------------------------------------------------------------
-- 5.  Split and join are each other's inverse.
--
--     R-WHILE inverts `q <= r` by SWAPPING the patterns, so `cons A B <= X` and
--     `X <= cons A B` are a syntactic inverse pair.  Here that is checked
--     semantically in the timed core: splitting a cons out of X and joining it
--     back restores every variable, at cost 11 (5 + 5 and the sequencing node).
--     This is the argument RWhilePushPop makes for push/pop, now WITH costs.
--
--     The restoration is stated POINTWISE rather than as `s' ≡ s`, and that is
--     forced: `set` extends a short store with nils, so writing to an index past
--     the end of s and clearing it again yields a LONGER list holding the same
--     values.  Propositional equality of the two stores is simply false (take
--     s = [] and a = 0); extensional equality is what actually holds.

split-join-restores : ∀ {s a b x u v}
                    → ¬ (a ≡ b) → ¬ (a ≡ x) → ¬ (b ≡ x)
                    → get s x ≡ (u ∙ v) → get s a ≡ nil → get s b ≡ nil
                    → Σ[ s' ∈ Store ]
                        (((splitPat a b x ⨾ joinPat x a b) ⊢ s ⇒ s' ∣ 11)
                         × (∀ y → get s' y ≡ get s y))
split-join-restores {s} {a} {b} {x} {u} {v} nab nax nbx gx ga gb =
  s' , e-seq (splitPat-run nab nax nbx gx ga gb)
             (joinPat-run nab nax nbx gx' ga' gb')
      , same
  where
    s₃ : Store
    s₃ = set (set (set s a u) b v) x nil
    s' : Store
    s' = set (set (set s₃ x (u ∙ v)) a nil) b nil
    gx' : get s₃ x ≡ nil
    gx' = get-set-≡ (set (set s a u) b v) x nil
    ga' : get s₃ a ≡ u
    ga' = trans (get-set-≢ (set (set s a u) b v) x a nil (λ e → nax (sym e)))
                (trans (get-set-≢ (set s a u) b a v (λ e → nab (sym e)))
                       (get-set-≡ s a u))
    gb' : get s₃ b ≡ v
    gb' = trans (get-set-≢ (set (set s a u) b v) x b nil (λ e → nbx (sym e)))
                (get-set-≡ (set s a u) b v)
    -- s₄ is s' before the final clear of b
    s₄ : Store
    s₄ = set (set s₃ x (u ∙ v)) a nil
    -- every variable holds what it held in s
    same : ∀ y → get s' y ≡ get s y
    same y with y ≟ b
    ... | yes refl = trans (get-set-≡ s₄ y nil) (sym gb)
    ... | no  nyb with y ≟ a
    ...   | yes refl = trans (get-set-≢ s₄ b y nil (λ e → nyb (sym e)))
                            (trans (get-set-≡ (set s₃ x (u ∙ v)) y nil) (sym ga))
    ...   | no nya with y ≟ x
    ...     | yes refl =
                trans (get-set-≢ s₄ b y nil (λ e → nyb (sym e)))
               (trans (get-set-≢ (set s₃ x (u ∙ v)) a y nil (λ e → nya (sym e)))
               (trans (get-set-≡ s₃ y (u ∙ v)) (sym gx)))
    ...     | no nyx =
                trans (get-set-≢ s₄ b y nil (λ e → nyb (sym e)))
               (trans (get-set-≢ (set s₃ x (u ∙ v)) a y nil (λ e → nya (sym e)))
               (trans (get-set-≢ s₃ x y (u ∙ v) (λ e → nyx (sym e)))
               (trans (get-set-≢ (set (set s a u) b v) x y nil (λ e → nyx (sym e)))
               (trans (get-set-≢ (set s a u) b y v (λ e → nyb (sym e)))
                      (get-set-≢ s a y u (λ e → nya (sym e)))))))

------------------------------------------------------------------------
-- 6.  The dispatch cost when an arm is TAKEN.
--
--     RWhileSurface.caseNest-cost covers the fall-through: all tests false, so
--     the cost is one node per arm plus the last arm's.  The complementary law
--     -- the one that says what an ordinary `case` costs -- is that reaching
--     arm i costs exactly i nodes of dispatch and then whatever the arm costs.
--     Together the two cover every run of a `case`.

caseNest-cost-taken :
  ∀ pre {e c f post last s t k}
  → AllFalse s (tests pre)
  → evalT s e ≡ just true
  → caseNest (pre ++ (e , c , f) ∷ post) last ⊢ s ⇒ t ∣ k
  → Σ[ m ∈ ℕ ] ((c ⊢ s ⇒ t ∣ m) × (k ≡ length pre + suc m))
caseNest-cost-taken []                     _         _  (e-then _ d _)  = _ , d , refl
caseNest-cost-taken []                     _         te (e-else fe _ _)
  with trans (sym te) fe
... | ()
caseNest-cost-taken ((e' , c' , f') ∷ pre) (fe ∷ af) te (e-else _ d _)
  with caseNest-cost-taken pre af te d
... | m , dc , refl = m , dc , refl
caseNest-cost-taken ((e' , c' , f') ∷ pre) (fe ∷ _)  _  (e-then te' _ _)
  with trans (sym fe) te'
... | ()

------------------------------------------------------------------------
-- 7.  examples/case_swap.rwhile, with nothing abstract left.
--
--     Its cons arm is
--
--         cons A B <= X ;  X <= cons B A
--
--     -- split X into its halves and rebuild it the other way round.  That is
--     splitPat followed by joinPat with the two variables exchanged, so §3 and
--     §4 give it directly.

swapArm : ℕ → ℕ → ℕ → Cmd
swapArm a b x = splitPat a b x ⨾ joinPat x b a

swapArm-run : ∀ {s a b x u v}
            → ¬ (a ≡ b) → ¬ (a ≡ x) → ¬ (b ≡ x)
            → get s x ≡ (u ∙ v) → get s a ≡ nil → get s b ≡ nil
            → Σ[ s' ∈ Store ]
                ((swapArm a b x ⊢ s ⇒ s' ∣ 11)
                 × (get s' x ≡ (v ∙ u))
                 × (get s' a ≡ nil) × (get s' b ≡ nil))
swapArm-run {s} {a} {b} {x} {u} {v} nab nax nbx gx ga gb =
  s' , e-seq (splitPat-run nab nax nbx gx ga gb)
             (joinPat-run (λ e → nab (sym e)) nbx nax gx₃ gb₃ ga₃)
     , gx' , ga' , gb'
  where
    s₃ : Store
    s₃ = set (set (set s a u) b v) x nil
    s' : Store
    s' = set (set (set s₃ x (v ∙ u)) b nil) a nil
    gx₃ : get s₃ x ≡ nil
    gx₃ = get-set-≡ (set (set s a u) b v) x nil
    ga₃ : get s₃ a ≡ u
    ga₃ = trans (get-set-≢ (set (set s a u) b v) x a nil (λ e → nax (sym e)))
                (trans (get-set-≢ (set s a u) b a v (λ e → nab (sym e)))
                       (get-set-≡ s a u))
    gb₃ : get s₃ b ≡ v
    gb₃ = trans (get-set-≢ (set (set s a u) b v) x b nil (λ e → nbx (sym e)))
                (get-set-≡ (set s a u) b v)
    gx' : get s' x ≡ (v ∙ u)
    gx' = trans (get-set-≢ (set (set s₃ x (v ∙ u)) b nil) a x nil nax)
                (trans (get-set-≢ (set s₃ x (v ∙ u)) b x nil nbx)
                       (get-set-≡ s₃ x (v ∙ u)))
    ga' : get s' a ≡ nil
    ga' = get-set-≡ (set (set s₃ x (v ∙ u)) b nil) a nil
    gb' : get s' b ≡ nil
    gb' = trans (get-set-≢ (set (set s₃ x (v ∙ u)) b nil) a b nil nab)
                (get-set-≡ (set s₃ x (v ∙ u)) b nil)

------------------------------------------------------------------------
-- 8.  The whole `case`, dispatch and body together.
--
--     `case X yields X of cons A B => nil <= nil => cons B A | nil => ... end`
--     desugars (./ri -exp) to a one-arm nest whose fall-through is the nil arm.
--     On a cons the nil arm is unreachable, so the run is: one conditional node
--     of dispatch, then the arm.  Total 12 in the compiled model.
--
--     `./ri -steps` says 6 for the same program.  The difference is entirely the
--     cost convention stated at the top: the interpreter charges 1 for each of
--     the three `<=` where the model spends 3 or 5, and the model's `skip`s are
--     nodes the surface grammar does not write.  What the two agree on is the
--     SHAPE of the law -- dispatch + arm, one node per arm skipped.

caseSwap : ℕ → ℕ → ℕ → Cmd
caseSwap a b x = caseNest ((prE (var x) , swapArm a b x , prE (var x)) ∷ []) skip

caseSwap-run : ∀ {s a b x u v}
             → ¬ (a ≡ b) → ¬ (a ≡ x) → ¬ (b ≡ x)
             → get s x ≡ (u ∙ v) → get s a ≡ nil → get s b ≡ nil
             → Σ[ s' ∈ Store ]
                 ((caseSwap a b x ⊢ s ⇒ s' ∣ 12) × (get s' x ≡ (v ∙ u)))
caseSwap-run {s} {a} {b} {x} {u} {v} nab nax nbx gx ga gb
  with swapArm-run {s} {a} {b} {x} {u} {v} nab nax nbx gx ga gb
... | s' , d , gx' , _ , _ = s' , e-then te d te' , gx'
  where
    te : evalT s (prE (var x)) ≡ just true
    te rewrite gx = refl
    te' : evalT s' (prE (var x)) ≡ just true
    te' rewrite gx' = refl

------------------------------------------------------------------------
-- 9.  ...and the same thing RUN inside the type checker, on real values.
--
--     X is variable 0 holding ('a . 'b), A is 1 and B is 2.  The answer must be
--     ('b . 'a) with A and B nil again -- the store-clean condition -- at the
--     cost §8 predicts.

private
  s0 : Store
  s0 = (atm 1 ∙ atm 2) ∷ nil ∷ nil ∷ []

  ex-swap : exec 40 (caseSwap 1 2 0) s0 ≡ just ((atm 2 ∙ atm 1) ∷ nil ∷ nil ∷ [] , 12)
  ex-swap = refl

  -- the arm alone, without the dispatch node
  ex-arm : exec 40 (swapArm 1 2 0) s0 ≡ just ((atm 2 ∙ atm 1) ∷ nil ∷ nil ∷ [] , 11)
  ex-arm = refl

  -- and the round trip of §5: splitting and re-joining changes nothing
  ex-split-join : exec 40 (splitPat 1 2 0 ⨾ joinPat 0 1 2) s0 ≡ just (s0 , 11)
  ex-split-join = refl
