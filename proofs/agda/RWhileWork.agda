{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE `-work` METER AS A COST RELATION ON RUNS.
--
--   `c ⊢ s ⇒ t ∣ k ∥ w`   :  running c on s yields t, executing k command
--                            nodes (`./ri -steps`) and examining w value
--                            nodes by structural comparison (`./ri -work`).
--
-- The relation is RWhileTime's `c ⊢ s ⇒ t ∣ k` with a SECOND counter added,
-- not a replacement: `⇒w-steps` forgets the work and lands back in the old
-- relation, so the ~100 modules that speak about `∣ k` are untouched, and
-- `wk-sound` shows every old derivation carries a work annotation.  Nothing
-- in RWhileTime.agda was modified.
--
-- WHERE THE WORK COMES FROM.  Exactly two producers, and they are the two
-- charged sites of src/EvalRwhile.ml that exist in this layer:
--
--   `expW s e`             site (1): `=? A B`, and NOTHING else -- read the
--                          five other clauses, they are literally `0`.
--   `rupdW (get s x) v`    site (2): the clearing test of `x ^= e`, free
--                          when the slot is nil.
--
-- (Site (3), a literal pattern, belongs to the `<=` layer which the timed
-- core does not have; see RWhileWorkV's header.)  Tests of conditionals and
-- loops charge `expW` for the test expression itself, which is where a `=?`
-- in a loop guard gets paid for -- the "二次の仕事は =? の中に隠れる" effect
-- that RWHILE_S.md records and that `-steps` cannot see.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileWork where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileWorkV using (nodes; eqW; rupdW; eqW-pos; rupdW-fresh)

------------------------------------------------------------------------
-- 1.  The work charged by evaluating an expression.
--
-- `=? A B` pays for the comparison it performs; every other form is O(1)
-- (cons/hd/tl move one pointer, `pair?` inspects one constructor, a
-- variable read is a store lookup) and pays nothing.  This clause list IS
-- the claim "only `=?` is charged among expressions".

expW : Store → Exp → ℕ
expW s (opd a)   = 0
expW s (cns a b) = 0
expW s (hdE a)   = 0
expW s (tlE a)   = 0
expW s (eqE a b) = eqW (evalO s a) (evalO s b)
expW s (prE a)   = 0

-- the "not charged" list, spelled out so a reader can check it at a glance
expW-opd-free : ∀ s a     → expW s (opd a)   ≡ 0
expW-opd-free _ _ = refl
expW-cns-free : ∀ s a b   → expW s (cns a b) ≡ 0
expW-cns-free _ _ _ = refl
expW-hd-free  : ∀ s a     → expW s (hdE a)   ≡ 0
expW-hd-free _ _ = refl
expW-tl-free  : ∀ s a     → expW s (tlE a)   ≡ 0
expW-tl-free _ _ = refl
expW-pair-free : ∀ s a    → expW s (prE a)   ≡ 0
expW-pair-free _ _ = refl

-- ... and the one that is charged, at the size of what it compares
expW-eq : ∀ s a b → expW s (eqE a b) ≡ eqW (evalO s a) (evalO s b)
expW-eq _ _ _ = refl

expW-eq-pos : ∀ s a b → 1 ≤ expW s (eqE a b)
expW-eq-pos s a b = eqW-pos (evalO s a) (evalO s b)

------------------------------------------------------------------------
-- 2.  The doubly-annotated cost relation.

infix 3 _⊢_⇒_∣_∥_

data _⊢_⇒_∣_∥_ : Cmd → Store → Store → ℕ → ℕ → Set
data RestW (e : Exp) (D L : Cmd) (f : Exp) : Store → Store → ℕ → ℕ → Set

data _⊢_⇒_∣_∥_ where
  w-skip : ∀ {s} → skip ⊢ s ⇒ s ∣ 1 ∥ 0
  w-ass  : ∀ {x e s v u}
         → evalE s e ≡ just v
         → rupd (get s x) v ≡ just u
         → (x ^= e) ⊢ s ⇒ set s x u ∣ 1 ∥ (expW s e + rupdW (get s x) v)
  w-seq  : ∀ {c d s t u k l w w′}
         → c ⊢ s ⇒ t ∣ k ∥ w → d ⊢ t ⇒ u ∣ l ∥ w′
         → (c ⨾ d) ⊢ s ⇒ u ∣ suc (k + l) ∥ (w + w′)
  w-then : ∀ {e c d f s t k w}
         → evalT s e ≡ just true → c ⊢ s ⇒ t ∣ k ∥ w → evalT t f ≡ just true
         → cond e c d f ⊢ s ⇒ t ∣ suc k ∥ (expW s e + w + expW t f)
  w-else : ∀ {e c d f s t k w}
         → evalT s e ≡ just false → d ⊢ s ⇒ t ∣ k ∥ w → evalT t f ≡ just false
         → cond e c d f ⊢ s ⇒ t ∣ suc k ∥ (expW s e + w + expW t f)
  w-loop : ∀ {e D L f s t u k n w wr}
         → evalT s e ≡ just true → D ⊢ s ⇒ t ∣ k ∥ w → RestW e D L f t u n wr
         → loop e D L f ⊢ s ⇒ u ∣ suc (k + n) ∥ (expW s e + w + wr)

data RestW e D L f where
  rw-exit : ∀ {w} → evalT w f ≡ just true → RestW e D L f w w 0 (expW w f)
  rw-iter : ∀ {w x y z k m n wl wd wr}
          → evalT w f ≡ just false
          → L ⊢ w ⇒ x ∣ k ∥ wl
          → evalT x e ≡ just false
          → D ⊢ x ⇒ y ∣ m ∥ wd
          → RestW e D L f y z n wr
          → RestW e D L f w z (k + m + n) (expW w f + wl + expW x e + wd + wr)

------------------------------------------------------------------------
-- 3.  FORGETTING THE WORK lands in RWhileTime's relation, with the same
--     step count.  This is what makes the addition conservative: anything
--     proved about `∣ k` applies verbatim to a work-annotated run.

⇒w-steps  : ∀ {c s t k w} → c ⊢ s ⇒ t ∣ k ∥ w → c ⊢ s ⇒ t ∣ k
RestW-Rest : ∀ {e D L f s t n w} → RestW e D L f s t n w → Rest e D L f s t n

⇒w-steps w-skip            = e-skip
⇒w-steps (w-ass ev ru)     = e-ass ev ru
⇒w-steps (w-seq d₁ d₂)     = e-seq (⇒w-steps d₁) (⇒w-steps d₂)
⇒w-steps (w-then t d f)    = e-then t (⇒w-steps d) f
⇒w-steps (w-else t d f)    = e-else t (⇒w-steps d) f
⇒w-steps (w-loop t d r)    = e-loop t (⇒w-steps d) (RestW-Rest r)

RestW-Rest (rw-exit f)            = r-exit f
RestW-Rest (rw-iter f dL e dD r)  =
  r-iter f (⇒w-steps dL) e (⇒w-steps dD) (RestW-Rest r)

------------------------------------------------------------------------
-- 4.  ... and every RWhileTime derivation HAS a work annotation, computed
--     from it by `wk`.  Together with 3 this says the two relations
--     describe the same runs; `wk d` is the number `./ri -work` prints.
--
--     Because `wk` is a function of the derivation and `exec-sound` turns a
--     COMPUTED run into a derivation, `wk (exec-sound n c s t k refl)`
--     evaluates -- which is how the worked examples below get their numbers
--     by `refl` rather than by hand.

wk  : ∀ {c s t k} → c ⊢ s ⇒ t ∣ k → ℕ
wkR : ∀ {e D L f s t n} → Rest e D L f s t n → ℕ

wk (e-skip {s})                              = 0
wk (e-ass {x} {e} {s} {v} _ _)               = expW s e + rupdW (get s x) v
wk (e-seq d₁ d₂)                             = wk d₁ + wk d₂
wk (e-then {e} {_} {_} {f} {s} {t} _ d _)    = expW s e + wk d + expW t f
wk (e-else {e} {_} {_} {f} {s} {t} _ d _)    = expW s e + wk d + expW t f
wk (e-loop {e} {_} {_} {_} {s} _ d r)        = expW s e + wk d + wkR r

wkR {f = f} (r-exit {w} _)                   = expW w f
wkR {e} {f = f} (r-iter {w} {x} _ dL _ dD r) =
  expW w f + wk dL + expW x e + wk dD + wkR r

wk-sound  : ∀ {c s t k} (d : c ⊢ s ⇒ t ∣ k) → c ⊢ s ⇒ t ∣ k ∥ wk d
wkR-sound : ∀ {e D L f s t n} (r : Rest e D L f s t n) → RestW e D L f s t n (wkR r)

wk-sound e-skip           = w-skip
wk-sound (e-ass ev ru)    = w-ass ev ru
wk-sound (e-seq d₁ d₂)    = w-seq (wk-sound d₁) (wk-sound d₂)
wk-sound (e-then t d f)   = w-then t (wk-sound d) f
wk-sound (e-else t d f)   = w-else t (wk-sound d) f
wk-sound (e-loop t d r)   = w-loop t (wk-sound d) (wkR-sound r)

wkR-sound (r-exit f)           = rw-exit f
wkR-sound (r-iter f dL e dD r) =
  rw-iter f (wk-sound dL) e (wk-sound dD) (wkR-sound r)

-- the packaged statement: a run has A work cost, whatever it is.
⇒-has-work : ∀ {c s t k} → c ⊢ s ⇒ t ∣ k → Σ[ w ∈ ℕ ] (c ⊢ s ⇒ t ∣ k ∥ w)
⇒-has-work d = wk d , wk-sound d

------------------------------------------------------------------------
-- 5.  WORK AND STEPS ARE INDEPENDENT.  The point of adding the meter.

-- (a) A run can execute commands and do NO work: `skip` and assignments
--     into nil slots are free, however many of them there are.
skip-free : ∀ {s} → wk (e-skip {s}) ≡ 0
skip-free = refl

fresh-ass-free : ∀ {x e s v u} (ev : evalE s e ≡ just v)
               → (ru : rupd (get s x) v ≡ just u)
               → get s x ≡ nil → expW s e ≡ 0
               → wk (e-ass {x} {e} {s} {v} {u} ev ru) ≡ 0
fresh-ass-free {x} {e} {s} {v} ev ru hn he =
  cong₂ _+_ he (cong (λ w → rupdW w v) hn)

-- (b) Conversely ONE command node can do arbitrarily much work: a single
--     `x ^= =? A B` on equal values of size n costs 1 step and ≥ n work.
--     So no function of the step count bounds the work: the two meters are
--     genuinely different, which is why the Jones-optimality claim has to
--     say which one it is measured on.
open import RWhileWorkV using (eqW-refl)

one-step-much-work :
    ∀ {x u} v (s : Store) (a b : Opd)
  → evalO s a ≡ v → evalO s b ≡ v
  → (ev : evalE s (eqE a b) ≡ just (boolV true))
  → (ru : rupd (get s x) (boolV true) ≡ just u)
  → wk (e-ass {x} {eqE a b} {s} {boolV true} {u} ev ru)
    ≡ nodes v + rupdW (get s x) (boolV true)
one-step-much-work {x} v s a b ha hb ev ru =
  cong (λ n → n + rupdW (get s x) (boolV true))
       (trans (cong₂ eqW ha hb) (eqW-refl v))
