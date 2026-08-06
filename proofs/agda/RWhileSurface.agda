{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- R-WHILE-S, the SURFACE language, and the correctness of compiling it away.
--
-- `src/Desugar.ml` defines the sugar BY its expansion, which makes "the
-- desugaring is correct" vacuous.  Here the surface forms get their own
-- semantics -- the rules a programmer would state, in terms of stores and not
-- of `if/fi` -- and compilation is proved to realise exactly those rules, cost
-- included:
--
--   compile-sound     every surface run is a run of the compiled program,
--                     at the same cost
--   compile-complete  and conversely, so the compiled program has no runs the
--                     surface language does not explain
--
-- Scope.  This is the TIMED core (RWhileTime), whose commands are skip, `^=`,
-- `;`, if/fi and from/until -- there is no pattern replacement `<=`, so the
-- sugar that expands to one (`X <-> Y`, `push`, `pop`) cannot be given a timed
-- semantics here.  That sugar lives in the other layer, where `RWhileCRep`
-- models `<=`; `case` is already covered there by `RWhileCaseInv`.  What is in
-- scope is exactly what compiles into the timed core: `assert`, the
-- `local`/`delocal` bracket, sequencing, and `for` (a bracket around a loop).
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSurface where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime
open import RWhileTimeDet using (⇒-det)
open import RWhileTimeInv using (eqV-sound)
open import RWhileSIWf using (get-set-≡; get-set-≢)
open import RWhileSugar
  using (trueE; nilTest; assertNil; bracket;
         assertNil-nil; assertNil-id; nilTest-sound;
         bracket-needs-nil; bracket-clears)

------------------------------------------------------------------------
-- 1.  Surface syntax.

infixr 3 _⨟_

data SCmd : Set where
  emb    : Cmd → SCmd                          -- a core command, unchanged
  _⨟_    : SCmd → SCmd → SCmd
  assert : Exp → SCmd                          -- assert E
  localD : ℕ → Exp → SCmd → Exp → SCmd         -- local X = E in C delocal X = F end

------------------------------------------------------------------------
-- 2.  Compilation -- literally what src/Desugar.ml does.

compile : SCmd → Cmd
compile (emb c)          = c
compile (a ⨟ b)          = compile a ⨾ compile b
compile (assert e)       = cond e skip skip trueE
compile (localD x e c f) = bracket x e (compile c) f

-- What the bracket costs, as the compiled shape computes it.  (`bcost k ≡ 10 + k`
-- below; the nested form is what the sequencing rule produces definitionally,
-- so keeping it makes compile-sound go through without arithmetic.)
bcost : ℕ → ℕ
bcost k = suc (2 + suc (1 + suc (k + 4)))

bcost≡ : ∀ k → bcost k ≡ 10 + k
bcost≡ k
  rewrite +-suc k 3 | +-suc k 2 | +-suc k 1 | +-suc k 0 | +-identityʳ k = refl

------------------------------------------------------------------------
-- 3.  Surface semantics.  Each sugar gets the rule a programmer would state.
--
--     `assert E` : E must hold; nothing changes.
--     `local X = E in C delocal X = F end` :
--        X must be nil on entry; E's value v is BOUND to X; the body runs from
--        there; F must name what X holds at the end, which is what clears it;
--        and X is nil again on exit.

infix 3 _⊩_⇒_∣_

data _⊩_⇒_∣_ : SCmd → Store → Store → ℕ → Set where

  s-emb : ∀ {c s t k} → c ⊢ s ⇒ t ∣ k → emb c ⊩ s ⇒ t ∣ k

  s-seq : ∀ {a b s t u k l}
        → a ⊩ s ⇒ t ∣ k → b ⊩ t ⇒ u ∣ l
        → (a ⨟ b) ⊩ s ⇒ u ∣ suc (k + l)

  s-assert : ∀ {e s} → evalT s e ≡ just true → assert e ⊩ s ⇒ s ∣ 2

  s-local : ∀ {x e c f s u v w k}
          → get s x ≡ nil                    -- X is free on entry
          → evalE s e ≡ just v               -- E's value ...
          → c ⊩ set s x v ⇒ u ∣ k            -- ... is what the body sees
          → evalE u f ≡ just w               -- F names ...
          → get u x ≡ w                      -- ... exactly what X holds, so it clears
          → localD x e c f ⊩ s ⇒ set u x nil ∣ bcost k

------------------------------------------------------------------------
-- 4.  Compilation realises the surface rules, cost included.

private
  -- `assert E` when E holds: the then-branch is taken and the exit assertion is
  -- a true constant, so it always closes.
  assert-run : ∀ {e s} → evalT s e ≡ just true
             → cond e skip skip trueE ⊢ s ⇒ s ∣ 2
  assert-run te = e-then te e-skip refl

  -- `X ^= E` on a store where X is nil: it SETS X (rupd nil v = just v).
  set-run : ∀ {x e s v} → get s x ≡ nil → evalE s e ≡ just v
          → (x ^= e) ⊢ s ⇒ set s x v ∣ 1
  set-run {x} {e} {s} {v} nx ev =
    e-ass ev (subst (λ z → rupd z v ≡ just v) (sym nx) refl)

  -- `X ^= F` where F names X's current value: it CLEARS X.
  clear-run : ∀ {x f s w} → evalE s f ≡ just w → get s x ≡ w
            → (x ^= f) ⊢ s ⇒ set s x nil ∣ 1
  clear-run {x} {f} {s} {w} ev gx =
    e-ass ev (subst (λ z → rupd z w ≡ just nil) (sym gx) (rupd-self w))

compile-sound : ∀ {c s t k} → c ⊩ s ⇒ t ∣ k → compile c ⊢ s ⇒ t ∣ k
compile-sound (s-emb d)      = d
compile-sound (s-seq a b)    = e-seq (compile-sound a) (compile-sound b)
compile-sound (s-assert te)  = assert-run te
compile-sound {localD x e c f} {s} (s-local {u = u} nx ev body fv gx) =
  e-seq (assert-run (nil→test s nx))
 (e-seq (set-run nx ev)
 (e-seq (compile-sound body)
 (e-seq (clear-run fv gx)
        (assert-run (nil→test (set u x nil) (get-set-≡ u x nil))))))
  where
    -- `=? X nil` is true exactly when X is nil
    nil→test : ∀ σ → get σ x ≡ nil → evalT σ (nilTest x) ≡ just true
    nil→test σ p rewrite p = refl

------------------------------------------------------------------------
-- 5.  ... and nothing else.  Every run of the compiled program comes from a
--     surface run, so the sugar hides no behaviour.

private
  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  -- An update that CLEARS a variable can only have been given that variable's
  -- own value.  (The nil case is the third branch of `rupd`: assigning nil to a
  -- nil variable also lands on nil.)
  rupd-clear : ∀ q v → rupd q v ≡ just nil → q ≡ v
  rupd-clear nil     v p = sym (just-inj p)
  rupd-clear (atm m) v p with eqV (atm m) v in q
  ... | true  = eqV-sound (atm m) v q
  ... | false with eqV v nil in r
  ...   | true  with p
  ...     | ()
  rupd-clear (atm m) v p | false | false with p
  ...   | ()
  rupd-clear (a ∙ b) v p with eqV (a ∙ b) v in q
  ... | true  = eqV-sound (a ∙ b) v q
  ... | false with eqV v nil in r
  ...   | true  with p
  ...     | ()
  rupd-clear (a ∙ b) v p | false | false with p
  ...   | ()

  -- The closing assertion sees `set σ x u′`, and it only passes when that slot
  -- is nil -- so the closing assignment really did clear X.
  cleared : ∀ {x σ u′ t k} → assertNil x ⊢ set σ x u′ ⇒ t ∣ k → u′ ≡ nil
  cleared {x} {σ} {u′} g = trans (sym (get-set-≡ σ x u′)) (assertNil-nil g)

compile-complete : ∀ c {s t k}
                 → compile c ⊢ s ⇒ t ∣ k
                 → Σ[ k′ ∈ ℕ ] (c ⊩ s ⇒ t ∣ k′)
compile-complete (emb _)    d = _ , s-emb d
compile-complete (a ⨟ b)    (e-seq da db)
  with compile-complete a da | compile-complete b db
... | _ , sa | _ , sb = _ , s-seq sa sb
compile-complete (assert e) (e-then te e-skip _) = _ , s-assert te
compile-complete (assert e) (e-else _ _ ())
compile-complete (localD x e c f)
    (e-seq g (e-seq (e-ass {v = v} {u = u} ev ru)
             (e-seq b (e-seq (e-ass {v = w} {u = u′} fv rw) g′))))
  with assertNil-id g | assertNil-nil g
... | refl | nx
  with just-inj (subst (λ q → rupd q v ≡ just u) nx ru)      -- v ≡ u
... | refl
  with assertNil-id g′ | cleared g′
... | refl | refl
  with compile-complete c b
... | _ , sb = _ , s-local nx ev sb fv (rupd-clear _ w rw)

------------------------------------------------------------------------
-- 6.  The two directions together pin the cost as well: the core is
--     deterministic, so a surface run and the compiled run agree exactly.

compile-cost : ∀ c {s t t′ k k′}
             → c ⊩ s ⇒ t ∣ k → compile c ⊢ s ⇒ t′ ∣ k′
             → t ≡ t′ × k ≡ k′
compile-cost _ d d′ = ⇒-det (compile-sound d) d′

------------------------------------------------------------------------
-- 7.  `for X = A to B do C end` is a bracket around a loop, so its counter
--     being loop-LOCAL is not a new theorem -- it is bracket-needs-nil and
--     bracket-clears, with no induction over the loop at all.

incr : ℕ → ℕ → Cmd            -- <X++> via one scratch T:  X := (nil . X)
incr x t =
  (t ^= cns (cst nil) (var x)) ⨾ (x ^= tlE (var t)) ⨾
  (x ^= opd (var t))           ⨾ (t ^= opd (var x))

forC : ℕ → ℕ → Opd → Opd → Cmd → Cmd
forC x t a b body =
  bracket x (opd a) (loop (eqE (var x) a) body (incr x t) (eqE (var x) b)) (opd b)

for-counter-local : ∀ {x t a b body s u k}
                  → forC x t a b body ⊢ s ⇒ u ∣ k
                  → (get s x ≡ nil) × (get u x ≡ nil)
for-counter-local d = bracket-needs-nil d , bracket-clears d

------------------------------------------------------------------------
-- 8.  The counter step `<X++>` itself.
--
--     src/Desugar.ml claims that sharing ONE scratch variable across every
--     expansion of a for-loop is safe, "because the scratch is set and cleared
--     within the increment, so it is nil before and after and nothing can
--     interleave".  That claim is what `incr-restores-scratch` below turns into
--     a theorem: T comes back nil, X has grown by exactly one nil, and the
--     whole step costs 7.
--
--     Route: build the run once (incr-run), then use determinism -- the same
--     trick as compile-cost.

private
  -- the four stores the four assignments walk through
  σ₁ σ₂ σ₃ σ₄ : Store → ℕ → ℕ → Store
  σ₁ σ x t = set σ t (nil ∙ get σ x)
  σ₂ σ x t = set (σ₁ σ x t) x nil
  σ₃ σ x t = set (σ₂ σ x t) x (nil ∙ get σ x)
  σ₄ σ x t = set (σ₃ σ x t) t nil

incr-run : ∀ {x t} σ → ¬ (x ≡ t) → ¬ (t ≡ x) → get σ t ≡ nil
         → incr x t ⊢ σ ⇒ σ₄ σ x t ∣ 7
incr-run {x} {t} σ nxt ntx gt =
  e-seq (e-ass refl (subst (λ z → rupd z (nil ∙ get σ x) ≡ just (nil ∙ get σ x))
                           (sym gt) refl))
 (e-seq (e-ass tl₁ (subst (λ z → rupd z (get σ x) ≡ just nil)
                          (sym g₁x) (rupd-self (get σ x))))
 (e-seq (e-ass (cong just g₂t)
               (subst (λ z → rupd z (nil ∙ get σ x) ≡ just (nil ∙ get σ x))
                      (sym (get-set-≡ (σ₁ σ x t) x nil)) refl))
        (e-ass (cong just (get-set-≡ (σ₂ σ x t) x (nil ∙ get σ x)))
               (subst (λ z → rupd z (nil ∙ get σ x) ≡ just nil)
                      (sym g₃t) (rupd-self (nil ∙ get σ x))))))
  where
    g₁t : get (σ₁ σ x t) t ≡ nil ∙ get σ x
    g₁t = get-set-≡ σ t (nil ∙ get σ x)
    g₁x : get (σ₁ σ x t) x ≡ get σ x
    g₁x = get-set-≢ σ t x (nil ∙ get σ x) ntx
    tl₁ : evalE (σ₁ σ x t) (tlE (var t)) ≡ just (get σ x)
    tl₁ rewrite g₁t = refl
    g₂t : get (σ₂ σ x t) t ≡ nil ∙ get σ x
    g₂t = trans (get-set-≢ (σ₁ σ x t) x t nil nxt) g₁t
    g₃t : get (σ₃ σ x t) t ≡ nil ∙ get σ x
    g₃t = trans (get-set-≢ (σ₂ σ x t) x t (nil ∙ get σ x) nxt) g₂t

-- What the step does, for ANY run of it: the counter grows by one, the scratch
-- comes back nil, and it costs 7.
incr-restores-scratch : ∀ {x t σ σ' k}
                      → ¬ (x ≡ t) → ¬ (t ≡ x) → get σ t ≡ nil
                      → incr x t ⊢ σ ⇒ σ' ∣ k
                      → (get σ' x ≡ (nil ∙ get σ x)) × (get σ' t ≡ nil) × (k ≡ 7)
incr-restores-scratch {x} {t} {σ} nxt ntx gt d
  with ⇒-det d (incr-run σ nxt ntx gt)
... | refl , refl =
    trans (get-set-≢ (σ₃ σ x t) t x nil ntx)
          (get-set-≡ (σ₂ σ x t) x (nil ∙ get σ x))
  , get-set-≡ (σ₃ σ x t) t nil
  , refl

------------------------------------------------------------------------
-- 9.  The loop inside a `for`.
--
--     src/Desugar.ml states two things about it in prose: "the body runs at
--     least once (A = B runs it exactly once)" and "the counter is loop-LOCAL:
--     it is nil before and after".  The first is immediate from the `e-loop`
--     rule; the second was proved via the bracket, but WHY the counter ends nil
--     -- because the loop leaves it equal to B, so the closing `X ^= B` clears
--     it -- needed the induction below.

private
  -- `=? A B` holding means the two operands really are equal
  eqTest-sound : ∀ σ a b → evalT σ (eqE a b) ≡ just true → evalO σ a ≡ evalO σ b
  eqTest-sound σ a b p with eqV (evalO σ a) (evalO σ b) in q
  ... | true  = eqV-sound (evalO σ a) (evalO σ b) q
  ... | false with p
  ...   | ()

-- However many times it went round, a loop whose exit test is `=? X B` stops
-- with X equal to B.  Induction on Rest; no assumption about the body at all.
rest-exits-at : ∀ {x b e D L w z n}
              → Rest e D L (eqE (var x) b) w z n
              → get z x ≡ evalO z b
rest-exits-at {x} {b} (r-exit p)         = eqTest-sound _ (var x) b p
rest-exits-at         (r-iter _ _ _ _ r) = rest-exits-at r

loop-exits-at : ∀ {x b e D L s u k}
              → loop e D L (eqE (var x) b) ⊢ s ⇒ u ∣ k
              → get u x ≡ evalO u b
loop-exits-at (e-loop _ _ r) = rest-exits-at r

-- The body runs at least once: `e-loop` runs D before consulting Rest, so even
-- `for X = A to A` executes the body.
loop-body-runs : ∀ {e D L f s u k}
               → loop e D L f ⊢ s ⇒ u ∣ k
               → Σ[ t ∈ Store ] Σ[ m ∈ ℕ ] (D ⊢ s ⇒ t ∣ m)
loop-body-runs (e-loop _ d _) = _ , _ , d

-- ONE trip round a for-loop, given that the body leaves the counter alone --
-- which src/Desugar.ml now checks at desugar time, after measuring on
-- 2026-08-06 that a body touching the counter silently changes the iteration
-- count.  The counter grows by exactly one nil.
for-iter-step : ∀ {x t body w y z k m}
              → (∀ {σ σ' j} → body ⊢ σ ⇒ σ' ∣ j → get σ' x ≡ get σ x)
              → ¬ (x ≡ t) → ¬ (t ≡ x) → get w t ≡ nil
              → incr x t ⊢ w ⇒ y ∣ k
              → body ⊢ y ⇒ z ∣ m
              → (get z x ≡ (nil ∙ get w x)) × (get y t ≡ nil)
for-iter-step {x} {t} keep nxt ntx gwt di db
  with incr-restores-scratch nxt ntx gwt di
... | gx , gt , _ = trans (keep db) gx , gt
