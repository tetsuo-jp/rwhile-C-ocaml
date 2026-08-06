{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE GUARDED BRACKET, the shape `src/Desugar.ml` expands `local`/`delocal`
-- and a `for`-counter into:
--
--     assert (=? X nil) ;  X ^= E ;  C ;  X ^= F ;  assert (=? X nil)
--
-- The two assertions are not decoration.  `X ^= E` is an XOR update, not a
-- binding: if X already holds E's value the same assignment CLEARS it, the body
-- then runs with X = nil, and the closing assignment puts the old value back --
-- a wrong answer with no error anywhere.  That is a real bug that was in this
-- repository on 2026-08-05; this module turns the argument into proofs and the
-- bug into a machine-checked counterexample.
--
-- What is proved here:
--
--   bracket-needs-nil   a run exists only when X is nil on entry
--   bracket-clears      X is nil again on exit
--   bracket-binds       the body really starts from `set s x v` where v is E's
--                       value -- i.e. the local is BOUND, not toggled
--   no-dirty-run        the guarded form has NO run from a store where X is
--                       already bound
--   ex-clean / ex-dirty the unguarded form RUNS from both, and returns
--                       DIFFERENT answers -- the silent wrong answer, executed
--                       inside the type checker
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSugar where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime
open import RWhileTimeInv using (eqV-sound; inv; inv-sound)
open import RWhileSIWf
  using (Wf; wf-skip; wf-ass; wf-seq; wf-cond; NotIn; InR)

------------------------------------------------------------------------
-- 1.  The pieces.  `assert E` is `if E fi 't`: two empty branches and an exit
--     assertion that is a true constant, so the else branch can never close.

trueE : Exp
trueE = opd (cst (boolV true))

nilTest : ℕ → Exp
nilTest x = eqE (var x) (cst nil)

assertNil : ℕ → Cmd
assertNil x = cond (nilTest x) skip skip trueE

bracket : ℕ → Exp → Cmd → Exp → Cmd
bracket x e c f =
  assertNil x ⨾ (x ^= e) ⨾ c ⨾ (x ^= f) ⨾ assertNil x

------------------------------------------------------------------------
-- 2.  What an assertion tells us.

nilTest-sound : ∀ x s → evalT s (nilTest x) ≡ just true → get s x ≡ nil
nilTest-sound x s p with eqV (get s x) nil in q
... | true  = eqV-sound (get s x) nil q
... | false with p
...   | ()

-- a run of `assert (=? X nil)` exists only if X is nil ...
assertNil-nil : ∀ {x s t k} → assertNil x ⊢ s ⇒ t ∣ k → get s x ≡ nil
assertNil-nil {x} {s} (e-then te _ _) = nilTest-sound x s te
assertNil-nil        (e-else _  _ ())

-- ... and it changes nothing (both branches are skip)
assertNil-id : ∀ {x s t k} → assertNil x ⊢ s ⇒ t ∣ k → t ≡ s
assertNil-id (e-then _ e-skip _) = refl
assertNil-id (e-else _ _ ())

-- ... and costs 2 in this model (the conditional node plus the `skip` in the
-- taken branch).  src/EvalRwhile.ml charges 1, because R-WHILE's grammar prints
-- an EMPTY branch where the model must write `skip`; that is the usual gap,
-- accounted for by RWhileTimeSkip.cost-split.
assertNil-cost : ∀ {x s t k} → assertNil x ⊢ s ⇒ t ∣ k → k ≡ 2
assertNil-cost (e-then _ e-skip _) = refl
assertNil-cost (e-else _ _ ())

------------------------------------------------------------------------
-- 3.  The bracket is a real binder.

bracket-needs-nil : ∀ {x e c f s t k}
                  → bracket x e c f ⊢ s ⇒ t ∣ k → get s x ≡ nil
bracket-needs-nil (e-seq g _) = assertNil-nil g

bracket-clears : ∀ {x e c f s t k}
               → bracket x e c f ⊢ s ⇒ t ∣ k → get t x ≡ nil
bracket-clears {x} (e-seq _ (e-seq _ (e-seq _ (e-seq _ g)))) =
  subst (λ w → get w x ≡ nil) (sym (assertNil-id g)) (assertNil-nil g)

-- The body starts from the store where X is BOUND to E's value.  This is the
-- statement the unguarded version fails: there the body would start from
-- `set s x nil` whenever X already held that value.
bracket-binds : ∀ {x e c f s t k}
              → bracket x e c f ⊢ s ⇒ t ∣ k
              → Σ[ v ∈ V ] (evalE s e ≡ just v ×
                  Σ[ u ∈ Store ] Σ[ m ∈ ℕ ] (c ⊢ set s x v ⇒ u ∣ m))
bracket-binds {x} {e} {c} {f} {s} (e-seq g (e-seq a (e-seq b _)))
  with assertNil-id g | assertNil-nil g
... | refl | nilx with a
...   | e-ass {v = v} {u = u} ev ru =
        v , ev , _ , _ ,
        subst (λ w → c ⊢ set s x w ⇒ _ ∣ _)
              (just-inj (trans (sym (subst (λ z → rupd z v ≡ just u) nilx ru))
                               refl))
              b
  where
    just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
    just-inj refl = refl

------------------------------------------------------------------------
-- 4.  THE COUNTEREXAMPLE, run inside the type checker.
--
--     X is variable 0, Y is variable 1, and the body is `Y ^= X`, so the answer
--     records what the body SAW.

private
  aE : Exp
  aE = opd (cst (atm 1))

  body : Cmd
  body = 1 ^= opd (var 0)

  -- Desugar.ml's expansion WITHOUT the two guards
  unguarded : Cmd
  unguarded = (0 ^= aE) ⨾ body ⨾ (0 ^= aE)

  guarded : Cmd
  guarded = bracket 0 aE body aE

  -- Entered with X = nil (the intended use): the body sees 'a, so Y := 'a.
  ex-clean : exec 10 unguarded (nil ∷ nil ∷ []) ≡ just (nil ∷ atm 1 ∷ [] , 5)
  ex-clean = refl

  -- Entered with X already holding 'a: the opening `X ^= 'a` CLEARS X, the body
  -- sees nil so Y stays nil, and the closing `X ^= 'a` puts 'a back.  Same
  -- program, same cost, DIFFERENT answer -- and no error is raised.
  ex-dirty : exec 10 unguarded (atm 1 ∷ nil ∷ []) ≡ just (atm 1 ∷ nil ∷ [] , 5)
  ex-dirty = refl

  -- The guarded form still runs from the clean store ...
  ex-guarded-clean :
    exec 20 guarded (nil ∷ nil ∷ []) ≡ just (nil ∷ atm 1 ∷ [] , 11)
  ex-guarded-clean = refl

  -- ... and has NO run at all from the dirty one.  That is the whole point of
  -- the guards: the wrong answer above is not reachable.
  no-dirty-run : ∀ {t k} → guarded ⊢ (atm 1 ∷ nil ∷ []) ⇒ t ∣ k → ⊥
  no-dirty-run d with bracket-needs-nil d
  ... | ()

------------------------------------------------------------------------
-- 5.  Inversion.  Nothing special is needed: `inv-sound` already holds for
--     every command, so it holds for the bracket -- the inverse runs backwards
--     at exactly the same cost.  Together with bracket-clears this is the
--     machine-checked form of what `examples/sugar.rwhile` shows by measurement
--     (50 steps in each direction).

-- The bracket is well-formed as soon as the body is and neither E nor F
-- mentions the bracketed variable -- which is exactly what `local X = E` means.
bracket-wf : ∀ {x e c f} → NotIn x e → NotIn x f → Wf c → Wf (bracket x e c f)
bracket-wf ne nf wc =
  wf-seq (wf-cond wf-skip wf-skip)
 (wf-seq (wf-ass ne)
 (wf-seq wc
 (wf-seq (wf-ass nf) (wf-cond wf-skip wf-skip))))

bracket-inv-cost : ∀ {x e c f s t k}
                 → NotIn x e → NotIn x f → Wf c
                 → InR (bracket x e c f) s
                 → bracket x e c f ⊢ s ⇒ t ∣ k
                 → inv (bracket x e c f) ⊢ t ⇒ s ∣ k
bracket-inv-cost ne nf wc = inv-sound (bracket-wf ne nf wc)
