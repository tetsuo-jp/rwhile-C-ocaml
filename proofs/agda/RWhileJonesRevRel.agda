{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- REVERSIBLE JONES OPTIMALITY OVER A **PARTIAL** SEMANTICS.
--
-- RWhileJonesRev states the criterion over a TOTAL semantics
-- `⟦_⟧ : P → D → D`.  The timed core (RWhileTime) does not have one: its
-- semantics is the RELATION `c ⊢ s ⇒ t ∣ k`, which is partial (a loop may
-- diverge, an `if/fi` exit assertion may fail).  That mismatch is the reason
-- "R-WHILE's p⁺ satisfies the criterion's PP" was stated twice — once
-- abstractly, once concretely — instead of once.  This module removes it.
--
-- WHY A RELATION AND NOT `Maybe`.  The obvious repair is to lift the
-- semantics to `⟦_⟧ : P → D → Maybe D`.  It does not work HERE: such a
-- function is a total computable map that DECIDES convergence, and there is
-- no way to define one from the timed relation without solving the halting
-- problem.  Writing it down would need a postulate (banned in this
-- development) or a fuel index — and a fuel index breaks the obligation,
-- because p and p⁺ do not converge at the same fuel.  A relation, by
-- contrast, is exactly what the timed core already is, so the instance costs
-- nothing: see RWhileJonesRevTimed.
--
-- WHAT REPLACES THE EQUATION.  With a partial semantics `⟦q⟧ d ≡ ⌜p⌝ ⊗ ⟦p⟧ d`
-- becomes KLEENE EQUALITY, spelled as two implications:
--
--   PP⇒ q p :  wherever p converges, q converges to the PAIRED answer;
--   PP⇐ q p :  q converges only where p does.
--
-- Both halves earn their keep.  PP⇒ alone gives `pp-answer` and the cost
-- theorems; PP⇐ is what makes `pp-unique` and `pp-injective` true (without
-- it, q could compute anything it likes off p's domain).
--
-- Likewise `cost r d ≤ cost q d` becomes a DEFINEDNESS-MONOTONE order
--
--   r ≼ q :  wherever q converges at cost k, r converges at cost j ≤ k
--
-- which is reflexive and transitive, so `classical⇒rev` is still one
-- composition.
--
-- The total setting is the special case: `module FromTotal` instantiates the
-- relation at the graph of a total `⟦_⟧` and proves that every notion here
-- agrees, in BOTH directions, with RWhileJonesRev's.  So nothing was lost.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileJonesRevRel where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

import RWhileJonesRev

------------------------------------------------------------------------
-- The abstract setting, relationally.
--
--   D                data
--   P                programs
--   p ⊨ d ⇓ v ∣ k    running p on d converges to v at cost k
--   ⇓-det            the semantics is deterministic (R-WHILE is:
--                    RWhileTimeDet.⇒-det); this is what lets a relation
--                    play the role of a function
--   p2d              the program encoding ⌜·⌝
--   _⊗_              pairing

module CriterionR
  (D P : Set)
  (_⊨_⇓_∣_ : P → D → D → ℕ → Set)
  (⇓-det : ∀ {p d v₁ v₂ k₁ k₂}
         → p ⊨ d ⇓ v₁ ∣ k₁ → p ⊨ d ⇓ v₂ ∣ k₂ → (v₁ ≡ v₂) × (k₁ ≡ k₂))
  (p2d : P → D)
  (_⊗_ : D → D → D)
  where

  ----------------------------------------------------------------------
  -- 1.  Convergence and the obligation.

  Conv : P → D → Set
  Conv p d = Σ[ v ∈ D ] Σ[ k ∈ ℕ ] (p ⊨ d ⇓ v ∣ k)

  -- forward half: q does p's job and carries p's text to the output
  PP⇒ : P → P → Set
  PP⇒ q p = ∀ {d v k} → p ⊨ d ⇓ v ∣ k → Σ[ j ∈ ℕ ] (q ⊨ d ⇓ (p2d p ⊗ v) ∣ j)

  -- backward half: q is defined nowhere else
  PP⇐ : P → P → Set
  PP⇐ q p = ∀ {d u k} → q ⊨ d ⇓ u ∣ k → Conv p d

  PP : P → P → Set
  PP q p = PP⇒ q p × PP⇐ q p

  ----------------------------------------------------------------------
  -- 2.  The obligation pins the answer down.

  -- on p's domain, ANY program meeting the obligation returns ⟨⌜p⌝ , answer⟩
  pp-answer : ∀ {q p d v k u j} → PP⇒ q p
            → p ⊨ d ⇓ v ∣ k → q ⊨ d ⇓ u ∣ j → u ≡ p2d p ⊗ v
  pp-answer ppq dp dq = proj₁ (⇓-det dq (proj₂ (ppq dp)))

  -- hence any two programs meeting it agree wherever either is defined:
  -- the only freedom left is COST, which is what a Jones-style criterion
  -- compares.  (This is where PP⇐ is used: it moves us onto p's domain.)
  pp-unique : ∀ {q₁ q₂ p d u₁ u₂ k₁ k₂}
            → PP⇒ q₁ p → PP⇒ q₂ p → PP⇐ q₁ p
            → q₁ ⊨ d ⇓ u₁ ∣ k₁ → q₂ ⊨ d ⇓ u₂ ∣ k₂ → u₁ ≡ u₂
  pp-unique f₁ f₂ b d₁ d₂ with b d₁
  ... | v , k , dp = trans (pp-answer f₁ dp d₁) (sym (pp-answer f₂ dp d₂))

  -- the domains agree, both ways
  pp-dom⇒ : ∀ {q p d} → PP⇒ q p → Conv p d → Conv q d
  pp-dom⇒ {q} {p} f (v , k , dp) = (p2d p ⊗ v) , proj₁ (f dp) , proj₂ (f dp)

  pp-dom⇐ : ∀ {q p d} → PP⇐ q p → Conv q d → Conv p d
  pp-dom⇐ b (u , k , dq) = b dq

  ----------------------------------------------------------------------
  -- 3.  Injectivity (the reversibility side of the obligation).

  ⊗-injectiveʳ : Set
  ⊗-injectiveʳ = ∀ {a x z} → (a ⊗ x) ≡ (a ⊗ z) → x ≡ z

  -- a partial function is injective if it never sends two inputs to one
  -- answer (on the inputs where it IS defined)
  Inj : P → Set
  Inj p = ∀ {d₁ d₂ v₁ v₂ k₁ k₂}
        → p ⊨ d₁ ⇓ v₁ ∣ k₁ → p ⊨ d₂ ⇓ v₂ ∣ k₂ → v₁ ≡ v₂ → d₁ ≡ d₂

  pp-injective : ∀ {q p} → ⊗-injectiveʳ → PP q p → Inj p → Inj q
  pp-injective ⊗inj (f , b) inj dq₁ dq₂ eq with b dq₁ | b dq₂
  ... | v₁ , k₁ , dp₁ | v₂ , k₂ , dp₂ =
        inj dp₁ dp₂ (⊗inj (trans (sym (pp-answer f dp₁ dq₁))
                                 (trans eq (pp-answer f dp₂ dq₂))))

  ----------------------------------------------------------------------
  -- 4.  The cost order, and the two criteria.
  --
  -- `r ≼ q` : r is defined wherever q is, and no dearer there.  Over a total
  -- semantics this is exactly `∀ d → cost r d ≤ cost q d` (see FromTotal).

  _≼_ : P → P → Set
  r ≼ q = ∀ {d u k} → q ⊨ d ⇓ u ∣ k
        → Σ[ w ∈ D ] Σ[ j ∈ ℕ ] ((r ⊨ d ⇓ w ∣ j) × (j ≤ k))

  ≼-refl : ∀ {r} → r ≼ r
  ≼-refl {r} {d} {u} {k} dr = u , k , dr , ≤-refl

  ≼-trans : ∀ {r q s} → r ≼ q → q ≼ s → r ≼ s
  ≼-trans rq qs ds with qs ds
  ... | u , j , dq , le with rq dq
  ...   | w , i , dr , le′ = w , i , dr , ≤-trans le′ le

  -- classical: the residual is no more expensive than the source program.
  JonesOptimal : P → P → Set
  JonesOptimal r p = r ≼ p

  -- reversible: no more expensive than a basis CARRYING THE SAME OBLIGATION.
  RevJonesOptimal : P → P → P → Set
  RevJonesOptimal r p q = PP q p × (r ≼ q)

  classical⇒rev : ∀ {r p q} → PP q p → p ≼ q
                → JonesOptimal r p → RevJonesOptimal r p q
  classical⇒rev ppq mono jo = ppq , ≼-trans jo mono

  rev-mono : ∀ {r p q q′} → PP q′ p → q ≼ q′
           → RevJonesOptimal r p q → RevJonesOptimal r p q′
  rev-mono ppq′ mono (_ , le) = ppq′ , ≼-trans le mono

  ----------------------------------------------------------------------
  -- 5.  WHY THE BASIS MUST CARRY THE OBLIGATION (the fp1 layer).
  --
  -- The two defining equations of a reversible Futamura projection, each
  -- now in both directions because the semantics is partial.

  module Fp1
    (rint : P)
    (spec : P → D → P)
    (def-rint⇒ : ∀ {p d v k} → p ⊨ d ⇓ v ∣ k
               → Σ[ j ∈ ℕ ] (rint ⊨ (p2d p ⊗ d) ⇓ (p2d p ⊗ v) ∣ j))
    (def-rint⇐ : ∀ {p d u k} → rint ⊨ (p2d p ⊗ d) ⇓ u ∣ k → Conv p d)
    (def-spec⇒ : ∀ {q s d v k} → q ⊨ (s ⊗ d) ⇓ v ∣ k
               → Σ[ j ∈ ℕ ] (spec q s ⊨ d ⇓ v ∣ j))
    (def-spec⇐ : ∀ {q s d u k} → spec q s ⊨ d ⇓ u ∣ k
               → Σ[ j ∈ ℕ ] (q ⊨ (s ⊗ d) ⇓ u ∣ j))
    where

    residual : P → P
    residual p = spec rint (p2d p)

    -- THE KEY FACT: the residual inherits the interpreter's obligation.
    residual-pp : ∀ p → PP (residual p) p
    residual-pp p = fwd , bwd
      where
        fwd : PP⇒ (residual p) p
        fwd dp = def-spec⇒ (proj₂ (def-rint⇒ dp))
        bwd : PP⇐ (residual p) p
        bwd dr = def-rint⇐ (proj₂ (def-spec⇐ dr))

    -- so the residual and ANY program-preserving basis compute one function:
    -- `residual ≤ p⁺` compares two implementations of ONE specification.
    residual-same-spec : ∀ p q {d u₁ u₂ k₁ k₂} → PP⇒ q p
                       → residual p ⊨ d ⇓ u₁ ∣ k₁ → q ⊨ d ⇓ u₂ ∣ k₂ → u₁ ≡ u₂
    residual-same-spec p q ppq =
      pp-unique (proj₁ (residual-pp p)) ppq (proj₂ (residual-pp p))

    residual-injective : ∀ p → ⊗-injectiveʳ → Inj p → Inj (residual p)
    residual-injective p ⊗inj inj = pp-injective ⊗inj (residual-pp p) inj

    basis-adequate : ∀ p q {d u₁ u₂ k₁ k₂} → PP⇒ q p
                   → residual p ⊨ d ⇓ u₁ ∣ k₁ → q ⊨ d ⇓ u₂ ∣ k₂ → u₁ ≡ u₂
    basis-adequate = residual-same-spec

------------------------------------------------------------------------
-- THE TOTAL SETTING IS THE SPECIAL CASE.
--
-- Instantiate the relation at the GRAPH of a total semantics.  Every notion
-- of CriterionR then coincides with the corresponding notion of
-- RWhileJonesRev.Criterion — and the proofs go both ways, so the
-- generalisation is conservative: it neither weakens nor strengthens what
-- the earlier module says about total programs.

module FromTotal
  (D P : Set)
  (⟦_⟧ : P → D → D)
  (cost : P → D → ℕ)
  (p2d : P → D)
  (_⊗_ : D → D → D)
  where

  -- the graph of ⟦_⟧ together with its cost
  Graph : P → D → D → ℕ → Set
  Graph p d v k = (⟦ p ⟧ d ≡ v) × (cost p d ≡ k)

  graph-det : ∀ {p d v₁ v₂ k₁ k₂}
            → Graph p d v₁ k₁ → Graph p d v₂ k₂ → (v₁ ≡ v₂) × (k₁ ≡ k₂)
  graph-det (e₁ , c₁) (e₂ , c₂) = trans (sym e₁) e₂ , trans (sym c₁) c₂

  -- every program converges everywhere, by construction
  graph-run : ∀ p d → Graph p d (⟦ p ⟧ d) (cost p d)
  graph-run p d = refl , refl

  module R = CriterionR D P Graph graph-det p2d _⊗_
  module T = RWhileJonesRev.Criterion D P ⟦_⟧ cost p2d _⊗_

  ----------------------------------------------------------------------
  -- The obligation: the equation and the Kleene pair say the same thing.

  PP-total⇒rel : ∀ {q p} → T.PP q p → R.PP q p
  PP-total⇒rel {q} {p} h = fwd , bwd
    where
      fwd : R.PP⇒ q p
      fwd {d} {v} (e , _) = cost q d , trans (h d) (cong (p2d p ⊗_) e) , refl
      bwd : R.PP⇐ q p
      bwd {d} _ = ⟦ p ⟧ d , cost p d , refl , refl

  PP-rel⇒total : ∀ {q p} → R.PP⇒ q p → T.PP q p
  PP-rel⇒total {q} {p} f d = proj₁ (proj₂ (f {d} (graph-run p d)))

  ----------------------------------------------------------------------
  -- The cost order: `≼` and the pointwise `≤` say the same thing.

  ≼-total⇒rel : ∀ {r q} → (∀ d → cost r d ≤ cost q d) → r R.≼ q
  ≼-total⇒rel {r} {q} h {d} {u} {k} (_ , c) =
    ⟦ r ⟧ d , cost r d , (refl , refl) , subst (cost r d ≤_) c (h d)

  ≼-rel⇒total : ∀ {r q} → r R.≼ q → ∀ d → cost r d ≤ cost q d
  ≼-rel⇒total {r} {q} h d with h {d} (graph-run q d)
  ... | w , j , (_ , c) , le = subst (_≤ cost q d) (sym c) le

  ----------------------------------------------------------------------
  -- ... and therefore the two criteria coincide.

  jones-total⇒rel : ∀ {r p} → T.JonesOptimal r p → R.JonesOptimal r p
  jones-total⇒rel = ≼-total⇒rel

  jones-rel⇒total : ∀ {r p} → R.JonesOptimal r p → T.JonesOptimal r p
  jones-rel⇒total = ≼-rel⇒total

  rev-total⇒rel : ∀ {r p q} → T.RevJonesOptimal r p q → R.RevJonesOptimal r p q
  rev-total⇒rel (ppq , le) = PP-total⇒rel ppq , ≼-total⇒rel le

  rev-rel⇒total : ∀ {r p q} → R.RevJonesOptimal r p q → T.RevJonesOptimal r p q
  rev-rel⇒total (ppq , le) = PP-rel⇒total (proj₁ ppq) , ≼-rel⇒total le
