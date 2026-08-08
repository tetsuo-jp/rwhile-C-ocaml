{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Part of the r-Turing completeness development; see RWhileRTM.agda
-- for the overview.  Split into several modules so that Agda's peak
-- memory stays bounded (one module held all of it and needed 47 GB).
------------------------------------------------------------------------

module RWhileRTM2 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileTimeInv using (inv)
open import RWhileSIWf
  using (get-set-≡; get-set-≢; Wf; wf-skip; wf-ass; wf-seq; wf-cond; wf-loop;
         NotIn; ni-opd; ni-cns; ni-hd; ni-tl; ni-eq; ni-pr; ni-var; ni-cst)

open import RWhileRTM1 public

------------------------------------------------------------------------
-- 6.  PUSH and POP (Fig. 2c, 2d).
--
-- The letter writes
--     PUSH(S,STK) ≡ rewrite [S,STK] by [b̄,nil] => [nil,nil]
--                                    | [S,STK] => [nil,(S.STK)]
-- i.e. "push S onto STK, except that a blank pushed onto the empty stack
-- disappears".  Pushing UNCONDITIONALLY and then normalising is the same
-- function, and its guard is a single equality against a constant:
--
--     STK ^= cons S STK ;  S ^= hd STK ;
--     if STK =? (b̄ . nil) then STK ^= (b̄ . nil) else skip fi STK =? nil
--
-- The exit assertion separates the branches: after the then-branch STK is
-- nil, after the else-branch it is a cons.
--
-- CAUTION (a real trap, found while checking this).  The obvious first
-- attempt
--        STK ^= cons S STK ;  S ^= hd STK ;  …
-- is NOT R-WHILE: the assigned variable occurs in the expression, which the
-- language forbids, and the semantics agrees — `rupd` sends a non-nil STK
-- and the value (S . STK) to `nothing`, so the command is simply stuck.
-- That linearity side condition is exactly why the letter builds PUSH from
-- the pattern replacement `<=` and not from `^=`.  Going through a scratch
-- variable W restores it: every assignment below either sets a nil variable
-- or clears one holding precisely the value named on the right, and in none
-- of them does the target occur in the expression.

pushC : ℕ → ℕ → ℕ → ℕ → Cmd
pushC b s stk w =
    w   ^= cns (var s) (var stk)          -- W   := (S . STK)   [W was nil]
  ⨾ s   ^= hdE (var w)                    -- S   = hd W         → clear S
  ⨾ stk ^= tlE (var w)                    -- STK = tl W         → clear STK
  ⨾ stk ^= opd (var w)                    -- STK := W           [STK now nil]
  ⨾ w   ^= opd (var stk)                  -- W   = STK          → clear W
  ⨾ cond (eqE (var stk) (cst (atm b ∙ nil)))
         (stk ^= opd (cst (atm b ∙ nil))) -- drop the blank: STK := nil
         skip
         (eqE (var stk) (cst nil))

popC : ℕ → ℕ → ℕ → ℕ → Cmd
popC b s stk w = inv (pushC b s stk w)


------------------------------------------------------------------------
-- 6b.  PUSH IS CORRECT.
--
-- `pushC` realises the letter's PUSH: from S = s̄ and STK = r̄ it reaches
-- S = nil and STK = encL (consNB b s r) — that is, it pushes s onto r
-- unless s is the blank and r is empty, in which case the blank vanishes.
-- Both of the letter's `rewrite` clauses are therefore accounted for, and
-- the scratch cell W comes back nil, so PUSH can be used again.

module Push (b s stk w : ℕ)
            (w≢s : ¬ (w ≡ s)) (w≢stk : ¬ (w ≡ stk)) (s≢stk : ¬ (s ≡ stk)) where

  private
    s≢w : ¬ (s ≡ w)
    s≢w e = w≢s (sym e)
    stk≢w : ¬ (stk ≡ w)
    stk≢w e = w≢stk (sym e)
    stk≢s : ¬ (stk ≡ s)
    stk≢s e = s≢stk (sym e)

  -- The straight-line part: the five assignments, their intermediate stores
  -- and the facts about them.  Shared by every case of the normalisation.
  module Run (σ : Store) (x : ℕ) (r : List ℕ)
             (hs : get σ s ≡ atm x) (hstk : get σ stk ≡ encL r)
             (hw : get σ w ≡ nil) where

    v : V
    v = atm x ∙ encL r

    τ1 τ2 τ3 τ4 τ5 : Store
    τ1 = set σ  w   v
    τ2 = set τ1 s   nil
    τ3 = set τ2 stk nil
    τ4 = set τ3 stk v
    τ5 = set τ4 w   nil

    g1s : get τ1 s ≡ atm x
    g1s = trans (get-set-≢ σ w s v w≢s) hs
    g1w : get τ1 w ≡ v
    g1w = get-set-≡ σ w v
    g1stk : get τ1 stk ≡ encL r
    g1stk = trans (get-set-≢ σ w stk v w≢stk) hstk

    g2w : get τ2 w ≡ v
    g2w = trans (get-set-≢ τ1 s w nil s≢w) g1w
    g2stk : get τ2 stk ≡ encL r
    g2stk = trans (get-set-≢ τ1 s stk nil s≢stk) g1stk
    g2s : get τ2 s ≡ nil
    g2s = get-set-≡ τ1 s nil

    g3w : get τ3 w ≡ v
    g3w = trans (get-set-≢ τ2 stk w nil stk≢w) g2w
    g3stk : get τ3 stk ≡ nil
    g3stk = get-set-≡ τ2 stk nil
    g3s : get τ3 s ≡ nil
    g3s = trans (get-set-≢ τ2 stk s nil stk≢s) g2s

    g4stk : get τ4 stk ≡ v
    g4stk = get-set-≡ τ3 stk v
    g4w : get τ4 w ≡ v
    g4w = trans (get-set-≢ τ3 stk w v stk≢w) g3w
    g4s : get τ4 s ≡ nil
    g4s = trans (get-set-≢ τ3 stk s v stk≢s) g3s

    g5stk : get τ5 stk ≡ v
    g5stk = trans (get-set-≢ τ4 w stk nil w≢stk) g4stk
    g5s : get τ5 s ≡ nil
    g5s = trans (get-set-≢ τ4 w s nil w≢s) g4s
    g5w : get τ5 w ≡ nil
    g5w = get-set-≡ τ4 w nil

    -- nothing but s, stk and w moves
    frame5 : ∀ y → ¬ (y ≡ s) → ¬ (y ≡ stk) → ¬ (y ≡ w) → get τ5 y ≡ get σ y
    frame5 y ys ystk yw =
      trans (get-set-≢ τ4 w y nil (λ e → yw (sym e)))
      (trans (get-set-≢ τ3 stk y v (λ e → ystk (sym e)))
      (trans (get-set-≢ τ2 stk y nil (λ e → ystk (sym e)))
      (trans (get-set-≢ τ1 s y nil (λ e → ys (sym e)))
             (get-set-≢ σ w y v (λ e → yw (sym e))))))

    -- `STK =? c` reads whatever STK holds
    testEq : ∀ (τ : Store) (u c : V) → get τ stk ≡ u
           → evalT τ (eqE (var stk) (cst c)) ≡ just (eqV u c)
    testEq τ u c h rewrite h = cong just (isTrue-boolV (eqV u c))

    d1 : (w ^= cns (var s) (var stk)) ⊢ σ ⇒ τ1 ∣ 1
    d1 = e-ass (cong just (cong₂ _∙_ hs hstk))
               (subst (λ z → rupd z v ≡ just v) (sym hw) refl)

    d2 : (s ^= hdE (var w)) ⊢ τ1 ⇒ τ2 ∣ 1
    d2 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g1w) refl)
               (subst (λ z → rupd z (atm x) ≡ just nil) (sym g1s) (rupd-self (atm x)))

    d3 : (stk ^= tlE (var w)) ⊢ τ2 ⇒ τ3 ∣ 1
    d3 = e-ass (subst (λ z → tlM z ≡ just (encL r)) (sym g2w) refl)
               (subst (λ z → rupd z (encL r) ≡ just nil) (sym g2stk) (rupd-self (encL r)))

    d4 : (stk ^= opd (var w)) ⊢ τ3 ⇒ τ4 ∣ 1
    d4 = e-ass (cong just g3w)
               (subst (λ z → rupd z v ≡ just v) (sym g3stk) refl)

    d5 : (w ^= opd (var stk)) ⊢ τ4 ⇒ τ5 ∣ 1
    d5 = e-ass (cong just g4stk)
               (subst (λ z → rupd z v ≡ just nil) (sym g4w) (rupd-self v))

    pre : ∀ {τ k} → cond (eqE (var stk) (cst (atm b ∙ nil)))
                         (stk ^= opd (cst (atm b ∙ nil))) skip
                         (eqE (var stk) (cst nil)) ⊢ τ5 ⇒ τ ∣ k
        → pushC b s stk w ⊢ σ ⇒ τ ∣ suc (1 + suc (1 + suc (1 + suc (1 + suc (1 + k)))))
    pre dc = e-seq d1 (e-seq d2 (e-seq d3 (e-seq d4 (e-seq d5 dc))))

  -- The statement: PUSH turns (S,STK) = (s̄, r̄) into (nil, consNB b s r).
  PushSpec : Store → ℕ → List ℕ → Set
  PushSpec σ x r =
    Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (pushC b s stk w ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ s ≡ nil)
      × (get σ′ stk ≡ encL (consNB b x r))
      × (get σ′ w ≡ nil)
      × (∀ y → ¬ (y ≡ s) → ¬ (y ≡ stk) → ¬ (y ≡ w) → get σ′ y ≡ get σ y) )

  push-sound : ∀ σ x r
    → get σ s ≡ atm x → get σ stk ≡ encL r → get σ w ≡ nil → PushSpec σ x r

  -- (a) empty half-tape: the blank disappears, any other symbol is pushed.
  push-sound σ x [] hs hstk hw = go (eqℕ x b) refl
    where
    open Run σ x [] hs hstk hw

    go : ∀ t → eqℕ x b ≡ t → PushSpec σ x []
    go true e =
        set τ5 stk nil , _
      , pre (e-then entry (e-ass refl clear) exit)
      , trans (get-set-≢ τ5 stk s nil stk≢s) g5s
      , trans (get-set-≡ τ5 stk nil) (sym encNil)
      , trans (get-set-≢ τ5 stk w nil stk≢w) g5w
      , (λ y ys ystk yw → trans (get-set-≢ τ5 stk y nil (λ q → ystk (sym q)))
                                (frame5 y ys ystk yw))
      where
      eqTrue : eqV v (atm b ∙ nil) ≡ true
      eqTrue rewrite e = refl
      encNil : encL (consNB b x []) ≡ nil
      encNil rewrite e = refl
      entry : evalT τ5 (eqE (var stk) (cst (atm b ∙ nil))) ≡ just true
      entry = trans (testEq τ5 v (atm b ∙ nil) g5stk) (cong just eqTrue)
      clearV : rupd v (atm b ∙ nil) ≡ just nil
      clearV rewrite eqTrue = refl
      clear : rupd (get τ5 stk) (atm b ∙ nil) ≡ just nil
      clear = subst (λ z → rupd z (atm b ∙ nil) ≡ just nil) (sym g5stk) clearV
      exit : evalT (set τ5 stk nil) (eqE (var stk) (cst nil)) ≡ just true
      exit = testEq (set τ5 stk nil) nil nil (get-set-≡ τ5 stk nil)

    go false e =
        τ5 , _ , pre (e-else entry e-skip exit)
      , g5s , trans g5stk (sym encCons) , g5w , frame5
      where
      eqFalse : eqV v (atm b ∙ nil) ≡ false
      eqFalse rewrite e = refl
      encCons : encL (consNB b x []) ≡ v
      encCons rewrite e = refl
      entry : evalT τ5 (eqE (var stk) (cst (atm b ∙ nil))) ≡ just false
      entry = trans (testEq τ5 v (atm b ∙ nil) g5stk) (cong just eqFalse)
      exit : evalT τ5 (eqE (var stk) (cst nil)) ≡ just false
      exit = testEq τ5 v nil g5stk

  -- (b) non-empty half-tape: always an ordinary push, whatever the symbol.
  push-sound σ x (y ∷ r′) hs hstk hw =
      τ5 , _ , pre (e-else entry e-skip exit)
    , g5s , g5stk , g5w , frame5
    where
    open Run σ x (y ∷ r′) hs hstk hw
    -- STK now holds (x̄ . (ȳ . r̄′)), whose tail is a cons, so it cannot be
    -- (b̄ . nil) no matter what x is: both branches of the test collapse.
    ifF : ∀ (u : Bool) → (if u then false else false) ≡ false
    ifF true  = refl
    ifF false = refl
    eqFalse : eqV v (atm b ∙ nil) ≡ false
    eqFalse = ifF (eqℕ x b)
    entry : evalT τ5 (eqE (var stk) (cst (atm b ∙ nil))) ≡ just false
    entry = trans (testEq τ5 v (atm b ∙ nil) g5stk) (cong just eqFalse)
    exit : evalT τ5 (eqE (var stk) (cst nil)) ≡ just false
    exit = testEq τ5 v nil g5stk

  ------------------------------------------------------------------------
  -- POP, the inverse of PUSH, run FORWARDS.
  --
  -- `popC = inv pushC` normalises to the same six commands in the opposite
  -- order (left-nested, since `inv (c ⨾ d) = inv d ⨾ inv c`), with the
  -- conditional's entry and exit tests exchanged.  Run forwards from
  -- STK = l̄ it delivers S = the head symbol and STK = the tail — where an
  -- EMPTY half-tape pops a BLANK, which is the first clause of movel.
  --
  -- The exit assertion of the normalisation step is `STK =? (b̄ . nil)`, and
  -- in the else-branch it must be FALSE.  That is exactly where NoTrailB is
  -- needed: without it the half-tape [b] would make the assertion true and
  -- the program would be stuck.

  testEqAt : ∀ (τ : Store) (u c : V) → get τ stk ≡ u
           → evalT τ (eqE (var stk) (cst c)) ≡ just (eqV u c)
  testEqAt τ u c h rewrite h = cong just (isTrue-boolV (eqV u c))

  private
    ifFF : ∀ (u : Bool) → (if u then false else false) ≡ false
    ifFF true  = refl
    ifFF false = refl

  -- the five assignments after the normalisation step
  module PopTail (π : Store) (x : ℕ) (l₀ : List ℕ)
                 (pstk : get π stk ≡ atm x ∙ encL l₀)
                 (ps : get π s ≡ nil) (pw : get π w ≡ nil) where
    v : V
    v = atm x ∙ encL l₀

    π1 π2 π3 π4 π5 : Store
    π1 = set π  w   v
    π2 = set π1 stk nil
    π3 = set π2 stk (encL l₀)
    π4 = set π3 s   (atm x)
    π5 = set π4 w   nil

    g1w : get π1 w ≡ v
    g1w = get-set-≡ π w v
    g1stk : get π1 stk ≡ v
    g1stk = trans (get-set-≢ π w stk v w≢stk) pstk
    g2w : get π2 w ≡ v
    g2w = trans (get-set-≢ π1 stk w nil stk≢w) g1w
    g2stk : get π2 stk ≡ nil
    g2stk = get-set-≡ π1 stk nil
    g3w : get π3 w ≡ v
    g3w = trans (get-set-≢ π2 stk w (encL l₀) stk≢w) g2w
    g3stk : get π3 stk ≡ encL l₀
    g3stk = get-set-≡ π2 stk (encL l₀)
    g3s : get π3 s ≡ nil
    g3s = trans (get-set-≢ π2 stk s (encL l₀) stk≢s)
          (trans (get-set-≢ π1 stk s nil stk≢s)
                 (trans (get-set-≢ π w s v w≢s) ps))
    g4w : get π4 w ≡ v
    g4w = trans (get-set-≢ π3 s w (atm x) s≢w) g3w
    g4s : get π4 s ≡ atm x
    g4s = get-set-≡ π3 s (atm x)
    g4stk : get π4 stk ≡ encL l₀
    g4stk = trans (get-set-≢ π3 s stk (atm x) s≢stk) g3stk

    g5s : get π5 s ≡ atm x
    g5s = trans (get-set-≢ π4 w s nil w≢s) g4s
    g5stk : get π5 stk ≡ encL l₀
    g5stk = trans (get-set-≢ π4 w stk nil w≢stk) g4stk
    g5w : get π5 w ≡ nil
    g5w = get-set-≡ π4 w nil

    frameP : ∀ y → ¬ (y ≡ s) → ¬ (y ≡ stk) → ¬ (y ≡ w) → get π5 y ≡ get π y
    frameP y ys ystk yw =
      trans (get-set-≢ π4 w y nil (λ e → yw (sym e)))
      (trans (get-set-≢ π3 s y (atm x) (λ e → ys (sym e)))
      (trans (get-set-≢ π2 stk y (encL l₀) (λ e → ystk (sym e)))
      (trans (get-set-≢ π1 stk y nil (λ e → ystk (sym e)))
             (get-set-≢ π w y v (λ e → yw (sym e))))))

    p5 : (w ^= opd (var stk)) ⊢ π ⇒ π1 ∣ 1
    p5 = e-ass (cong just pstk)
               (subst (λ z → rupd z v ≡ just v) (sym pw) refl)
    p4 : (stk ^= opd (var w)) ⊢ π1 ⇒ π2 ∣ 1
    p4 = e-ass (cong just g1w)
               (subst (λ z → rupd z v ≡ just nil) (sym g1stk) (rupd-self v))
    p3 : (stk ^= tlE (var w)) ⊢ π2 ⇒ π3 ∣ 1
    p3 = e-ass (subst (λ z → tlM z ≡ just (encL l₀)) (sym g2w) refl)
               (subst (λ z → rupd z (encL l₀) ≡ just (encL l₀)) (sym g2stk) refl)
    p2 : (s ^= hdE (var w)) ⊢ π3 ⇒ π4 ∣ 1
    p2 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g3w) refl)
               (subst (λ z → rupd z (atm x) ≡ just (atm x)) (sym g3s) refl)
    p1 : (w ^= cns (var s) (var stk)) ⊢ π4 ⇒ π5 ∣ 1
    p1 = e-ass (cong just (cong₂ _∙_ g4s g4stk))
               (subst (λ z → rupd z v ≡ just nil) (sym g4w) (rupd-self v))

    tail-run : ∀ {ρ k}
             → cond (eqE (var stk) (cst nil))
                    (stk ^= opd (cst (atm b ∙ nil))) skip
                    (eqE (var stk) (cst (atm b ∙ nil))) ⊢ ρ ⇒ π ∣ k
             → popC b s stk w ⊢ ρ ⇒ π5 ∣ suc (suc (suc (suc (suc (k + 1) + 1) + 1) + 1) + 1)
    tail-run dc = e-seq (e-seq (e-seq (e-seq (e-seq dc p5) p4) p3) p2) p1

  wf-pushC : Wf (pushC b s stk w)
  wf-pushC =
    wf-seq (wf-ass (ni-cns (ni-var w≢s) (ni-var w≢stk)))
    (wf-seq (wf-ass (ni-hd  (ni-var s≢w)))
    (wf-seq (wf-ass (ni-tl  (ni-var stk≢w)))
    (wf-seq (wf-ass (ni-opd (ni-var stk≢w)))
    (wf-seq (wf-ass (ni-opd (ni-var w≢stk)))
            (wf-cond (wf-ass (ni-opd ni-cst)) wf-skip)))))

  wf-popC : Wf (popC b s stk w)
  wf-popC = wf-inv (pushC b s stk w) wf-pushC

  PopSpec : Store → List ℕ → Set
  PopSpec σ l =
    Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (popC b s stk w ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ s ≡ atm (popHead b l))
      × (get σ′ stk ≡ encL (popTail l))
      × (get σ′ w ≡ nil)
      × (∀ y → ¬ (y ≡ s) → ¬ (y ≡ stk) → ¬ (y ≡ w) → get σ′ y ≡ get σ y) )

  pop-sound : ∀ σ l → NoTrailB b l
    → get σ s ≡ nil → get σ stk ≡ encL l → get σ w ≡ nil → PopSpec σ l

  -- (a) empty half-tape: the normalisation step RESTORES the blank that PUSH
  --     dropped, and the pop then delivers it.
  pop-sound σ [] nt-[] hs hstk hw =
      π5 , _ , tail-run (e-then entry (e-ass refl setv) exit)
    , g5s , g5stk , g5w
    , (λ y ys ystk yw → trans (frameP y ys ystk yw)
                              (get-set-≢ σ stk y (atm b ∙ nil) (λ e → ystk (sym e))))
    where
    π : Store
    π = set σ stk (atm b ∙ nil)
    open PopTail π b [] (get-set-≡ σ stk (atm b ∙ nil))
                        (trans (get-set-≢ σ stk s (atm b ∙ nil) stk≢s) hs)
                        (trans (get-set-≢ σ stk w (atm b ∙ nil) stk≢w) hw)
    entry : evalT σ (eqE (var stk) (cst nil)) ≡ just true
    entry = testEqAt σ nil nil hstk
    setv : rupd (get σ stk) (atm b ∙ nil) ≡ just (atm b ∙ nil)
    setv = subst (λ z → rupd z (atm b ∙ nil) ≡ just (atm b ∙ nil)) (sym hstk) refl
    exit : evalT π (eqE (var stk) (cst (atm b ∙ nil))) ≡ just true
    exit = trans (testEqAt π (atm b ∙ nil) (atm b ∙ nil) (get-set-≡ σ stk (atm b ∙ nil)))
                 (cong just (eqV-refl (atm b ∙ nil)))

  -- (b) a single symbol: NoTrailB says it is not the blank, which is what
  --     makes the else-branch's exit assertion false.
  pop-sound σ (y ∷ []) (nt-1 y≢b) hs hstk hw =
      π5 , _ , tail-run (e-else entry e-skip exit)
    , g5s , g5stk , g5w , frameP
    where
    open PopTail σ y [] hstk hs hw
    entry : evalT σ (eqE (var stk) (cst nil)) ≡ just false
    entry = testEqAt σ (atm y ∙ nil) nil hstk
    eqF : eqV (atm y ∙ nil) (atm b ∙ nil) ≡ false
    eqF rewrite eqℕ-false y b y≢b = refl
    exit : evalT σ (eqE (var stk) (cst (atm b ∙ nil))) ≡ just false
    exit = trans (testEqAt σ (atm y ∙ nil) (atm b ∙ nil) hstk) (cong just eqF)

  -- (c) two or more symbols: the tail is a cons, so the assertion is false
  --     whatever the head symbol is.
  pop-sound σ (y ∷ z ∷ l1) (nt-∷ nt) hs hstk hw =
      π5 , _ , tail-run (e-else entry e-skip exit)
    , g5s , g5stk , g5w , frameP
    where
    open PopTail σ y (z ∷ l1) hstk hs hw
    entry : evalT σ (eqE (var stk) (cst nil)) ≡ just false
    entry = testEqAt σ (atm y ∙ (atm z ∙ encL l1)) nil hstk
    eqF : eqV (atm y ∙ (atm z ∙ encL l1)) (atm b ∙ nil) ≡ false
    eqF = ifFF (eqℕ y b)
    exit : evalT σ (eqE (var stk) (cst (atm b ∙ nil))) ≡ just false
    exit = trans (testEqAt σ (atm y ∙ (atm z ∙ encL l1)) (atm b ∙ nil) hstk)
                 (cong just eqF)

------------------------------------------------------------------------
-- 7.  MOVEL and MOVER (Fig. 2c).
--
--     MOVEL((L S R)) ≡ PUSH(S,R) ; POP(S,L)
--     MOVER         ≡ I⟦MOVEL⟧

movelC : ℕ → Cmd
movelC b = unpackT ⨾ pushC b vS vR vW ⨾ popC b vS vL vW ⨾ packT

moverC : ℕ → Cmd
moverC b = inv (movelC b)

-- MOVER is the MIRROR of MOVEL: pushing the symbol under the head onto the
-- LEFT half-tape and popping from the RIGHT.  This holds definitionally —
-- `inv` turns `PUSH(S,R) ; POP(S,L)` into `PUSH(S,L) ; POP(S,R)` because POP
-- is `inv PUSH` and `inv` is involutive on these concrete terms.
moverC-mirror : ∀ b → moverC b
              ≡ (((unpackT ⨾ pushC b vS vL vW) ⨾ popC b vS vR vW) ⨾ packT)
moverC-mirror b = refl

------------------------------------------------------------------------
-- 7b.  MOVEL IS CORRECT: it computes the letter's `movel`.
--
--   MOVEL((L S R)) ≡ PUSH(S,R) ; POP(S,L)
--
-- and `movel b (l,x,r) = (popTail l , popHead b l , consNB b x r)`
-- (movel-pop-push), so the two stack operations are exactly the two halves
-- of one head move.  The left half-tape must have no trailing blank; that is
-- what POP needs.

movel-sound : ∀ b σ l x r
  → NoTrailB b l
  → get σ vT ≡ encT (l , x , r) → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (movelC b ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vT ≡ encT (movel b (l , x , r)))
      × Scratch-nil σ′
      × (∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR)
             → ¬ (y ≡ vTmp) → ¬ (y ≡ vW) → get σ′ y ≡ get σ y) )
movel-sound b σ l x r ntl hT (hL , hS , hR , hTmp , hW)
  with unpack-sound σ l x r hT hL hS hR hTmp
... | σ₁ , _ , dU , g1L , g1S , g1R , g1T , g1Tmp , f1
  with Push.push-sound b vS vR vW (λ ()) (λ ()) (λ ())
         σ₁ x r g1S g1R (trans (f1 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hW)
... | σ₂ , _ , dPush , p2S , p2R , p2W , f2
  with Push.pop-sound b vS vL vW (λ ()) (λ ()) (λ ())
         σ₂ l ntl p2S (trans (f2 vL (λ ()) (λ ()) (λ ())) g1L) p2W
... | σ₃ , _ , dPop , p3S , p3L , p3W , f3
  with pack-sound σ₃ (popTail l) (popHead b l) (consNB b x r)
         p3L p3S
         (trans (f3 vR (λ ()) (λ ()) (λ ())) p2R)
         (trans (f3 vT (λ ()) (λ ()) (λ ()))
                (trans (f2 vT (λ ()) (λ ()) (λ ())) g1T))
         (trans (f3 vTmp (λ ()) (λ ()) (λ ()))
                (trans (f2 vTmp (λ ()) (λ ()) (λ ())) g1Tmp))
... | σ₄ , _ , dPack , g4T , g4L , g4S , g4R , g4Tmp , f4 =
    σ₄ , _
  , e-seq dU (e-seq dPush (e-seq dPop dPack))
  , subst (λ z → get σ₄ vT ≡ encT z) (sym (movel-pop-push b l x r)) g4T
  , (g4L , g4S , g4R , g4Tmp
    , trans (f4 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) p3W)
  , (λ y yT yL yS yR yTmp yW →
        trans (f4 y yT yL yS yR yTmp)
        (trans (f3 y yS yL yW)
        (trans (f2 y yS yR yW) (f1 y yT yL yS yR yTmp))))

-- Well-formedness of the head-move macros and, below, of every translated
-- rule: the construction never breaks R-WHILE's linearity condition.
wf-movelC : ∀ b → Wf (movelC b)
wf-movelC b =
  wf-seq wf-unpackT
  (wf-seq (Push.wf-pushC b vS vR vW (λ ()) (λ ()) (λ ()))
  (wf-seq (Push.wf-popC  b vS vL vW (λ ()) (λ ()) (λ ())) wf-packT))

wf-moverC : ∀ b → Wf (moverC b)
wf-moverC b = wf-inv (movelC b) (wf-movelC b)

-- MOVER IS CORRECT: it computes `mover`, the mirror of `movel`.  The
-- half-tape it pops from is the RIGHT one, so that is where NoTrailB is
-- needed this time.
mover-sound : ∀ b σ l x r
  → NoTrailB b r
  → get σ vT ≡ encT (l , x , r) → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (moverC b ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vT ≡ encT (mover b (l , x , r)))
      × Scratch-nil σ′
      × (∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR)
             → ¬ (y ≡ vTmp) → ¬ (y ≡ vW) → get σ′ y ≡ get σ y) )
mover-sound b σ l x r ntr hT (hL , hS , hR , hTmp , hW)
  with unpack-sound σ l x r hT hL hS hR hTmp
... | σ₁ , _ , dU , g1L , g1S , g1R , g1T , g1Tmp , f1
  with Push.push-sound b vS vL vW (λ ()) (λ ()) (λ ())
         σ₁ x l g1S g1L (trans (f1 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hW)
... | σ₂ , _ , dPush , p2S , p2L , p2W , f2
  with Push.pop-sound b vS vR vW (λ ()) (λ ()) (λ ())
         σ₂ r ntr p2S (trans (f2 vR (λ ()) (λ ()) (λ ())) g1R) p2W
... | σ₃ , _ , dPop , p3S , p3R , p3W , f3
  with pack-sound σ₃ (consNB b x l) (popHead b r) (popTail r)
         (trans (f3 vL (λ ()) (λ ()) (λ ())) p2L) p3S p3R
         (trans (f3 vT (λ ()) (λ ()) (λ ()))
                (trans (f2 vT (λ ()) (λ ()) (λ ())) g1T))
         (trans (f3 vTmp (λ ()) (λ ()) (λ ()))
                (trans (f2 vTmp (λ ()) (λ ()) (λ ())) g1Tmp))
... | σ₄ , _ , dPack , g4T , g4L , g4S , g4R , g4Tmp , f4 =
    σ₄ , _
  , e-seq (e-seq (e-seq dU dPush) dPop) dPack
  , g4T
  , (g4L , g4S , g4R , g4Tmp
    , trans (f4 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) p3W)
  , (λ y yT yL yS yR yTmp yW →
        trans (f4 y yT yL yS yR yTmp)
        (trans (f3 y yS yR yW)
        (trans (f2 y yS yL yW) (f1 y yT yL yS yR yTmp))))

------------------------------------------------------------------------
-- 7c.  THE HEAD MOVES ON AN UNPACKED TAPE.
--
-- From here on the tape is kept UNPACKED, in L, S and R, for the whole run
-- of the main loop.  The letter keeps it packed in T and dispatches by
-- matching patterns over the PAIR (Q,T); the core has neither pattern
-- matching nor a conjunction in its tests, and `Exp` carries one operator
-- over variable-or-constant operands, so `Q = q̄ ∧ hd (tl T) = s̄` is not one
-- test.  Keeping the tape unpacked makes the symbol under the head a
-- variable, and the pair (Q,S) is then held in a key variable K, so the
-- guard becomes ONE equality against a CONSTANT PAIR.  Same information,
-- expressible in the core.
--
-- With the tape unpacked, a head move is just the two stack operations of
-- Fig. 2c, with no packing around them.

moveLC : ℕ → Cmd
moveLC b = pushC b vS vR vW ⨾ popC b vS vL vW

moveRC : ℕ → Cmd
moveRC b = pushC b vS vL vW ⨾ popC b vS vR vW

-- and the right move is still literally the inverse of the left one
moveRC-inv : ∀ b → moveRC b ≡ inv (moveLC b)
moveRC-inv b = refl

wf-moveLC : ∀ b → Wf (moveLC b)
wf-moveLC b = wf-seq (Push.wf-pushC b vS vR vW (λ ()) (λ ()) (λ ()))
                     (Push.wf-popC  b vS vL vW (λ ()) (λ ()) (λ ()))
wf-moveRC : ∀ b → Wf (moveRC b)
wf-moveRC b = wf-seq (Push.wf-pushC b vS vL vW (λ ()) (λ ()) (λ ()))
                     (Push.wf-popC  b vS vR vW (λ ()) (λ ()) (λ ()))

moveL-sound : ∀ b σ l x r
  → NoTrailB b l
  → get σ vS ≡ atm x → get σ vL ≡ encL l → get σ vR ≡ encL r → get σ vW ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (moveLC b ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vS ≡ atm (popHead b l))
      × (get σ′ vL ≡ encL (popTail l))
      × (get σ′ vR ≡ encL (consNB b x r))
      × (get σ′ vW ≡ nil)
      × (∀ y → ¬ (y ≡ vS) → ¬ (y ≡ vL) → ¬ (y ≡ vR) → ¬ (y ≡ vW)
             → get σ′ y ≡ get σ y) )
moveL-sound b σ l x r ntl hS hL hR hW
  with Push.push-sound b vS vR vW (λ ()) (λ ()) (λ ()) σ x r hS hR hW
... | σ₁ , _ , dPush , p1S , p1R , p1W , f1
  with Push.pop-sound b vS vL vW (λ ()) (λ ()) (λ ())
         σ₁ l ntl p1S (trans (f1 vL (λ ()) (λ ()) (λ ())) hL) p1W
... | σ₂ , _ , dPop , p2S , p2L , p2W , f2 =
    σ₂ , _ , e-seq dPush dPop
  , p2S , p2L , trans (f2 vR (λ ()) (λ ()) (λ ())) p1R , p2W
  , (λ y yS yL yR yW → trans (f2 y yS yL yW) (f1 y yS yR yW))

moveR-sound : ∀ b σ l x r
  → NoTrailB b r
  → get σ vS ≡ atm x → get σ vL ≡ encL l → get σ vR ≡ encL r → get σ vW ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (moveRC b ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vS ≡ atm (popHead b r))
      × (get σ′ vR ≡ encL (popTail r))
      × (get σ′ vL ≡ encL (consNB b x l))
      × (get σ′ vW ≡ nil)
      × (∀ y → ¬ (y ≡ vS) → ¬ (y ≡ vL) → ¬ (y ≡ vR) → ¬ (y ≡ vW)
             → get σ′ y ≡ get σ y) )
moveR-sound b σ l x r ntr hS hL hR hW
  with Push.push-sound b vS vL vW (λ ()) (λ ()) (λ ()) σ x l hS hL hW
... | σ₁ , _ , dPush , p1S , p1L , p1W , f1
  with Push.pop-sound b vS vR vW (λ ()) (λ ()) (λ ())
         σ₁ r ntr p1S (trans (f1 vR (λ ()) (λ ()) (λ ())) hR) p1W
... | σ₂ , _ , dPop , p2S , p2R , p2W , f2 =
    σ₂ , _ , e-seq dPush dPop
  , p2S , p2R , trans (f2 vL (λ ()) (λ ()) (λ ())) p1L , p2W
  , (λ y yS yL yR yW → trans (f2 y yS yR yW) (f1 y yS yL yW))
