{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- R-WHILE IS r-TURING COMPLETE — the machine-checked version of
--
--   青木利晃・横山哲郎, 「可逆プログラミング言語 R-WHILE の可逆チューリング
--   完全性」, 電子情報通信学会論文誌 D, J101-D(9), pp.1372-1375, 2018.
--
-- That letter builds, for every reversible Turing machine T, an R-WHILE
-- program T̲ with ⟦T⟧^TM r = r′ ⟹ ⟦T̲⟧ r̄ = r̄′ (its Theorem 2), via a
-- rule-by-rule simulation (its Lemma 1).  This module carries the
-- construction out inside Agda, on top of the already verified R-WHILE
-- semantics of `RWhileTime`.
--
-- WHY `RWhileTime` AND NOT `RWhileRevFull`.  The abstract core
-- `RWhileRevFull.Core` takes atomic commands to be arbitrary RELATIONS on
-- stores.  Simulating a Turing machine there would be vacuous: one could
-- put the machine's whole step relation into a single atom.  `RWhileTime`
-- is a first-order deep embedding — `Cmd` is skip / `^=` / `⨾` / if-fi /
-- from-until and `Exp` is a flat expression grammar over variables and
-- constants, with no function space anywhere — so a program built here is
-- a genuine piece of R-WHILE text and the theorem has content.
--
-- WHAT REPLACES THE PAPER'S `rewrite` MACRO.  Fig. 2 of the letter writes
-- PUSH, POP and STEP with R-WHILE's pattern replacement `q <= r` and its
-- `rewrite … by …` multi-way case.  `RWhileTime` has neither: its commands
-- are the five reversible core constructs, and its expressions carry ONE
-- operator with variable-or-constant operands, so a guard like
-- `S = b̄ ∧ STK = nil` is not expressible as one test.  Both are recovered
-- without leaving the core:
--
--   * `q <= r` for a linear pattern is the local/delocal idiom — build the
--     value with `^=`, then clear the source with a `^=` that names it
--     (`rupd` case 2).  See `unpack3` / `pack3`, which are inverse.
--   * a conjunctive guard becomes ONE equality against a CONSTANT VALUE,
--     because `Opd` has `cst : V → Opd`.  `pushC` tests
--     `STK =? (b̄ . nil)`; `stepC` will test the dispatch key `(Q . S)`
--     against `(q̄ . s̄)`.
--
-- STATUS.  LEMMA 1 OF THE LETTER IS PROVED (`lemma1`), for all four rule
-- shapes of Fig. 3.  So is everything it rests on: the two halves of the
-- pattern replacement (`unpack-sound`, `pack-sound`), PUSH and POP
-- (`push-sound`, `pop-sound`), the two head moves (`movel-sound`,
-- `mover-sound`), and the fact that the translation only ever emits legal
-- R-WHILE (`wf-ruleC` — R-WHILE's linearity side condition).
--
-- What remains is the multi-way dispatch `stepC`, which selects the branch
-- for the applicable rule (its entry guards are mutually exclusive by local
-- forward determinism, its exit assertions by local backward determinism),
-- and the induction over the main loop that turns Lemma 1 into Theorem 2.
-- r-Turing completeness is therefore still a `Set` here, not a theorem.
--
-- No postulates, no holes — an unproved statement appears as a `Set`, never
-- as an assumed inhabitant.
------------------------------------------------------------------------

module RWhileRTM where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
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

------------------------------------------------------------------------
-- 1.  Reversible Turing machines (§2 of the letter).
--
-- States and tape symbols are ℕ.  A machine's rules are TRIPLES, as in the
-- letter: either a symbol rewrite (q,(s,s'),q') or a head move (q,a,q').

data Move : Set where
  mvL : Move          -- ←
  mvS : Move          -- ↓
  mvR : Move          -- →

data Rule : Set where
  rsym : ℕ → ℕ → ℕ → ℕ → Rule      -- (q , (s , s') , q')
  rmov : ℕ → Move → ℕ → Rule       -- (q , a , q')

src : Rule → ℕ
src (rsym q _ _ _) = q
src (rmov q _ _)   = q

tgt : Rule → ℕ
tgt (rsym _ _ _ q') = q'
tgt (rmov _ _ q')   = q'

record RTM : Set where
  field
    rules : List Rule
    blank : ℕ            -- b
    q-s   : ℕ            -- initial state
    q-f   : ℕ            -- final state

open RTM public

------------------------------------------------------------------------
-- Configurations.  A tape is (l , s , r): the symbol s under the head, the
-- half-tapes l (nearest symbol FIRST) and r.  Both are blank-free, which is
-- what `consNB` maintains.

Tape : Set
Tape = List ℕ × ℕ × List ℕ

Conf : Set
Conf = ℕ × Tape

-- push s onto the half-tape r, dropping it if it is a blank at the very end.
-- This is the third clause of the letter's `movel`, which is what keeps the
-- representation canonical.
consNB : ℕ → ℕ → List ℕ → List ℕ
consNB b s []      = if eqℕ s b then [] else s ∷ []
consNB b s (x ∷ r) = s ∷ x ∷ r

-- movel, all three clauses of the letter at once.
movel : ℕ → Tape → Tape
movel b ([]     , s , r) = []  , b  , consNB b s r
movel b (s' ∷ l , s , r) = l   , s' , consNB b s r

-- Reading movel as "pop from l, push onto r" — which is exactly Fig. 2c,
-- `MOVEL((L S R)) ≡ PUSH(S,R) ; POP(S,L)`.  An empty left half-tape pops a
-- blank, which is the first clause of movel.
popHead : ℕ → List ℕ → ℕ
popHead b []      = b
popHead b (y ∷ _) = y

popTail : List ℕ → List ℕ
popTail []       = []
popTail (_ ∷ l0) = l0

movel-pop-push : ∀ b l x r
               → movel b (l , x , r) ≡ (popTail l , popHead b l , consNB b x r)
movel-pop-push b []      x r = refl
movel-pop-push b (y ∷ l) x r = refl

-- The mirror function, which is what MOVER computes on tapes.
mover : ℕ → Tape → Tape
mover b (l , x , r) = consNB b x l , popHead b r , popTail r

tri : ∀ {l l′ : List ℕ} {x x′ : ℕ} {r r′ : List ℕ}
    → l ≡ l′ → x ≡ x′ → r ≡ r′ → (l , x , r) ≡ (l′ , x′ , r′)
tri refl refl refl = refl

------------------------------------------------------------------------
-- The canonicity invariant on half-tapes: NO TRAILING BLANK.
--
-- The letter writes configurations in Q × ((Σ∖{b})* × Σ × (Σ∖{b})*).  What
-- the construction actually needs — and what movel actually preserves — is
-- weaker: a half-tape must not END in a blank.  (Blank-freeness everywhere
-- is NOT preserved: moving left over a blank under the head pushes that
-- blank onto a non-empty right half-tape, which is a legitimate tape.)
--
-- The invariant is what makes POP's exit assertion hold: `encL l` can only
-- be (b̄ . nil) when l is the single blank, which this rules out.

data NoTrailB (b : ℕ) : List ℕ → Set where
  nt-[] : NoTrailB b []
  nt-1  : ∀ {x} → ¬ (x ≡ b) → NoTrailB b (x ∷ [])
  nt-∷  : ∀ {x y l} → NoTrailB b (y ∷ l) → NoTrailB b (x ∷ y ∷ l)

tf→⊥ : true ≡ false → ⊥
tf→⊥ ()

eqℕ-false : ∀ m n → ¬ (m ≡ n) → eqℕ m n ≡ false
eqℕ-false zero    zero    ne = ⊥-elim (ne refl)
eqℕ-false zero    (suc n) ne = refl
eqℕ-false (suc m) zero    ne = refl
eqℕ-false (suc m) (suc n) ne = eqℕ-false m n (λ e → ne (cong suc e))

eqℕ-false-inv : ∀ {m n} → eqℕ m n ≡ false → ¬ (m ≡ n)
eqℕ-false-inv {m} {n} e q =
  tf→⊥ (trans (sym (subst (λ z → eqℕ z n ≡ true) (sym q) (eqℕ-refl n))) e)

-- consNB preserves it: pushing onto a non-empty half-tape keeps the old
-- last symbol, and pushing onto the empty one either drops the blank or
-- leaves a single non-blank symbol.
consNB-nt : ∀ b x l → NoTrailB b l → NoTrailB b (consNB b x l)
consNB-nt b x (y ∷ l) nt = nt-∷ nt
consNB-nt b x []      nt = go (eqℕ x b) refl
  where
  go : ∀ u → eqℕ x b ≡ u → NoTrailB b (consNB b x [])
  go true  e rewrite e = nt-[]
  go false e rewrite e = nt-1 (eqℕ-false-inv e)

eqℕ-true-inv : ∀ m n → eqℕ m n ≡ true → m ≡ n
eqℕ-true-inv zero    zero    e = refl
eqℕ-true-inv zero    (suc n) ()
eqℕ-true-inv (suc m) zero    ()
eqℕ-true-inv (suc m) (suc n) e = cong suc (eqℕ-true-inv m n e)

-- popping then pushing back is the identity — this is where NoTrailB pays
-- off: without it the half-tape [b] would come back as [].
consNB-pop : ∀ b l → NoTrailB b l → consNB b (popHead b l) (popTail l) ≡ l
consNB-pop b []            nt-[]      rewrite eqℕ-refl b          = refl
consNB-pop b (y ∷ [])      (nt-1 y≢b) rewrite eqℕ-false y b y≢b   = refl
consNB-pop b (y ∷ z ∷ l1)  (nt-∷ nt)                              = refl

-- pushing then popping back is the identity, unconditionally
pop-consNB-head : ∀ b x r → popHead b (consNB b x r) ≡ x
pop-consNB-head b x []      = go (eqℕ x b) refl
  where
  go : ∀ u → eqℕ x b ≡ u → popHead b (consNB b x []) ≡ x
  go true  e rewrite e = sym (eqℕ-true-inv x b e)
  go false e rewrite e = refl
pop-consNB-head b x (y ∷ r0) = refl

pop-consNB-tail : ∀ b x r → popTail (consNB b x r) ≡ r
pop-consNB-tail b x []      = go (eqℕ x b) refl
  where
  go : ∀ u → eqℕ x b ≡ u → popTail (consNB b x []) ≡ []
  go true  e rewrite e = refl
  go false e rewrite e = refl
pop-consNB-tail b x (y ∷ r0) = refl

-- movel and mover are mutually inverse on canonical tapes.  The second is
-- what the letter's → clause needs: `Step` defines a right move by the
-- CONVERSE of movel, and mover-movel says the tape MOVER produces is the
-- unique one movel sends back.
movel-mover : ∀ b l x r → NoTrailB b r → movel b (mover b (l , x , r)) ≡ (l , x , r)
movel-mover b l x r ntr =
  trans (movel-pop-push b (consNB b x l) (popHead b r) (popTail r))
        (tri (pop-consNB-tail b x l) (pop-consNB-head b x l) (consNB-pop b r ntr))

mover-movel : ∀ b l x r → NoTrailB b l → mover b (movel b (l , x , r)) ≡ (l , x , r)
mover-movel b l x r ntl =
  trans (cong (mover b) (movel-pop-push b l x r))
        (tri (consNB-pop b l ntl) (pop-consNB-head b x r) (pop-consNB-tail b x r))

-- popping preserves it too (a suffix of a list with no trailing blank has
-- none either)
popTail-nt : ∀ b l → NoTrailB b l → NoTrailB b (popTail l)
popTail-nt b []           nt        = nt-[]
popTail-nt b (x ∷ [])     (nt-1 _)  = nt-[]
popTail-nt b (x ∷ y ∷ l)  (nt-∷ nt) = nt

-- Both half-tapes are canonical.  Required on the configuration BEFORE and
-- AFTER the step: a right move is stated by the converse of movel, so the
-- successor's left half-tape is not determined by the predecessor's.
TapeOK : ℕ → Tape → Set
TapeOK b (l , x , r) = NoTrailB b l × NoTrailB b r


-- One computation step (Fig. 1 of the letter).  Note that the → case is
-- given by the CONVERSE of movel, exactly as in the letter — that is what
-- makes ← and → each other's inverse.
data Step (M : RTM) : Conf → Conf → Set where
  st-sym : ∀ {q s s' q' l r}
         → rsym q s s' q' ∈ rules M
         → Step M (q , (l , s , r)) (q' , (l , s' , r))
  st-lft : ∀ {q q' t}
         → rmov q mvL q' ∈ rules M
         → Step M (q , t) (q' , movel (blank M) t)
  st-sty : ∀ {q q' t}
         → rmov q mvS q' ∈ rules M
         → Step M (q , t) (q' , t)
  st-rgt : ∀ {q q' t t'}
         → rmov q mvR q' ∈ rules M
         → movel (blank M) t' ≡ t
         → Step M (q , t) (q' , t')

data Step* (M : RTM) : Conf → Conf → Set where
  done : ∀ {c} → Step* M c c
  more : ∀ {c c₁ c₂} → Step M c c₁ → Step* M c₁ c₂ → Step* M c c₂

data StepBy (b : ℕ) : Rule → Conf → Conf → Set where
  sb-sym : ∀ {q s s′ q′ l r}
         → StepBy b (rsym q s s′ q′) (q , (l , s , r)) (q′ , (l , s′ , r))
  sb-lft : ∀ {q q′ l x r}
         → StepBy b (rmov q mvL q′) (q , (l , x , r)) (q′ , movel b (l , x , r))
  sb-sty : ∀ {q q′ l x r}
         → StepBy b (rmov q mvS q′) (q , (l , x , r)) (q′ , (l , x , r))
  sb-rgt : ∀ {q q′ l x r l′ x′ r′}
         → movel b (l′ , x′ , r′) ≡ (l , x , r)
         → StepBy b (rmov q mvR q′) (q , (l , x , r)) (q′ , (l′ , x′ , r′))

step-splits : ∀ {M c c′} → Step M c c′
            → Σ[ d ∈ Rule ] ((d ∈ rules M) × StepBy (blank M) d c c′)
step-splits (st-sym mem)   = _ , mem , sb-sym
step-splits (st-lft mem)   = _ , mem , sb-lft
step-splits (st-sty mem)   = _ , mem , sb-sty
step-splits (st-rgt mem e) = _ , mem , sb-rgt e


------------------------------------------------------------------------
-- 2.  The reversibility conditions (§2.2 of the letter).
--
-- Local forward determinism: two DISTINCT rules leaving the same state must
-- both be symbol rules, and must read different symbols.  (So a state has
-- either one move rule or a set of symbol rules with distinct inputs — this
-- is precisely what lets `stepC` dispatch with mutually exclusive guards.)

LFD : RTM → Set
LFD M = ∀ d₁ d₂ → d₁ ∈ rules M → d₂ ∈ rules M → ¬ (d₁ ≡ d₂) → src d₁ ≡ src d₂
      → Σ[ q ∈ ℕ ] Σ[ s₁ ∈ ℕ ] Σ[ t₁ ∈ ℕ ] Σ[ p₁ ∈ ℕ ]
        Σ[ s₂ ∈ ℕ ] Σ[ t₂ ∈ ℕ ] Σ[ p₂ ∈ ℕ ]
        ( (d₁ ≡ rsym q s₁ t₁ p₁) × (d₂ ≡ rsym q s₂ t₂ p₂) × ¬ (s₁ ≡ s₂) )

-- Local backward determinism: the mirror image, on the WRITTEN symbol.
-- This is what makes the exit assertions of `stepC` mutually exclusive.
LBD : RTM → Set
LBD M = ∀ d₁ d₂ → d₁ ∈ rules M → d₂ ∈ rules M → ¬ (d₁ ≡ d₂) → tgt d₁ ≡ tgt d₂
      → Σ[ q ∈ ℕ ] Σ[ s₁ ∈ ℕ ] Σ[ t₁ ∈ ℕ ] Σ[ p₁ ∈ ℕ ]
        Σ[ s₂ ∈ ℕ ] Σ[ t₂ ∈ ℕ ] Σ[ p₂ ∈ ℕ ]
        ( (d₁ ≡ rsym p₁ s₁ t₁ q) × (d₂ ≡ rsym p₂ s₂ t₂ q) × ¬ (t₁ ≡ t₂) )

NoFromFinal : RTM → Set
NoFromFinal M = ∀ d → d ∈ rules M → ¬ (src d ≡ q-f M)

NoIntoStart : RTM → Set
NoIntoStart M = ∀ d → d ∈ rules M → ¬ (tgt d ≡ q-s M)

-- An RTM is a machine satisfying all four.
record IsRTM (M : RTM) : Set where
  field
    lfd : LFD M
    lbd : LBD M
    nff : NoFromFinal M
    nis : NoIntoStart M

------------------------------------------------------------------------
-- 3.  The encoding  x ↦ x̄  (§4 of the letter).
--
-- Symbols and states become atoms; half-tapes become cons lists; the tape
-- triple (l,s,r) becomes (l̄ . (s̄ . r̄)), which is the letter's `(L S R)`.

encL : List ℕ → V
encL []      = nil
encL (x ∷ l) = atm x ∙ encL l

encT : Tape → V
encT (l , s , r) = encL l ∙ (atm s ∙ encL r)

------------------------------------------------------------------------
-- 4.  Variables of the generated program.

vQ vT vL vS vR vTmp vW vIn vOut vK : ℕ
vQ   = 0        -- current state
vT   = 1        -- the tape triple
vL   = 2        -- scratch: left half-tape
vS   = 3        -- scratch: symbol under the head
vR   = 4        -- scratch: right half-tape
vTmp = 5        -- scratch: the suffix (s̄ . r̄), used while splitting T
vW   = 6        -- scratch: PUSH/POP's working cell
vIn  = 7        -- the program's input  R
vOut = 8        -- the program's output R'
vK   = 9        -- the dispatch key (Q . S), maintained by the loop

------------------------------------------------------------------------
-- 4b.  What it means for a store to hold a configuration.

HoldsConf : Conf → Store → Set
HoldsConf (q , t) σ = (get σ vQ ≡ atm q) × (get σ vT ≡ encT t)

Scratch-nil : Store → Set
Scratch-nil σ = (get σ vL ≡ nil) × (get σ vS ≡ nil) × (get σ vR ≡ nil)
              × (get σ vTmp ≡ nil) × (get σ vW ≡ nil)


------------------------------------------------------------------------
-- 5.  `q <= r` for the tape triple, as the local/delocal idiom.
--
--   unpack3 :  (L . (S . R)) <= T
--   pack3   :  T <= (L . (S . R))
--
-- Each `^=` either SETS a nil variable (rupd case 1) or CLEARS a variable
-- that already holds exactly the named value (rupd case 2); nothing else is
-- needed, and the two commands are each other's inverse.

-- `hd (tl T)` is not a single flat expression, so the split goes through the
-- intermediate Tmp = (s̄ . r̄) — which is also how a compiler would flatten it.
-- Each line is a `^=` that either SETS a nil variable or CLEARS a variable
-- holding exactly the value named on the right; T is cleared while Tmp still
-- holds its tail, and Tmp is cleared last.
unpackT : Cmd
unpackT =   vL   ^= hdE (var vT)               -- L   := hd T           = l̄
          ⨾ vTmp ^= tlE (var vT)               -- Tmp := tl T           = (s̄ . r̄)
          ⨾ vT   ^= cns (var vL) (var vTmp)    -- T holds (L . Tmp)     → clear T
          ⨾ vS   ^= hdE (var vTmp)             -- S   := hd Tmp         = s̄
          ⨾ vR   ^= tlE (var vTmp)             -- R   := tl Tmp         = r̄
          ⨾ vTmp ^= cns (var vS) (var vR)      -- Tmp holds (S . R)     → clear Tmp

packT : Cmd
packT = inv unpackT

------------------------------------------------------------------------
-- 5b.  unpackT AND packT ARE CORRECT.
--
-- These are the two halves of the letter's `(L S R) <= T` and `T <= (L S R)`.
-- Each is six assignments; each assignment either SETS a nil variable or
-- CLEARS one holding exactly the value named on the right, and in none of
-- them does the target occur in the expression.  The variables are concrete
-- numerals, so every distinctness side condition closes by `λ ()`.

unpack-sound : ∀ σ l x r
  → get σ vT ≡ encT (l , x , r)
  → get σ vL ≡ nil → get σ vS ≡ nil → get σ vR ≡ nil → get σ vTmp ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (unpackT ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vL ≡ encL l) × (get σ′ vS ≡ atm x) × (get σ′ vR ≡ encL r)
      × (get σ′ vT ≡ nil) × (get σ′ vTmp ≡ nil)
      × (∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
             → get σ′ y ≡ get σ y) )
unpack-sound σ l x r hT hL hS hR hTmp =
    υ6 , _
  , e-seq d1 (e-seq d2 (e-seq d3 (e-seq d4 (e-seq d5 d6))))
  , g6L , g6S , g6R , g6T , get-set-≡ υ5 vTmp nil , frame
  where
  A B : V
  A = encL l
  B = atm x ∙ encL r

  υ1 υ2 υ3 υ4 υ5 υ6 : Store
  υ1 = set σ  vL   A
  υ2 = set υ1 vTmp B
  υ3 = set υ2 vT   nil
  υ4 = set υ3 vS   (atm x)
  υ5 = set υ4 vR   (encL r)
  υ6 = set υ5 vTmp nil

  g1T : get υ1 vT ≡ A ∙ B
  g1T = trans (get-set-≢ σ vL vT A (λ ())) hT
  g1Tmp : get υ1 vTmp ≡ nil
  g1Tmp = trans (get-set-≢ σ vL vTmp A (λ ())) hTmp
  g1L : get υ1 vL ≡ A
  g1L = get-set-≡ σ vL A

  g2T : get υ2 vT ≡ A ∙ B
  g2T = trans (get-set-≢ υ1 vTmp vT B (λ ())) g1T
  g2L : get υ2 vL ≡ A
  g2L = trans (get-set-≢ υ1 vTmp vL B (λ ())) g1L
  g2Tmp : get υ2 vTmp ≡ B
  g2Tmp = get-set-≡ υ1 vTmp B

  g3Tmp : get υ3 vTmp ≡ B
  g3Tmp = trans (get-set-≢ υ2 vT vTmp nil (λ ())) g2Tmp
  g3S : get υ3 vS ≡ nil
  g3S = trans (get-set-≢ υ2 vT vS nil (λ ()))
        (trans (get-set-≢ υ1 vTmp vS B (λ ()))
               (trans (get-set-≢ σ vL vS A (λ ())) hS))
  g3L : get υ3 vL ≡ A
  g3L = trans (get-set-≢ υ2 vT vL nil (λ ())) g2L

  g4Tmp : get υ4 vTmp ≡ B
  g4Tmp = trans (get-set-≢ υ3 vS vTmp (atm x) (λ ())) g3Tmp
  g4R : get υ4 vR ≡ nil
  g4R = trans (get-set-≢ υ3 vS vR (atm x) (λ ()))
        (trans (get-set-≢ υ2 vT vR nil (λ ()))
        (trans (get-set-≢ υ1 vTmp vR B (λ ()))
               (trans (get-set-≢ σ vL vR A (λ ())) hR)))

  g5Tmp : get υ5 vTmp ≡ B
  g5Tmp = trans (get-set-≢ υ4 vR vTmp (encL r) (λ ())) g4Tmp
  g5S : get υ5 vS ≡ atm x
  g5S = trans (get-set-≢ υ4 vR vS (encL r) (λ ())) (get-set-≡ υ3 vS (atm x))
  g5R : get υ5 vR ≡ encL r
  g5R = get-set-≡ υ4 vR (encL r)

  g6L : get υ6 vL ≡ A
  g6L = trans (get-set-≢ υ5 vTmp vL nil (λ ()))
        (trans (get-set-≢ υ4 vR vL (encL r) (λ ()))
               (trans (get-set-≢ υ3 vS vL (atm x) (λ ())) g3L))
  g6S : get υ6 vS ≡ atm x
  g6S = trans (get-set-≢ υ5 vTmp vS nil (λ ())) g5S
  g6R : get υ6 vR ≡ encL r
  g6R = trans (get-set-≢ υ5 vTmp vR nil (λ ())) g5R
  g6T : get υ6 vT ≡ nil
  g6T = trans (get-set-≢ υ5 vTmp vT nil (λ ()))
        (trans (get-set-≢ υ4 vR vT (encL r) (λ ()))
        (trans (get-set-≢ υ3 vS vT (atm x) (λ ())) (get-set-≡ υ2 vT nil)))

  frame : ∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
        → get υ6 y ≡ get σ y
  frame y yT yL yS yR yTmp =
    trans (get-set-≢ υ5 vTmp y nil (λ e → yTmp (sym e)))
    (trans (get-set-≢ υ4 vR y (encL r) (λ e → yR (sym e)))
    (trans (get-set-≢ υ3 vS y (atm x) (λ e → yS (sym e)))
    (trans (get-set-≢ υ2 vT y nil (λ e → yT (sym e)))
    (trans (get-set-≢ υ1 vTmp y B (λ e → yTmp (sym e)))
           (get-set-≢ σ vL y A (λ e → yL (sym e)))))))

  d1 : (vL ^= hdE (var vT)) ⊢ σ ⇒ υ1 ∣ 1
  d1 = e-ass (subst (λ z → hdM z ≡ just A) (sym hT) refl)
             (subst (λ z → rupd z A ≡ just A) (sym hL) refl)
  d2 : (vTmp ^= tlE (var vT)) ⊢ υ1 ⇒ υ2 ∣ 1
  d2 = e-ass (subst (λ z → tlM z ≡ just B) (sym g1T) refl)
             (subst (λ z → rupd z B ≡ just B) (sym g1Tmp) refl)
  d3 : (vT ^= cns (var vL) (var vTmp)) ⊢ υ2 ⇒ υ3 ∣ 1
  d3 = e-ass (cong just (cong₂ _∙_ g2L g2Tmp))
             (subst (λ z → rupd z (A ∙ B) ≡ just nil) (sym g2T) (rupd-self (A ∙ B)))
  d4 : (vS ^= hdE (var vTmp)) ⊢ υ3 ⇒ υ4 ∣ 1
  d4 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g3Tmp) refl)
             (subst (λ z → rupd z (atm x) ≡ just (atm x)) (sym g3S) refl)
  d5 : (vR ^= tlE (var vTmp)) ⊢ υ4 ⇒ υ5 ∣ 1
  d5 = e-ass (subst (λ z → tlM z ≡ just (encL r)) (sym g4Tmp) refl)
             (subst (λ z → rupd z (encL r) ≡ just (encL r)) (sym g4R) refl)
  d6 : (vTmp ^= cns (var vS) (var vR)) ⊢ υ5 ⇒ υ6 ∣ 1
  d6 = e-ass (cong just (cong₂ _∙_ g5S g5R))
             (subst (λ z → rupd z B ≡ just nil) (sym g5Tmp) (rupd-self B))

-- packT is `inv unpackT`, so it is the same six assignments in the opposite
-- order (left-nested, as `inv (c ⨾ d) = inv d ⨾ inv c` builds it).
pack-sound : ∀ σ l x r
  → get σ vL ≡ encL l → get σ vS ≡ atm x → get σ vR ≡ encL r
  → get σ vT ≡ nil → get σ vTmp ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (packT ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vT ≡ encT (l , x , r))
      × (get σ′ vL ≡ nil) × (get σ′ vS ≡ nil) × (get σ′ vR ≡ nil)
      × (get σ′ vTmp ≡ nil)
      × (∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
             → get σ′ y ≡ get σ y) )
pack-sound σ l x r hL hS hR hT hTmp =
    ω6 , _
  , e-seq (e-seq (e-seq (e-seq (e-seq b1 b2) b3) b4) b5) b6
  , g6T , get-set-≡ ω5 vL nil , g6S , g6R , g6Tmp , frame
  where
  A B : V
  A = encL l
  B = atm x ∙ encL r

  ω1 ω2 ω3 ω4 ω5 ω6 : Store
  ω1 = set σ  vTmp B
  ω2 = set ω1 vR   nil
  ω3 = set ω2 vS   nil
  ω4 = set ω3 vT   (A ∙ B)
  ω5 = set ω4 vTmp nil
  ω6 = set ω5 vL   nil

  g1Tmp : get ω1 vTmp ≡ B
  g1Tmp = get-set-≡ σ vTmp B
  g1R : get ω1 vR ≡ encL r
  g1R = trans (get-set-≢ σ vTmp vR B (λ ())) hR
  g2Tmp : get ω2 vTmp ≡ B
  g2Tmp = trans (get-set-≢ ω1 vR vTmp nil (λ ())) g1Tmp
  g2S : get ω2 vS ≡ atm x
  g2S = trans (get-set-≢ ω1 vR vS nil (λ ())) (trans (get-set-≢ σ vTmp vS B (λ ())) hS)
  g3Tmp : get ω3 vTmp ≡ B
  g3Tmp = trans (get-set-≢ ω2 vS vTmp nil (λ ())) g2Tmp
  g3L : get ω3 vL ≡ A
  g3L = trans (get-set-≢ ω2 vS vL nil (λ ()))
        (trans (get-set-≢ ω1 vR vL nil (λ ()))
               (trans (get-set-≢ σ vTmp vL B (λ ())) hL))
  g3T : get ω3 vT ≡ nil
  g3T = trans (get-set-≢ ω2 vS vT nil (λ ()))
        (trans (get-set-≢ ω1 vR vT nil (λ ()))
               (trans (get-set-≢ σ vTmp vT B (λ ())) hT))
  g4T : get ω4 vT ≡ A ∙ B
  g4T = get-set-≡ ω3 vT (A ∙ B)
  g4Tmp : get ω4 vTmp ≡ B
  g4Tmp = trans (get-set-≢ ω3 vT vTmp (A ∙ B) (λ ())) g3Tmp
  g5T : get ω5 vT ≡ A ∙ B
  g5T = trans (get-set-≢ ω4 vTmp vT nil (λ ())) g4T
  g5L : get ω5 vL ≡ A
  g5L = trans (get-set-≢ ω4 vTmp vL nil (λ ()))
        (trans (get-set-≢ ω3 vT vL (A ∙ B) (λ ())) g3L)

  g6T : get ω6 vT ≡ A ∙ B
  g6T = trans (get-set-≢ ω5 vL vT nil (λ ())) g5T
  g6S : get ω6 vS ≡ nil
  g6S = trans (get-set-≢ ω5 vL vS nil (λ ()))
        (trans (get-set-≢ ω4 vTmp vS nil (λ ()))
               (trans (get-set-≢ ω3 vT vS (A ∙ B) (λ ())) (get-set-≡ ω2 vS nil)))
  g6R : get ω6 vR ≡ nil
  g6R = trans (get-set-≢ ω5 vL vR nil (λ ()))
        (trans (get-set-≢ ω4 vTmp vR nil (λ ()))
        (trans (get-set-≢ ω3 vT vR (A ∙ B) (λ ()))
               (trans (get-set-≢ ω2 vS vR nil (λ ())) (get-set-≡ ω1 vR nil))))
  g6Tmp : get ω6 vTmp ≡ nil
  g6Tmp = trans (get-set-≢ ω5 vL vTmp nil (λ ())) (get-set-≡ ω4 vTmp nil)

  frame : ∀ y → ¬ (y ≡ vT) → ¬ (y ≡ vL) → ¬ (y ≡ vS) → ¬ (y ≡ vR) → ¬ (y ≡ vTmp)
        → get ω6 y ≡ get σ y
  frame y yT yL yS yR yTmp =
    trans (get-set-≢ ω5 vL y nil (λ e → yL (sym e)))
    (trans (get-set-≢ ω4 vTmp y nil (λ e → yTmp (sym e)))
    (trans (get-set-≢ ω3 vT y (A ∙ B) (λ e → yT (sym e)))
    (trans (get-set-≢ ω2 vS y nil (λ e → yS (sym e)))
    (trans (get-set-≢ ω1 vR y nil (λ e → yR (sym e)))
           (get-set-≢ σ vTmp y B (λ e → yTmp (sym e)))))))

  b1 : (vTmp ^= cns (var vS) (var vR)) ⊢ σ ⇒ ω1 ∣ 1
  b1 = e-ass (cong just (cong₂ _∙_ hS hR))
             (subst (λ z → rupd z B ≡ just B) (sym hTmp) refl)
  b2 : (vR ^= tlE (var vTmp)) ⊢ ω1 ⇒ ω2 ∣ 1
  b2 = e-ass (subst (λ z → tlM z ≡ just (encL r)) (sym g1Tmp) refl)
             (subst (λ z → rupd z (encL r) ≡ just nil) (sym g1R) (rupd-self (encL r)))
  b3 : (vS ^= hdE (var vTmp)) ⊢ ω2 ⇒ ω3 ∣ 1
  b3 = e-ass (subst (λ z → hdM z ≡ just (atm x)) (sym g2Tmp) refl)
             (subst (λ z → rupd z (atm x) ≡ just nil) (sym g2S) (rupd-self (atm x)))
  b4 : (vT ^= cns (var vL) (var vTmp)) ⊢ ω3 ⇒ ω4 ∣ 1
  b4 = e-ass (cong just (cong₂ _∙_ g3L g3Tmp))
             (subst (λ z → rupd z (A ∙ B) ≡ just (A ∙ B)) (sym g3T) refl)
  b5 : (vTmp ^= tlE (var vT)) ⊢ ω4 ⇒ ω5 ∣ 1
  b5 = e-ass (subst (λ z → tlM z ≡ just B) (sym g4T) refl)
             (subst (λ z → rupd z B ≡ just nil) (sym g4Tmp) (rupd-self B))
  b6 : (vL ^= hdE (var vT)) ⊢ ω5 ⇒ ω6 ∣ 1
  b6 = e-ass (subst (λ z → hdM z ≡ just A) (sym g5T) refl)
             (subst (λ z → rupd z A ≡ just nil) (sym g5L) (rupd-self A))

------------------------------------------------------------------------
-- 5c.  EVERY GENERATED COMMAND IS LEGAL R-WHILE.
--
-- `Wf` is the library's rendering of R-WHILE's linearity side condition: in
-- `x ^= e` the assigned variable must not occur in e.  That is the condition
-- the naive PUSH violated (see the caution below), so it is worth certifying
-- that nothing the translation emits does.  It is also what the library's
-- `inv-sound` demands before it will run a command backwards.

wf-inv : ∀ c → Wf c → Wf (inv c)
wf-inv skip           wf-skip         = wf-skip
wf-inv (x ^= e)       (wf-ass ni)     = wf-ass ni
wf-inv (c ⨾ d)        (wf-seq wc wd)  = wf-seq (wf-inv d wd) (wf-inv c wc)
wf-inv (cond e c d f) (wf-cond wc wd) = wf-cond (wf-inv c wc) (wf-inv d wd)
wf-inv (loop e D L f) (wf-loop wD wL) = wf-loop (wf-inv D wD) (wf-inv L wL)

wf-unpackT : Wf unpackT
wf-unpackT =
  wf-seq (wf-ass (ni-hd  (ni-var (λ ()))))
  (wf-seq (wf-ass (ni-tl  (ni-var (λ ()))))
  (wf-seq (wf-ass (ni-cns (ni-var (λ ())) (ni-var (λ ()))))
  (wf-seq (wf-ass (ni-hd  (ni-var (λ ()))))
  (wf-seq (wf-ass (ni-tl  (ni-var (λ ()))))
          (wf-ass (ni-cns (ni-var (λ ())) (ni-var (λ ()))))))))

wf-packT : Wf packT
wf-packT = wf-inv unpackT wf-unpackT

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

------------------------------------------------------------------------
-- 8.  The translation of one rule (Fig. 3).
--
--   (q₁,(s₁,s₂),q₂)  ↦  [q̄₁,(L s̄₁ R)] => [q̄₂,(L s̄₂ R)]
--   (q₁,←,q₂)        ↦  [q̄₁,T] => { MOVEL(T) ; Q ^= q̄₁ ; Q ^= q̄₂ }
--   (q₁,↓,q₂)        ↦  [q̄₁,T] => [q̄₂,T]
--   (q₁,→,q₂)        ↦  [q̄₁,T] => { MOVER(T) ; Q ^= q̄₁ ; Q ^= q̄₂ }
--
-- Here only the BODY of each branch is built; the dispatch that selects it
-- is `stepC` (milestone 2).  A state change is always the pair of
-- assignments `Q ^= q̄₁ ; Q ^= q̄₂`: the first clears (rupd case 2), the
-- second sets (rupd case 1).

setState : ℕ → ℕ → Cmd
setState q₁ q₂ = vQ ^= opd (cst (atm q₁)) ⨾ vQ ^= opd (cst (atm q₂))

ruleC : ℕ → Rule → Cmd
ruleC b (rsym q₁ s₁ s₂ q₂) =
    unpackT
  ⨾ vS ^= opd (cst (atm s₁))
  ⨾ vS ^= opd (cst (atm s₂))
  ⨾ packT
  ⨾ setState q₁ q₂
ruleC b (rmov q₁ mvL q₂) = movelC b ⨾ setState q₁ q₂
ruleC b (rmov q₁ mvS q₂) = setState q₁ q₂
ruleC b (rmov q₁ mvR q₂) = moverC b ⨾ setState q₁ q₂

wf-setState : ∀ q₁ q₂ → Wf (setState q₁ q₂)
wf-setState q₁ q₂ = wf-seq (wf-ass (ni-opd ni-cst)) (wf-ass (ni-opd ni-cst))

-- THE TRANSLATION EMITS ONLY LEGAL R-WHILE.
wf-ruleC : ∀ b d → Wf (ruleC b d)
wf-ruleC b (rsym q₁ s₁ s₂ q₂) =
  wf-seq wf-unpackT
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq wf-packT (wf-setState q₁ q₂))))
wf-ruleC b (rmov q₁ mvL q₂) = wf-seq (wf-movelC b) (wf-setState q₁ q₂)
wf-ruleC b (rmov q₁ mvS q₂) = wf-setState q₁ q₂
wf-ruleC b (rmov q₁ mvR q₂) = wf-seq (wf-moverC b) (wf-setState q₁ q₂)

setState-sound : ∀ q₁ q₂ σ → get σ vQ ≡ atm q₁
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (setState q₁ q₂ ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂)
      × (∀ y → ¬ (y ≡ vQ) → get σ′ y ≡ get σ y) )
setState-sound q₁ q₂ σ hQ =
    set (set σ vQ nil) vQ (atm q₂) , _
  , e-seq s1 s2
  , get-set-≡ (set σ vQ nil) vQ (atm q₂)
  , (λ y yq → trans (get-set-≢ (set σ vQ nil) vQ y (atm q₂) (λ e → yq (sym e)))
                    (get-set-≢ σ vQ y nil (λ e → yq (sym e))))
  where
  s1 : (vQ ^= opd (cst (atm q₁))) ⊢ σ ⇒ set σ vQ nil ∣ 1
  s1 = e-ass refl (subst (λ z → rupd z (atm q₁) ≡ just nil) (sym hQ)
                         (rupd-self (atm q₁)))
  s2 : (vQ ^= opd (cst (atm q₂))) ⊢ set σ vQ nil
                                 ⇒ set (set σ vQ nil) vQ (atm q₂) ∣ 1
  s2 = e-ass refl (subst (λ z → rupd z (atm q₂) ≡ just (atm q₂))
                         (sym (get-set-≡ σ vQ nil)) refl)

------------------------------------------------------------------------
-- 8c.  THE RULE BODIES ON THE UNPACKED TAPE, WITH THE DISPATCH KEY.
--
-- Invariant of the main loop: Q holds the state, S the symbol under the
-- head, L and R the half-tapes, and K the PAIR (Q . S).  K is redundant —
-- it is a function of Q and S — but it is what makes the guard of a symbol
-- rule a single flat test, and it is cleared again when the loop ends, so
-- it is not garbage.
--
-- A state change is `Q ^= q̄ ; Q ^= q̄′` (clear then set) as before, and the
-- key is re-established by `K ^= cons Q S`, which is its own inverse: it
-- CLEARS K when K already holds (Q . S) and SETS it when K is nil.

-- Projections of a tape.  Tape is a Σ-type, so these reduce even when the
-- tape is a variable; that is what lets `HoldsU` be stated on an
-- undestructured configuration and still compute.
lefts : Tape → List ℕ
lefts (l , _ , _) = l
symOf : Tape → ℕ
symOf (_ , x , _) = x
rights : Tape → List ℕ
rights (_ , _ , r) = r

stOf : Conf → ℕ
stOf (q , _) = q
tpOf : Conf → Tape
tpOf (_ , t) = t

HoldsU : Conf → Store → Set
HoldsU c σ =
    (get σ vQ ≡ atm (stOf c)) × (get σ vS ≡ atm (symOf (tpOf c)))
  × (get σ vL ≡ encL (lefts (tpOf c))) × (get σ vR ≡ encL (rights (tpOf c)))
  × (get σ vK ≡ atm (stOf c) ∙ atm (symOf (tpOf c)))

UFrame : Store → Store → Set
UFrame σ′ σ = ∀ y → ¬ (y ≡ vQ) → ¬ (y ≡ vS) → ¬ (y ≡ vL) → ¬ (y ≡ vR)
            → ¬ (y ≡ vK) → ¬ (y ≡ vW) → get σ′ y ≡ get σ y

setKey : Cmd
setKey = vK ^= cns (var vQ) (var vS)

uruleC : ℕ → Rule → Cmd
uruleC b (rsym q s s′ q′) =
    vK ^= opd (cst (atm q  ∙ atm s ))
  ⨾ vS ^= opd (cst (atm s ))
  ⨾ vS ^= opd (cst (atm s′))
  ⨾ vQ ^= opd (cst (atm q ))
  ⨾ vQ ^= opd (cst (atm q′))
  ⨾ vK ^= opd (cst (atm q′ ∙ atm s′))
uruleC b (rmov q mvL q′) = setKey ⨾ setState q q′ ⨾ moveLC b ⨾ setKey
uruleC b (rmov q mvS q′) = setKey ⨾ setState q q′ ⨾ setKey
uruleC b (rmov q mvR q′) = setKey ⨾ setState q q′ ⨾ moveRC b ⨾ setKey

wf-setKey : Wf setKey
wf-setKey = wf-ass (ni-cns (ni-var (λ ())) (ni-var (λ ())))

wf-uruleC : ∀ b d → Wf (uruleC b d)
wf-uruleC b (rsym q s s′ q′) =
  wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst))
  (wf-seq (wf-ass (ni-opd ni-cst)) (wf-ass (ni-opd ni-cst))))))
wf-uruleC b (rmov q mvL q′) =
  wf-seq wf-setKey (wf-seq (wf-setState q q′) (wf-seq (wf-moveLC b) wf-setKey))
wf-uruleC b (rmov q mvS q′) =
  wf-seq wf-setKey (wf-seq (wf-setState q q′) wf-setKey)
wf-uruleC b (rmov q mvR q′) =
  wf-seq wf-setKey (wf-seq (wf-setState q q′) (wf-seq (wf-moveRC b) wf-setKey))

-- the two directions of a constant reversible assignment
constSet : ∀ x c σ → get σ x ≡ nil → (x ^= opd (cst c)) ⊢ σ ⇒ set σ x c ∣ 1
constSet x c σ h = e-ass refl (subst (λ z → rupd z c ≡ just c) (sym h) refl)

constClr : ∀ x c σ → get σ x ≡ c → (x ^= opd (cst c)) ⊢ σ ⇒ set σ x nil ∣ 1
constClr x c σ h = e-ass refl (subst (λ z → rupd z c ≡ just nil) (sym h) (rupd-self c))

setKey-set : ∀ σ q x → get σ vQ ≡ atm q → get σ vS ≡ atm x → get σ vK ≡ nil
           → setKey ⊢ σ ⇒ set σ vK (atm q ∙ atm x) ∣ 1
setKey-set σ q x hQ hS hK =
  e-ass (cong just (cong₂ _∙_ hQ hS))
        (subst (λ z → rupd z (atm q ∙ atm x) ≡ just (atm q ∙ atm x)) (sym hK) refl)

setKey-clr : ∀ σ q x → get σ vQ ≡ atm q → get σ vS ≡ atm x
           → get σ vK ≡ atm q ∙ atm x → setKey ⊢ σ ⇒ set σ vK nil ∣ 1
setKey-clr σ q x hQ hS hK =
  e-ass (cong just (cong₂ _∙_ hQ hS))
        (subst (λ z → rupd z (atm q ∙ atm x) ≡ just nil) (sym hK)
               (rupd-self (atm q ∙ atm x)))

USpec : ℕ → Rule → Conf → Store → Set
USpec b d c′ σ =
  Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
    ( (uruleC b d ⊢ σ ⇒ σ′ ∣ k) × HoldsU c′ σ′ × (get σ′ vW ≡ nil) × UFrame σ′ σ )

-- (q,(s,s′),q′) : six constant assignments, nothing else moves.
usym-sound : ∀ b q s s′ q′ σ l r
  → HoldsU (q , (l , s , r)) σ → get σ vW ≡ nil
  → USpec b (rsym q s s′ q′) (q′ , (l , s′ , r)) σ
usym-sound b q s s′ q′ σ l r (hQ , hS , hL , hR , hK) hW =
    τ6 , _
  , e-seq a1 (e-seq a2 (e-seq a3 (e-seq a4 (e-seq a5 a6))))
  , (g6Q , g6S , g6L , g6R , get-set-≡ τ5 vK (atm q′ ∙ atm s′))
  , g6W , frame
  where
  τ1 τ2 τ3 τ4 τ5 τ6 : Store
  τ1 = set σ  vK nil
  τ2 = set τ1 vS nil
  τ3 = set τ2 vS (atm s′)
  τ4 = set τ3 vQ nil
  τ5 = set τ4 vQ (atm q′)
  τ6 = set τ5 vK (atm q′ ∙ atm s′)

  g1S : get τ1 vS ≡ atm s
  g1S = trans (get-set-≢ σ vK vS nil (λ ())) hS
  g3Q : get τ3 vQ ≡ atm q
  g3Q = trans (get-set-≢ τ2 vS vQ (atm s′) (λ ()))
        (trans (get-set-≢ τ1 vS vQ nil (λ ()))
               (trans (get-set-≢ σ vK vQ nil (λ ())) hQ))
  g5K : get τ5 vK ≡ nil
  g5K = trans (get-set-≢ τ4 vQ vK (atm q′) (λ ()))
        (trans (get-set-≢ τ3 vQ vK nil (λ ()))
        (trans (get-set-≢ τ2 vS vK (atm s′) (λ ()))
        (trans (get-set-≢ τ1 vS vK nil (λ ())) (get-set-≡ σ vK nil))))

  a1 = constClr vK (atm q ∙ atm s) σ hK
  a2 = constClr vS (atm s) τ1 g1S
  a3 = constSet vS (atm s′) τ2 (get-set-≡ τ1 vS nil)
  a4 = constClr vQ (atm q) τ3 g3Q
  a5 = constSet vQ (atm q′) τ4 (get-set-≡ τ3 vQ nil)
  a6 = constSet vK (atm q′ ∙ atm s′) τ5 g5K

  g6Q : get τ6 vQ ≡ atm q′
  g6Q = trans (get-set-≢ τ5 vK vQ (atm q′ ∙ atm s′) (λ ()))
              (get-set-≡ τ4 vQ (atm q′))
  g6S : get τ6 vS ≡ atm s′
  g6S = trans (get-set-≢ τ5 vK vS (atm q′ ∙ atm s′) (λ ()))
        (trans (get-set-≢ τ4 vQ vS (atm q′) (λ ()))
        (trans (get-set-≢ τ3 vQ vS nil (λ ())) (get-set-≡ τ2 vS (atm s′))))
  down : ∀ y → ¬ (y ≡ vQ) → ¬ (y ≡ vS) → ¬ (y ≡ vK) → get τ6 y ≡ get σ y
  down y yQ yS yK =
    trans (get-set-≢ τ5 vK y (atm q′ ∙ atm s′) (λ e → yK (sym e)))
    (trans (get-set-≢ τ4 vQ y (atm q′) (λ e → yQ (sym e)))
    (trans (get-set-≢ τ3 vQ y nil (λ e → yQ (sym e)))
    (trans (get-set-≢ τ2 vS y (atm s′) (λ e → yS (sym e)))
    (trans (get-set-≢ τ1 vS y nil (λ e → yS (sym e)))
           (get-set-≢ σ vK y nil (λ e → yK (sym e)))))))
  g6L : get τ6 vL ≡ encL l
  g6L = trans (down vL (λ ()) (λ ()) (λ ())) hL
  g6R : get τ6 vR ≡ encL r
  g6R = trans (down vR (λ ()) (λ ()) (λ ())) hR
  g6W : get τ6 vW ≡ nil
  g6W = trans (down vW (λ ()) (λ ()) (λ ())) hW
  frame : UFrame τ6 σ
  frame y yQ yS yL yR yK yW = down y yQ yS yK

-- (q,↓,q′) : clear the key, change the state, re-establish the key.
umvS-sound : ∀ b q q′ σ l x r
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → USpec b (rmov q mvS q′) (q′ , (l , x , r)) σ
umvS-sound b q q′ σ l x r (hQ , hS , hL , hR , hK) hW
  with setState-sound q q′ (set σ vK nil)
         (trans (get-set-≢ σ vK vQ nil (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2 =
    set σ₂ vK (atm q′ ∙ atm x) , _
  , e-seq (setKey-clr σ q x hQ hS hK) (e-seq dS (setKey-set σ₂ q′ x g2Q g2S g2K))
  , ( trans (get-set-≢ σ₂ vK vQ (atm q′ ∙ atm x) (λ ())) g2Q
    , trans (get-set-≢ σ₂ vK vS (atm q′ ∙ atm x) (λ ())) g2S
    , trans (get-set-≢ σ₂ vK vL (atm q′ ∙ atm x) (λ ())) g2L
    , trans (get-set-≢ σ₂ vK vR (atm q′ ∙ atm x) (λ ())) g2R
    , get-set-≡ σ₂ vK (atm q′ ∙ atm x) )
  , trans (get-set-≢ σ₂ vK vW (atm q′ ∙ atm x) (λ ())) g2W
  , (λ y yQ yS yL yR yK yW →
       trans (get-set-≢ σ₂ vK y (atm q′ ∙ atm x) (λ e → yK (sym e)))
       (trans (f2 y yQ) (get-set-≢ σ vK y nil (λ e → yK (sym e)))))
  where
  g2S : get σ₂ vS ≡ atm x
  g2S = trans (f2 vS (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS)
  g2L : get σ₂ vL ≡ encL l
  g2L = trans (f2 vL (λ ())) (trans (get-set-≢ σ vK vL nil (λ ())) hL)
  g2R : get σ₂ vR ≡ encL r
  g2R = trans (f2 vR (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR)
  g2W : get σ₂ vW ≡ nil
  g2W = trans (f2 vW (λ ())) (trans (get-set-≢ σ vK vW nil (λ ())) hW)
  g2K : get σ₂ vK ≡ nil
  g2K = trans (f2 vK (λ ())) (get-set-≡ σ vK nil)

-- (q,←,q′) : clear the key, change the state, MOVE, re-establish the key.
umvL-sound : ∀ b q q′ σ l x r → NoTrailB b l
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → USpec b (rmov q mvL q′) (q′ , (popTail l , popHead b l , consNB b x r)) σ
umvL-sound b q q′ σ l x r ntl (hQ , hS , hL , hR , hK) hW
  with setState-sound q q′ (set σ vK nil)
         (trans (get-set-≢ σ vK vQ nil (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2
  with moveL-sound b σ₂ l x r ntl
         (trans (f2 vS (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS))
         (trans (f2 vL (λ ())) (trans (get-set-≢ σ vK vL nil (λ ())) hL))
         (trans (f2 vR (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR))
         (trans (f2 vW (λ ())) (trans (get-set-≢ σ vK vW nil (λ ())) hW))
... | σ₃ , _ , dM , g3S , g3L , g3R , g3W , f3 =
    set σ₃ vK (atm q′ ∙ atm (popHead b l)) , _
  , e-seq (setKey-clr σ q x hQ hS hK)
          (e-seq dS (e-seq dM (setKey-set σ₃ q′ (popHead b l) g3Q g3S g3K)))
  , ( trans (get-set-≢ σ₃ vK vQ _ (λ ())) g3Q
    , trans (get-set-≢ σ₃ vK vS _ (λ ())) g3S
    , trans (get-set-≢ σ₃ vK vL _ (λ ())) g3L
    , trans (get-set-≢ σ₃ vK vR _ (λ ())) g3R
    , get-set-≡ σ₃ vK _ )
  , trans (get-set-≢ σ₃ vK vW _ (λ ())) g3W
  , (λ y yQ yS yL yR yK yW →
       trans (get-set-≢ σ₃ vK y _ (λ e → yK (sym e)))
       (trans (f3 y yS yL yR yW)
       (trans (f2 y yQ) (get-set-≢ σ vK y nil (λ e → yK (sym e))))))
  where
  g3Q : get σ₃ vQ ≡ atm q′
  g3Q = trans (f3 vQ (λ ()) (λ ()) (λ ()) (λ ())) g2Q
  g3K : get σ₃ vK ≡ nil
  g3K = trans (f3 vK (λ ()) (λ ()) (λ ()) (λ ()))
              (trans (f2 vK (λ ())) (get-set-≡ σ vK nil))

-- (q,→,q′) : the mirror image.
umvR-sound : ∀ b q q′ σ l x r → NoTrailB b r
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → USpec b (rmov q mvR q′) (q′ , (consNB b x l , popHead b r , popTail r)) σ
umvR-sound b q q′ σ l x r ntr (hQ , hS , hL , hR , hK) hW
  with setState-sound q q′ (set σ vK nil)
         (trans (get-set-≢ σ vK vQ nil (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2
  with moveR-sound b σ₂ l x r ntr
         (trans (f2 vS (λ ())) (trans (get-set-≢ σ vK vS nil (λ ())) hS))
         (trans (f2 vL (λ ())) (trans (get-set-≢ σ vK vL nil (λ ())) hL))
         (trans (f2 vR (λ ())) (trans (get-set-≢ σ vK vR nil (λ ())) hR))
         (trans (f2 vW (λ ())) (trans (get-set-≢ σ vK vW nil (λ ())) hW))
... | σ₃ , _ , dM , g3S , g3R , g3L , g3W , f3 =
    set σ₃ vK (atm q′ ∙ atm (popHead b r)) , _
  , e-seq (setKey-clr σ q x hQ hS hK)
          (e-seq dS (e-seq dM (setKey-set σ₃ q′ (popHead b r) g3Q g3S g3K)))
  , ( trans (get-set-≢ σ₃ vK vQ _ (λ ())) g3Q
    , trans (get-set-≢ σ₃ vK vS _ (λ ())) g3S
    , trans (get-set-≢ σ₃ vK vL _ (λ ())) g3L
    , trans (get-set-≢ σ₃ vK vR _ (λ ())) g3R
    , get-set-≡ σ₃ vK _ )
  , trans (get-set-≢ σ₃ vK vW _ (λ ())) g3W
  , (λ y yQ yS yL yR yK yW →
       trans (get-set-≢ σ₃ vK y _ (λ e → yK (sym e)))
       (trans (f3 y yS yL yR yW)
       (trans (f2 y yQ) (get-set-≢ σ vK y nil (λ e → yK (sym e))))))
  where
  g3Q : get σ₃ vQ ≡ atm q′
  g3Q = trans (f3 vQ (λ ()) (λ ()) (λ ()) (λ ())) g2Q
  g3K : get σ₃ vK ≡ nil
  g3K = trans (f3 vK (λ ()) (λ ()) (λ ()) (λ ()))
              (trans (f2 vK (λ ())) (get-set-≡ σ vK nil))

------------------------------------------------------------------------
-- 8d.  THE GUARDS OF THE DISPATCH, AND WHAT THE RTM CONDITIONS BUY.
--
-- The letter's STEP is `rewrite [Q,T] by d̲₁ | … | d̲ₙ`, a reversible
-- multi-way case.  In the core it becomes a chain of binary conditionals,
-- one per rule: the ENTRY test says "this rule's left pattern matches" and
-- the EXIT test says "its right pattern matches".  Local forward
-- determinism makes the entry tests mutually exclusive (so the chain picks
-- the right branch going forwards); local backward determinism makes the
-- exit tests mutually exclusive (so it does going backwards).  Both are
-- packaged below as "at most one rule fires", which is what the chain
-- actually consumes.

ft→⊥ : false ≡ true → ⊥
ft→⊥ ()

_≟M_ : (a c : Move) → Dec (a ≡ c)
mvL ≟M mvL = yes refl
mvL ≟M mvS = no λ ()
mvL ≟M mvR = no λ ()
mvS ≟M mvL = no λ ()
mvS ≟M mvS = yes refl
mvS ≟M mvR = no λ ()
mvR ≟M mvL = no λ ()
mvR ≟M mvS = no λ ()
mvR ≟M mvR = yes refl

_≟R_ : (d e : Rule) → Dec (d ≡ e)
rsym _ _ _ _ ≟R rmov _ _ _   = no λ ()
rmov _ _ _   ≟R rsym _ _ _ _ = no λ ()
rsym q s u p ≟R rsym q′ s′ u′ p′ with q ≟ q′
... | no ne = no λ { refl → ne refl }
... | yes refl with s ≟ s′
...   | no ne = no λ { refl → ne refl }
...   | yes refl with u ≟ u′
...     | no ne = no λ { refl → ne refl }
...     | yes refl with p ≟ p′
...       | no ne = no λ { refl → ne refl }
...       | yes refl = yes refl
rmov q a p ≟R rmov q′ a′ p′ with q ≟ q′
... | no ne = no λ { refl → ne refl }
... | yes refl with a ≟M a′
...   | no ne = no λ { refl → ne refl }
...   | yes refl with p ≟ p′
...     | no ne = no λ { refl → ne refl }
...     | yes refl = yes refl

-- The guards, as R-WHILE expressions.  Each is ONE equality against a
-- constant: a symbol rule tests the key (Q . S), a move rule tests Q alone.
entryE : Rule → Exp
entryE (rsym q s _ _)  = eqE (var vK) (cst (atm q ∙ atm s))
entryE (rmov q _ _)    = eqE (var vQ) (cst (atm q))

exitE : Rule → Exp
exitE (rsym _ _ s′ q′) = eqE (var vK) (cst (atm q′ ∙ atm s′))
exitE (rmov _ _ q′)    = eqE (var vQ) (cst (atm q′))

-- and what they compute, as booleans on the (state, symbol) pair
entryB : Rule → ℕ → ℕ → Bool
entryB (rsym q₀ s₀ _ _) q x = if eqℕ q q₀ then eqℕ x s₀ else false
entryB (rmov q₀ _ _)    q x = eqℕ q q₀

exitB : Rule → ℕ → ℕ → Bool
exitB (rsym _ _ s₀ q₀) q x = if eqℕ q q₀ then eqℕ x s₀ else false
exitB (rmov _ _ q₀)    q x = eqℕ q q₀

eval-entry : ∀ d σ q x → get σ vQ ≡ atm q → get σ vK ≡ atm q ∙ atm x
           → evalT σ (entryE d) ≡ just (entryB d q x)
eval-entry (rsym _ _ _ _) σ q x hQ hK rewrite hK = cong just (isTrue-boolV _)
eval-entry (rmov _ _ _)   σ q x hQ hK rewrite hQ = cong just (isTrue-boolV _)

eval-exit : ∀ d σ q x → get σ vQ ≡ atm q → get σ vK ≡ atm q ∙ atm x
          → evalT σ (exitE d) ≡ just (exitB d q x)
eval-exit (rsym _ _ _ _) σ q x hQ hK rewrite hK = cong just (isTrue-boolV _)
eval-exit (rmov _ _ _)   σ q x hQ hK rewrite hQ = cong just (isTrue-boolV _)

-- reading a firing guard back
entryB-src : ∀ d q x → entryB d q x ≡ true → src d ≡ q
entryB-src (rsym q₀ s₀ _ _) q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → q₀ ≡ q
  go true  h = sym (eqℕ-true-inv q q₀ h)
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))
entryB-src (rmov q₀ _ _) q x e = sym (eqℕ-true-inv q q₀ e)

entryB-read : ∀ q₀ s₀ u₀ p₀ q x → entryB (rsym q₀ s₀ u₀ p₀) q x ≡ true → s₀ ≡ x
entryB-read q₀ s₀ u₀ p₀ q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → s₀ ≡ x
  go true  h = sym (eqℕ-true-inv x s₀
                 (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))

exitB-tgt : ∀ d q x → exitB d q x ≡ true → tgt d ≡ q
exitB-tgt (rsym _ _ s₀ q₀) q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → q₀ ≡ q
  go true  h = sym (eqℕ-true-inv q q₀ h)
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x s₀ else false) ≡ true) h e))
exitB-tgt (rmov _ _ q₀) q x e = sym (eqℕ-true-inv q q₀ e)

exitB-write : ∀ p₀ s₀ u₀ q₀ q x → exitB (rsym p₀ s₀ u₀ q₀) q x ≡ true → u₀ ≡ x
exitB-write p₀ s₀ u₀ q₀ q x e = go (eqℕ q q₀) refl
  where
  go : ∀ u → eqℕ q q₀ ≡ u → u₀ ≡ x
  go true  h = sym (eqℕ-true-inv x u₀
                 (subst (λ z → (if z then eqℕ x u₀ else false) ≡ true) h e))
  go false h = ⊥-elim (ft→⊥ (subst (λ z → (if z then eqℕ x u₀ else false) ≡ true) h e))

-- LOCAL FORWARD DETERMINISM, in the form the dispatch uses: at most one
-- rule of the machine fires on a given (state, scanned symbol).
lfd-fires : ∀ {M} → LFD M → ∀ d₁ d₂ q x → d₁ ∈ rules M → d₂ ∈ rules M
          → entryB d₁ q x ≡ true → entryB d₂ q x ≡ true → d₁ ≡ d₂
lfd-fires lfd d₁ d₂ q x m₁ m₂ e₁ e₂ with d₁ ≟R d₂
... | yes eq = eq
... | no ne
  with lfd d₁ d₂ m₁ m₂ ne
         (trans (entryB-src d₁ q x e₁) (sym (entryB-src d₂ q x e₂)))
...  | _ , s₁ , _ , _ , s₂ , _ , _ , refl , refl , s₁≢s₂ =
       ⊥-elim (s₁≢s₂ (trans (entryB-read _ s₁ _ _ q x e₁)
                            (sym (entryB-read _ s₂ _ _ q x e₂))))

-- LOCAL BACKWARD DETERMINISM, likewise: at most one rule of the machine can
-- have produced a given (state, written symbol).
lbd-fires : ∀ {M} → LBD M → ∀ d₁ d₂ q x → d₁ ∈ rules M → d₂ ∈ rules M
          → exitB d₁ q x ≡ true → exitB d₂ q x ≡ true → d₁ ≡ d₂
lbd-fires lbd d₁ d₂ q x m₁ m₂ e₁ e₂ with d₁ ≟R d₂
... | yes eq = eq
... | no ne
  with lbd d₁ d₂ m₁ m₂ ne
         (trans (exitB-tgt d₁ q x e₁) (sym (exitB-tgt d₂ q x e₂)))
...  | _ , _ , u₁ , _ , _ , u₂ , _ , refl , refl , u₁≢u₂ =
       ⊥-elim (u₁≢u₂ (trans (exitB-write _ _ u₁ _ q x e₁)
                            (sym (exitB-write _ _ u₂ _ q x e₂))))

------------------------------------------------------------------------
-- 8e.  ONE LEMMA FOR THE FOUR RULE BODIES, PLUS THE TWO GUARD FACTS.

-- the rule that makes a step fires on that step's (state, scanned symbol) ...
fires-entry : ∀ b d q t c′ → StepBy b d (q , t) c′ → entryB d q (symOf t) ≡ true
fires-entry b (rsym q s _ _) _ _ _ sb-sym rewrite eqℕ-refl q | eqℕ-refl s = refl
fires-entry b (rmov q _ _) _ _ _ sb-lft   = eqℕ-refl q
fires-entry b (rmov q _ _) _ _ _ sb-sty   = eqℕ-refl q
fires-entry b (rmov q _ _) _ _ _ (sb-rgt _) = eqℕ-refl q

-- ... and its output pattern matches the (state, written symbol) it left
fires-exit : ∀ b d q t q′ t′ → StepBy b d (q , t) (q′ , t′)
           → exitB d q′ (symOf t′) ≡ true
fires-exit b (rsym _ _ s′ q′) _ _ _ _ sb-sym rewrite eqℕ-refl q′ | eqℕ-refl s′ = refl
fires-exit b (rmov _ _ q′) _ _ _ _ sb-lft     = eqℕ-refl q′
fires-exit b (rmov _ _ q′) _ _ _ _ sb-sty     = eqℕ-refl q′
fires-exit b (rmov _ _ q′) _ _ _ _ (sb-rgt _) = eqℕ-refl q′

ubody-sound : ∀ b d q l x r c′ σ
  → StepBy b d (q , (l , x , r)) c′
  → TapeOK b (l , x , r) → TapeOK b (tpOf c′)
  → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (uruleC b d ⊢ σ ⇒ σ′ ∣ k) × HoldsU c′ σ′
      × (get σ′ vW ≡ nil) × UFrame σ′ σ )
ubody-sound b _ q l x r _ σ (sb-sym {s′ = s′} {q′ = q′}) _ _ hu hW =
  usym-sound b q x s′ q′ σ l r hu hW
ubody-sound b _ q l x r _ σ (sb-lft {q′ = q′}) (ntl , _) _ hu hW =
  subst (λ z → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
                 ( (uruleC b (rmov q mvL q′) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , z) σ′
                 × (get σ′ vW ≡ nil) × UFrame σ′ σ ))
        (sym (movel-pop-push b l x r))
        (umvL-sound b q q′ σ l x r ntl hu hW)
ubody-sound b _ q l x r _ σ (sb-sty {q′ = q′}) _ _ hu hW =
  umvS-sound b q q′ σ l x r hu hW
ubody-sound b _ q l x r _ σ (sb-rgt {q′ = q′} {l′ = l′} {x′} {r′} em) (_ , ntr)
            (ntl′ , _) hu hW =
  subst (λ z → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
                 ( (uruleC b (rmov q mvR q′) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , z) σ′
                 × (get σ′ vW ≡ nil) × UFrame σ′ σ ))
        t′-is
        (umvR-sound b q q′ σ l x r ntr hu hW)
  where
  t′-is : (consNB b x l , popHead b r , popTail r) ≡ (l′ , x′ , r′)
  t′-is = trans (sym (cong (mover b) em)) (mover-movel b l′ x′ r′ ntl′)

------------------------------------------------------------------------
-- 8f.  THE DISPATCH: the letter's `rewrite [Q,T] by d̲₁ | … | d̲ₙ`.
--
-- One binary conditional per rule.  Going FORWARDS the chain picks the
-- branch whose entry guard fires, and local forward determinism says at
-- most one does.  Going BACKWARDS — which is what the exit assertions
-- police — local backward determinism says at most one rule could have
-- produced the state and symbol now in place.  Both conditions are used
-- exactly once each, below.

stepC : ℕ → List Rule → Cmd
stepC b []       = skip
stepC b (d ∷ ds) = cond (entryE d) (uruleC b d) (stepC b ds) (exitE d)

wf-stepC : ∀ b ds → Wf (stepC b ds)
wf-stepC b []       = wf-skip
wf-stepC b (d ∷ ds) = wf-cond (wf-uruleC b d) (wf-stepC b ds)

module Dispatch (M : RTM) (ok : IsRTM M) where
  open IsRTM ok

  dispatch-sound : ∀ ds d q l x r q′ t′ σ
    → (∀ e → e ∈ ds → e ∈ rules M)
    → d ∈ ds → d ∈ rules M
    → StepBy (blank M) d (q , (l , x , r)) (q′ , t′)
    → TapeOK (blank M) (l , x , r) → TapeOK (blank M) t′
    → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
    → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
        ( (stepC (blank M) ds ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , t′) σ′
        × (get σ′ vW ≡ nil) × UFrame σ′ σ )
  dispatch-sound [] d q l x r q′ t′ σ sub () md st tok tok′ hu hW
  dispatch-sound (d₀ ∷ ds) d q l x r q′ t′ σ sub mem md st tok tok′
                 (hQ , hS , hL , hR , hK) hW = go (entryB d₀ q x) refl
    where
    firesE : entryB d q x ≡ true
    firesE = fires-entry (blank M) d q (l , x , r) (q′ , t′) st
    firesX : exitB d q′ (symOf t′) ≡ true
    firesX = fires-exit (blank M) d q (l , x , r) q′ t′ st

    -- if the head's guard does NOT fire, the head is not our rule ...
    neq : entryB d₀ q x ≡ false → ¬ (d ≡ d₀)
    neq h px = tf→⊥ (trans (sym (subst (λ z → entryB z q x ≡ true) px firesE)) h)

    -- ... so the rule is further down the chain ...
    memTail : (m : d ∈ (d₀ ∷ ds)) → entryB d₀ q x ≡ false → d ∈ ds
    memTail (here px) h = ⊥-elim (neq h px)
    memTail (there m) h = m

    -- ... and, by LOCAL BACKWARD DETERMINISM, the head's exit assertion is
    -- false on the store the rest of the chain leaves behind.  Without that
    -- the else-branch could not be closed.
    exFalse : entryB d₀ q x ≡ false → exitB d₀ q′ (symOf t′) ≡ false
    exFalse h = g2 (exitB d₀ q′ (symOf t′)) refl
      where
      g2 : ∀ u → exitB d₀ q′ (symOf t′) ≡ u → exitB d₀ q′ (symOf t′) ≡ false
      g2 true hh = ⊥-elim (neq h (sym (lbd-fires lbd d₀ d q′ (symOf t′)
                                        (sub d₀ (here refl)) md hh firesX)))
      g2 false hh = hh

    go : ∀ u → entryB d₀ q x ≡ u
       → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
           ( (stepC (blank M) (d₀ ∷ ds) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , t′) σ′
           × (get σ′ vW ≡ nil) × UFrame σ′ σ )
    -- the head's guard fires: by LOCAL FORWARD DETERMINISM it IS our rule
    go true h
      with lfd-fires lfd d₀ d q x (sub d₀ (here refl)) md h firesE
    ... | refl
      with ubody-sound (blank M) d q l x r (q′ , t′) σ st tok tok′
                       (hQ , hS , hL , hR , hK) hW
    ...  | σ′ , _ , dBody , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr =
           σ′ , _
         , e-then (trans (eval-entry d σ q x hQ hK) (cong just firesE))
                  dBody
                  (trans (eval-exit d σ′ q′ (symOf t′) hQ′ hK′) (cong just firesX))
         , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr
    -- it does not: skip this branch and recurse
    go false h
      with dispatch-sound ds d q l x r q′ t′ σ (λ e me → sub e (there me))
                          (memTail mem h) md st tok tok′ (hQ , hS , hL , hR , hK) hW
    ... | σ′ , _ , dRest , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr =
          σ′ , _
        , e-else (trans (eval-entry d₀ σ q x hQ hK) (cong just h))
                 dRest
                 (trans (eval-exit d₀ σ′ q′ (symOf t′) hQ′ hK′)
                        (cong just (exFalse h)))
        , (hQ′ , hS′ , hL′ , hR′ , hK′) , hW′ , fr

  -- THE STEP: the whole rule list, for a step the machine actually makes.
  step-sound : ∀ q l x r q′ t′ σ
    → Step M (q , (l , x , r)) (q′ , t′)
    → TapeOK (blank M) (l , x , r) → TapeOK (blank M) t′
    → HoldsU (q , (l , x , r)) σ → get σ vW ≡ nil
    → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
        ( (stepC (blank M) (rules M) ⊢ σ ⇒ σ′ ∣ k) × HoldsU (q′ , t′) σ′
        × (get σ′ vW ≡ nil) × UFrame σ′ σ )
  step-sound q l x r q′ t′ σ stp tok tok′ hu hW with step-splits stp
  ... | d , md , sb =
    dispatch-sound (rules M) d q l x r q′ t′ σ (λ _ me → me) md md sb
                   tok tok′ hu hW

------------------------------------------------------------------------
-- 9b.  LEMMA 1, for the rules that do not move the head.
--
-- The two easy shapes of Fig. 3 are discharged here: the symbol rewrite
--     (q₁,(s₁,s₂),q₂)  ↦  [q̄₁,(L s̄₁ R)] => [q̄₂,(L s̄₂ R)]
-- and the stay rule
--     (q₁,↓,q₂)        ↦  [q̄₁,T] => [q̄₂,T].
-- The two head-moving shapes need POP, and follow in the next step.

-- (q₁,↓,q₂): only the state changes.
rule-stay-sound : ∀ b q₁ q₂ σ t
  → get σ vQ ≡ atm q₁ → get σ vT ≡ encT t → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b (rmov q₁ mvS q₂) ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂) × (get σ′ vT ≡ encT t) × Scratch-nil σ′ )
rule-stay-sound b q₁ q₂ σ t hQ hT (hL , hS , hR , hTmp , hW)
  with setState-sound q₁ q₂ σ hQ
... | σ′ , k , d , gQ , fr =
    σ′ , k , d , gQ
  , trans (fr vT (λ ())) hT
  , trans (fr vL (λ ())) hL , trans (fr vS (λ ())) hS
  , trans (fr vR (λ ())) hR , trans (fr vTmp (λ ())) hTmp
  , trans (fr vW (λ ())) hW

-- (q₁,(s₁,s₂),q₂): unpack the tape, exchange the symbol under the head by a
-- pair of reversible assignments (the first CLEARS, the second SETS), pack it
-- back, and change the state.
rule-sym-sound : ∀ b q₁ s₁ s₂ q₂ σ l r
  → get σ vQ ≡ atm q₁ → get σ vT ≡ encT (l , s₁ , r) → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b (rsym q₁ s₁ s₂ q₂) ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂) × (get σ′ vT ≡ encT (l , s₂ , r)) × Scratch-nil σ′ )
rule-sym-sound b q₁ s₁ s₂ q₂ σ l r hQ hT (hL , hS , hR , hTmp , hW)
  with unpack-sound σ l s₁ r hT hL hS hR hTmp
... | σ₁ , _ , dU , g1L , g1S , g1R , g1T , g1Tmp , f1
  with pack-sound (set (set σ₁ vS nil) vS (atm s₂)) l s₂ r
         (trans (get-set-≢ (set σ₁ vS nil) vS vL (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vL nil (λ ())) g1L))
         (get-set-≡ (set σ₁ vS nil) vS (atm s₂))
         (trans (get-set-≢ (set σ₁ vS nil) vS vR (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vR nil (λ ())) g1R))
         (trans (get-set-≢ (set σ₁ vS nil) vS vT (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vT nil (λ ())) g1T))
         (trans (get-set-≢ (set σ₁ vS nil) vS vTmp (atm s₂) (λ ()))
                (trans (get-set-≢ σ₁ vS vTmp nil (λ ())) g1Tmp))
... | σ₄ , _ , dP , g4T , g4L , g4S , g4R , g4Tmp , f4
  with setState-sound q₁ q₂ σ₄ q1-at-σ₄
  where
  σ₂ σ₃ : Store
  σ₂ = set σ₁ vS nil
  σ₃ = set σ₂ vS (atm s₂)
  q1-at-σ₄ : get σ₄ vQ ≡ atm q₁
  q1-at-σ₄ = trans (f4 vQ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
             (trans (get-set-≢ σ₂ vS vQ (atm s₂) (λ ()))
             (trans (get-set-≢ σ₁ vS vQ nil (λ ()))
                    (trans (f1 vQ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hQ)))
... | σ₅ , _ , dS , g5Q , f5 =
    σ₅ , _
  , e-seq dU (e-seq e1 (e-seq e2 (e-seq dP dS)))
  , g5Q
  , trans (f5 vT (λ ())) g4T
  , trans (f5 vL (λ ())) g4L , trans (f5 vS (λ ())) g4S
  , trans (f5 vR (λ ())) g4R , trans (f5 vTmp (λ ())) g4Tmp
  , trans (f5 vW (λ ())) vW-at-σ₄
  where
  σ₂ σ₃ : Store
  σ₂ = set σ₁ vS nil
  σ₃ = set σ₂ vS (atm s₂)
  e1 : (vS ^= opd (cst (atm s₁))) ⊢ σ₁ ⇒ σ₂ ∣ 1
  e1 = e-ass refl (subst (λ z → rupd z (atm s₁) ≡ just nil) (sym g1S)
                         (rupd-self (atm s₁)))
  e2 : (vS ^= opd (cst (atm s₂))) ⊢ σ₂ ⇒ σ₃ ∣ 1
  e2 = e-ass refl (subst (λ z → rupd z (atm s₂) ≡ just (atm s₂))
                         (sym (get-set-≡ σ₁ vS nil)) refl)
  vW-at-σ₄ : get σ₄ vW ≡ nil
  vW-at-σ₄ = trans (f4 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
             (trans (get-set-≢ σ₂ vS vW (atm s₂) (λ ()))
             (trans (get-set-≢ σ₁ vS vW nil (λ ()))
                    (trans (f1 vW (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hW)))

-- (q₁,←,q₂): move the head left, then change the state.
rule-left-sound : ∀ b q₁ q₂ σ l x r
  → NoTrailB b l
  → get σ vQ ≡ atm q₁ → get σ vT ≡ encT (l , x , r) → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b (rmov q₁ mvL q₂) ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂)
      × (get σ′ vT ≡ encT (movel b (l , x , r)))
      × Scratch-nil σ′ )
rule-left-sound b q₁ q₂ σ l x r ntl hQ hT sn
  with movel-sound b σ l x r ntl hT sn
... | σ₁ , _ , dM , g1T , (g1L , g1S , g1R , g1Tmp , g1W) , f1
  with setState-sound q₁ q₂ σ₁
         (trans (f1 vQ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2 =
    σ₂ , _ , e-seq dM dS , g2Q
  , trans (f2 vT (λ ())) g1T
  , ( trans (f2 vL (λ ())) g1L , trans (f2 vS (λ ())) g1S
    , trans (f2 vR (λ ())) g1R , trans (f2 vTmp (λ ())) g1Tmp
    , trans (f2 vW (λ ())) g1W )

-- (q₁,→,q₂): move the head right, then change the state.  `Step` states the
-- right move by the converse of movel; `movel-mover` says the tape produced
-- here is exactly the one that converse asks for.
rule-right-sound : ∀ b q₁ q₂ σ l x r
  → NoTrailB b r
  → get σ vQ ≡ atm q₁ → get σ vT ≡ encT (l , x , r) → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b (rmov q₁ mvR q₂) ⊢ σ ⇒ σ′ ∣ k)
      × (get σ′ vQ ≡ atm q₂)
      × (get σ′ vT ≡ encT (mover b (l , x , r)))
      × Scratch-nil σ′
      × (movel b (mover b (l , x , r)) ≡ (l , x , r)) )
rule-right-sound b q₁ q₂ σ l x r ntr hQ hT sn
  with mover-sound b σ l x r ntr hT sn
... | σ₁ , _ , dM , g1T , (g1L , g1S , g1R , g1Tmp , g1W) , f1
  with setState-sound q₁ q₂ σ₁
         (trans (f1 vQ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) hQ)
... | σ₂ , _ , dS , g2Q , f2 =
    σ₂ , _ , e-seq dM dS , g2Q
  , trans (f2 vT (λ ())) g1T
  , ( trans (f2 vL (λ ())) g1L , trans (f2 vS (λ ())) g1S
    , trans (f2 vR (λ ())) g1R , trans (f2 vTmp (λ ())) g1Tmp
    , trans (f2 vW (λ ())) g1W )
  , movel-mover b l x r ntr

------------------------------------------------------------------------
-- 10.  LEMMA 1 OF THE LETTER, PROVED.
--
--   c ⇒_d c′  ⟹  C⟦d̲⟧ c̄ = c̄′
--
-- The translated rule, run on a store holding c, terminates on a store
-- holding c′ with the scratch variables clear again — so it can be run
-- again, which is what the main loop needs.
--
-- `Step` bundles the rule membership with the move; `StepBy` names the rule
-- that was used, which is what a per-rule statement has to talk about.

lemma1 : ∀ b d q t q′ t′ σ
  → StepBy b d (q , t) (q′ , t′)
  → TapeOK b t → TapeOK b t′
  → HoldsConf (q , t) σ → Scratch-nil σ
  → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
      ( (ruleC b d ⊢ σ ⇒ σ′ ∣ k) × HoldsConf (q′ , t′) σ′ × Scratch-nil σ′ )

lemma1 b _ q _ q′ _ σ (sb-sym {s = s} {s′ = s′} {l = l} {r = r}) _ _ (hQ , hT) sn
  with rule-sym-sound b q s s′ q′ σ l r hQ hT sn
... | σ′ , k , d , gQ , gT , sn′ = σ′ , k , d , (gQ , gT) , sn′

lemma1 b _ q _ q′ _ σ (sb-lft {l = l} {x = x} {r = r}) (ntl , _) _ (hQ , hT) sn
  with rule-left-sound b q q′ σ l x r ntl hQ hT sn
... | σ′ , k , d , gQ , gT , sn′ = σ′ , k , d , (gQ , gT) , sn′

lemma1 b _ q _ q′ _ σ sb-sty _ _ (hQ , hT) sn
  with rule-stay-sound b q q′ σ _ hQ hT sn
... | σ′ , k , d , gQ , gT , sn′ = σ′ , k , d , (gQ , gT) , sn′

lemma1 b _ q _ q′ _ σ (sb-rgt {l = l} {x = x} {r = r} {l′} {x′} {r′} em)
       (_ , ntr) (ntl′ , _) (hQ , hT) sn
  with rule-right-sound b q q′ σ l x r ntr hQ hT sn
... | σ′ , k , d , gQ , gT , sn′ , _ =
  σ′ , k , d , (gQ , subst (λ z → get σ′ vT ≡ encT z) t′-is gT) , sn′
  where
  -- the successor tape is exactly what MOVER computed: apply mover to the
  -- step's own equation and use that mover undoes movel on canonical tapes.
  t′-is : mover b (l , x , r) ≡ (l′ , x′ , r′)
  t′-is = trans (sym (cong (mover b) em)) (mover-movel b l′ x′ r′ ntl′)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- 11.  THEOREM 2 of the letter, as a statement: R-WHILE is r-Turing
-- complete.
--
--   r′ = ⟦T⟧^TM r  ⟹  r̄′ = ⟦T̲⟧^R-WHILE r̄
--
-- Stated existentially over the program, so that it does not presuppose any
-- particular translation: for every RTM there IS an R-WHILE program (a
-- first-order `Cmd`) that simulates it.  The output condition asks that R′
-- hold the encoded result and every other variable be nil — the letter's
-- "the rest of main only initialises, swaps and clears to nil".

AllNilBut : ℕ → Store → Set
AllNilBut x σ = ∀ y → ¬ (y ≡ x) → get σ y ≡ nil

inStore : List ℕ → Store
inStore r = set [] vIn (encL r)

rTuringComplete : Set
rTuringComplete =
  ∀ (M : RTM) → IsRTM M
  → Σ[ C ∈ Cmd ] ( ∀ r r′
      → Step* M (q-s M , ([] , blank M , r)) (q-f M , ([] , blank M , r′))
      → Σ[ σ′ ∈ Store ] Σ[ k ∈ ℕ ]
          ( (C ⊢ inStore r ⇒ σ′ ∣ k) × (get σ′ vOut ≡ encL r′) × AllNilBut vOut σ′ ) )
