{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Part of the r-Turing completeness development; see RWhileRTM.agda
-- for the overview.  Split into several modules so that Agda's peak
-- memory stays bounded (one module held all of it and needed 47 GB).
------------------------------------------------------------------------

module RWhileRTM1 where

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
