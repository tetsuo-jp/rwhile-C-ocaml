{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick P5: the program-level simulation.
--
-- `RWhileSIStep` proved, case by case, that the dispatch body STEP realises
-- every machine step.  Here those cases are composed ALONG THE OBJECT
-- DERIVATION -- the same induction as `RWhileSIMach.sim`, but at the level
-- of R-WHILE runs -- so that the interpreter's main loop
--
--     SI = from (=? Cd' nil) do skip loop STEP until (=? Cd nil)
--
-- gets a `Rest` derivation for the whole run.  Doing the induction on the
-- object derivation (rather than on machine states) is what makes the
-- well-formedness side conditions available: `Wf c` (every assignment obeys
-- X ∉ Vars(E)) and `InR c σ` (every variable is a cell of the store) come
-- from the induction hypothesis, so no separate machine-state invariant is
-- needed.
--
-- `PChain` is the composable form of the loop's iteration chain (a `Rest`
-- cannot be concatenated in the middle: its `r-exit` demands that the exit
-- test hold).  `pc→rest` converts once, at the end.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSISim where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤
        ; m≤m+n; m≤n+m; +-assoc; +-comm)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime
open import RWhileSIEnc
open import RWhileSIMac using (iCd; iDn)
open import RWhileSIRun
open import RWhileSIStep

------------------------------------------------------------------------
-- The interpreter, as a program: the main loop around STEP.

emptyDone emptyTodo : Exp
emptyDone = eqE (var iDn) (cst nil)      -- =? Cd' nil   (loop entry test)
emptyTodo = eqE (var iCd) (cst nil)      -- =? Cd  nil   (loop exit test)

SI : Cmd
SI = loop emptyDone skip STEP emptyTodo

-- the two tests at a machine state: they only look at the two stacks
todo-cons : ∀ h t dn σ → evalT (embM (h ∙ t) dn σ) emptyTodo ≡ just false
todo-cons h t dn σ = refl

todo-nil : ∀ dn σ → evalT (embM nil dn σ) emptyTodo ≡ just true
todo-nil dn σ = refl

done-cons : ∀ td h d σ → evalT (embM td (h ∙ d) σ) emptyDone ≡ just false
done-cons td h d σ = refl

done-nil : ∀ td σ → evalT (embM td nil σ) emptyDone ≡ just true
done-nil td σ = refl

------------------------------------------------------------------------
-- Composable iteration chains.

data PChain : Store → Store → ℕ → Set where
  []   : ∀ {s} → PChain s s 0
  cons : ∀ {s t u j n}
       → evalT s emptyTodo ≡ just false
       → STEP ⊢ s ⇒ t ∣ j
       → evalT t emptyDone ≡ just false
       → PChain t u n
       → PChain s u (j + 1 + n)

pchain-++ : ∀ {s t u m n} → PChain s t m → PChain t u n → PChain s u (m + n)
pchain-++ []                     ys = ys
pchain-++ (cons {j = j} {n = n₁} ex st en xs) ys =
  subst (PChain _ _) (sym (+-assoc (j + 1) n₁ _)) (cons ex st en (pchain-++ xs ys))

-- a chain with a cost bound
record PC (s t : Store) (B : ℕ) : Set where
  constructor mkPC
  field
    pcost : ℕ
    pchain : PChain s t pcost
    pbnd : pcost ≤ B

open PC public

pcNil : ∀ {s} → PC s s 0
pcNil = mkPC 0 [] z≤n

pcStep : ∀ {s t u J N}
       → evalT s emptyTodo ≡ just false
       → Run STEP s t J
       → evalT t emptyDone ≡ just false
       → PC t u N
       → PC s u (J + 1 + N)
pcStep ex r en c =
  mkPC _ (cons ex (run r) en (pchain c))
       (+-mono-≤ (+-monoˡ-≤ 1 (bnd r)) (pbnd c))

pcApp : ∀ {s t u M N} → PC s t M → PC t u N → PC s u (M + N)
pcApp c₁ c₂ = mkPC _ (pchain-++ (pchain c₁) (pchain c₂)) (+-mono-≤ (pbnd c₁) (pbnd c₂))

pcWeak : ∀ {s t M N} → M ≤ N → PC s t M → PC s t N
pcWeak le c = mkPC (pcost c) (pchain c) (≤-trans (pbnd c) le)

------------------------------------------------------------------------
-- Converting a finished chain into the loop's `Rest` derivation.

pc→rest : ∀ {s t B} → PC s t B → evalT t emptyTodo ≡ just true
        → Σ[ j ∈ ℕ ] (Rest emptyDone skip STEP emptyTodo s t j × j ≤ B)
pc→rest c fin = pcost c , go (pchain c) fin , pbnd c
  where
    go : ∀ {s t n} → PChain s t n → evalT t emptyTodo ≡ just true
       → Rest emptyDone skip STEP emptyTodo s t n
    go [] fin = r-exit fin
    go (cons ex st en xs) fin = r-iter ex st en e-skip (go xs fin)

------------------------------------------------------------------------
-- The uniform per-step constant `CC` and the slack `SL`.
--
-- `CC M` is the budget one object step gets; `SL M` is the slack that pays
-- for the loop's exit step (which the object semantics charges nothing for).
-- Both are sums of case bounds plus a literal, chosen so that the
-- inequalities the composition needs hold by monotonicity alone.

SL : ℕ → ℕ
SL M = lpDStep M + (lpAStep M + 200)

CCy : ℕ → ℕ
CCy M = lpAStep M + (assStep M + (condStep M + (condEStep M + 300)))

CC : ℕ → ℕ
CC M = SL M + CCy M

private
  le300 : ∀ M → 300 ≤ CCy M
  le300 M = ≤-trans (≤-trans (≤-trans (m≤n+m 300 (condEStep M)) (m≤n+m _ (condStep M)))
                             (m≤n+m _ (assStep M)))
                    (m≤n+m _ (lpAStep M))

  le200 : ∀ M → 200 ≤ SL M
  le200 M = ≤-trans (m≤n+m 200 (lpAStep M)) (m≤n+m _ (lpDStep M))

  lit300 : ∀ (n : ℕ) {p : True (n ≤? 300)} → n ≤ 300
  lit300 n {p} = toWitness p

  lit200 : ∀ (n : ℕ) {p : True (n ≤? 200)} → n ≤ 200
  lit200 n {p} = toWitness p

  lit : ∀ (n : ℕ) {p : True (n ≤? 300)} M → n ≤ CCy M
  lit n {p} M = ≤-trans (toWitness p) (le300 M)

  litS : ∀ (n : ℕ) {p : True (n ≤? 200)} M → n ≤ lpAStep M + 200
  litS n {p} M = ≤-trans (toWitness p) (m≤n+m 200 (lpAStep M))

-- X + SL ≤ CC follows from X ≤ CCy
withSL : ∀ {X} M → X ≤ CCy M → X + SL M ≤ CC M
withSL {X} M le = ≤-trans (+-monoˡ-≤ (SL M) le) (≤-reflexive (+-comm (CCy M) (SL M)))

------------------------------------------------------------------------
-- The seven inequalities the composition needs.

condSkip : ∀ M → 35 + SL M ≤ CC M
condSkip M = withSL M (lit 35 M)

condAss : ∀ M → assStep M + 1 + SL M ≤ CC M
condAss M = withSL M
  (≤-trans (+-monoʳ-≤ (assStep M)
              (≤-trans (lit300 1)
                       (≤-trans (m≤n+m 300 (condEStep M)) (m≤n+m _ (condStep M)))))
           (m≤n+m _ (lpAStep M)))

condSeq : ∀ M → 163 ≤ CC M + SL M
condSeq M = ≤-trans (lit 163 M) (≤-trans (m≤n+m _ (SL M)) (m≤m+n _ (SL M)))

condCond : ∀ M → condStep M + condEStep M + 2 ≤ CC M
condCond M =
  ≤-trans (≤-reflexive (+-assoc (condStep M) (condEStep M) 2))
    (≤-trans (+-monoʳ-≤ (condStep M) (+-monoʳ-≤ (condEStep M) (lit300 2)))
      (≤-trans (m≤n+m _ (assStep M))
        (≤-trans (m≤n+m _ (lpAStep M)) (m≤n+m _ (SL M)))))

condLoop : ∀ M → 56 + lpAStep M + SL M ≤ CC M
condLoop M = withSL M
  (≤-trans (≤-reflexive (+-comm 56 (lpAStep M)))
           (+-monoʳ-≤ (lpAStep M)
             (≤-trans (lit300 56)
                      (≤-trans (m≤n+m 300 (condEStep M))
                        (≤-trans (m≤n+m _ (condStep M)) (m≤n+m _ (assStep M)))))))

condExit : ∀ M → lpDStep M + 59 ≤ SL M
condExit M = +-monoʳ-≤ (lpDStep M) (litS 59 M)

condIter : ∀ M → lpDStep M + lpAStep M + 175 ≤ SL M + SL M
condIter M =
  ≤-trans (≤-reflexive (+-assoc (lpDStep M) (lpAStep M) 175))
    (≤-trans (+-monoʳ-≤ (lpDStep M) (+-monoʳ-≤ (lpAStep M) (lit200 175)))
             (m≤m+n _ (SL M)))

------------------------------------------------------------------------
-- THE COMPOSITION.  Along the object derivation, the case lemmas of
-- RWhileSIStep are strung into one iteration chain of the main loop.
-- `Wf c` and `InR c σ` come from the induction hypothesis, and the store's
-- length is invariant, so a single constant `CC M` works throughout.

open import RWhileSIWf
open import RWhileSIArith
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Properties using (*-identityʳ; *-suc; *-distribˡ-+; *-distribʳ-+; *-monoʳ-≤; +-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

-- one dispatch step, as a chain of length one
one : ∀ {s t B} → evalT s emptyTodo ≡ just false → Run STEP s t B
    → evalT t emptyDone ≡ just false
    → Σ[ j ∈ ℕ ] (PChain s t j × j ≤ suc B)
one {B = B} ex r en =
  _ , cons ex (run r) en []
    , ≤-trans (≤-reflexive (trans (+-identityʳ (cost r + 1)) (+-comm (cost r) 1)))
              (s≤s (bnd r))

-- reading a test's value off its truth
evalT-t : ∀ σ e → evalT σ e ≡ just true → Σ[ v ∈ V ] (evalE σ e ≡ just v × isTrue v ≡ true)
evalT-t σ e et with evalE σ e
... | just v = v , refl , just-injective et

evalT-f : ∀ σ e → evalT σ e ≡ just false → Σ[ v ∈ V ] (evalE σ e ≡ just v × isTrue v ≡ false)
evalT-f σ e et with evalE σ e
... | just v = v , refl , just-injective et

isNil : ∀ v → isTrue v ≡ false → v ≡ nil
isNil nil     _  = refl
isNil (atm _) ()
isNil (_ ∙ _) ()

-- transporting an "in range" fact along a store-length equation
cast≤ : ∀ {a m n} → n ≡ m → a ≤ m → a ≤ n
cast≤ eq le = subst (_ ≤_) (sym eq) le

-- the true branch of a conditional: the marker the exit case expects is
-- `boolV true`, which `step-cond-true` produces as `boolV (isTrue v)`
condT-run : ∀ (σ : Store) (e : Exp) (v : V) → evalE σ e ≡ just v → isTrue v ≡ true
          → vmaxᵉ e ≤ length σ → ∀ cc dc fc cd dn
          → Run STEP (embM ((atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd) dn σ)
                     (embM (cc ∙ ((atm t-condE ∙ (nil ∙ nil)) ∙ cd))
                           ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn) σ)
                     (condStep (length σ))
condT-run σ e v ev tv vm cc dc fc cd dn =
  subst (λ b → Run STEP (embM ((atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ cd) dn σ)
                        (embM (cc ∙ ((atm t-condE ∙ boolV b) ∙ cd))
                              ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (cc ∙ (dc ∙ fc)))) ∙ dn) σ)
                        (condStep (length σ)))
        tv (step-cond-true σ e v ev tv vm cc dc fc cd dn)

simP : ∀ {c σ τ k} (M : ℕ) → length σ ≡ M → c ⊢ σ ⇒ τ ∣ k → Wf c → InR c σ → ∀ cd dn
     → Σ[ j ∈ ℕ ] (PChain (embM (⌜ c ⌝ ∙ cd) dn σ) (embM cd (⌜ c ⌝ ∙ dn) τ) j
                   × j + SL M ≤ CC M * k)

simPR : ∀ {e D L f σ τ n} (M : ℕ) → length σ ≡ M
      → Rest e D L f σ τ n → Wf D → Wf L → InR (loop e D L f) σ → ∀ cd dn
      → Σ[ j ∈ ℕ ]
          (PChain (embM ((atm t-lpD ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
                        (⌜ D ⌝ ∙ ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)) σ)
                  (embM cd (⌜ loop e D L f ⌝ ∙ dn) τ) j
           × j ≤ CC M * n + SL M)

simP {σ = σ} M refl e-skip wf ir cd dn =
  proj₁ h , proj₁ (proj₂ h)
  , ≤-trans (+-monoˡ-≤ (SL (length σ)) (proj₂ (proj₂ h)))
      (≤-trans (condSkip (length σ)) (≤-reflexive (sym (*-identityʳ (CC (length σ))))))
  where
    h = one refl (step-skip cd dn σ) refl

simP {σ = σ} M refl (e-ass {x = x} {e = e} ev ru) (wf-ass ni) ir cd dn =
  proj₁ h , proj₁ (proj₂ h) , lemAss {S = SL (length σ)} {C = CC (length σ)} (proj₂ (proj₂ h)) (condAss (length σ))
  where
    h = one refl (step-ass σ x e _ _ ev ru
                    (ass-in-range {x} {e} {σ} ir) (inR-assE {x} {e} {σ} ir) ni cd dn) refl

simP {σ = σ} M refl (e-seq {c = c} {d = d} {t = t} {k = k} {l = l} d₁ d₂) (wf-seq w₁ w₂) ir cd dn =
  _ , pchain-++ (proj₁ (proj₂ h₁))
        (pchain-++ (proj₁ (proj₂ h₂))
          (pchain-++ (proj₁ (proj₂ h₃)) (proj₁ (proj₂ h₄))))
    , lemSeq {S = SL (length σ)} {C = CC (length σ)} {k = k} {l = l} (proj₂ (proj₂ h₁)) (proj₂ (proj₂ h₄))
             (proj₂ (proj₂ h₂)) (proj₂ (proj₂ h₃)) (condSeq (length σ))
  where
    irc = inR-seqˡ {c} {d} {σ} ir
    lt : length t ≡ length σ
    lt = ⇒-length irc d₁
    h₁ = one refl (step-seq ⌜ c ⌝ ⌜ d ⌝ cd dn σ) refl
    h₂ = simP (length σ) refl d₁ w₁ irc
              (⌜ d ⌝ ∙ ((atm t-seqE ∙ nil) ∙ cd)) ((atm t-seqB ∙ nil) ∙ dn)
    h₃ = simP (length σ) lt d₂ w₂ (cast≤ lt (inR-seqʳ {c} {d} {σ} ir))
              ((atm t-seqE ∙ nil) ∙ cd) (⌜ c ⌝ ∙ ((atm t-seqB ∙ nil) ∙ dn))
    h₄ = one refl (step-seqE ⌜ c ⌝ ⌜ d ⌝ cd dn _) refl

simP {σ = σ} M refl (e-then {e = e} {c = c} {d = d} {f = f} {t = t} {k = k} te dc tf)
     (wf-cond w₁ w₂) ir cd dn =
  _ , pchain-++ (proj₁ (proj₂ h₁)) (pchain-++ (proj₁ (proj₂ h₂)) (proj₁ (proj₂ h₃)))
    , lemCond {S = SL (length σ)} {C = CC (length σ)} {k = k} (proj₂ (proj₂ h₁)) (proj₂ (proj₂ h₃)) (proj₂ (proj₂ h₂)) (condCond (length σ))
  where
    irc = inR-condˡ {e} {c} {d} {f} {σ} ir
    lt : length t ≡ length σ
    lt = ⇒-length irc dc
    tv = evalT-t σ e te
    tf′ = evalT-t t f tf
    h₁ = one refl (condT-run σ e (proj₁ tv) (proj₁ (proj₂ tv)) (proj₂ (proj₂ tv))
                     (inR-condT {e} {c} {d} {f} {σ} ir) ⌜ c ⌝ ⌜ d ⌝ ⌜ f ⌝ᵉ cd dn) refl
    h₂ = simP (length σ) refl dc w₁ irc
              ((atm t-condE ∙ (nil ∙ nil)) ∙ cd)
              ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
    h₃ = one refl (rWeak (≤-reflexive (cong condEStep lt))
                     (step-condE-t t f (proj₁ tf′) (proj₁ (proj₂ tf′)) (proj₂ (proj₂ tf′))
                        (cast≤ lt (inR-condF {e} {c} {d} {f} {σ} ir))
                        ⌜ e ⌝ᵉ ⌜ c ⌝ ⌜ d ⌝ cd dn)) refl

simP {σ = σ} M refl (e-else {e = e} {c = c} {d = d} {f = f} {t = t} {k = k} te dd tf)
     (wf-cond w₁ w₂) ir cd dn =
  _ , pchain-++ (proj₁ (proj₂ h₁)) (pchain-++ (proj₁ (proj₂ h₂)) (proj₁ (proj₂ h₃)))
    , lemCond {S = SL (length σ)} {C = CC (length σ)} {k = k} (proj₂ (proj₂ h₁)) (proj₂ (proj₂ h₃)) (proj₂ (proj₂ h₂)) (condCond (length σ))
  where
    ird = inR-condʳ {e} {c} {d} {f} {σ} ir
    lt : length t ≡ length σ
    lt = ⇒-length ird dd
    fv = evalT-f σ e te
    ff = evalT-f t f tf
    evn : evalE σ e ≡ just nil
    evn = trans (proj₁ (proj₂ fv)) (cong just (isNil _ (proj₂ (proj₂ fv))))
    h₁ = one refl (step-cond-f σ e evn (inR-condT {e} {c} {d} {f} {σ} ir)
                     ⌜ c ⌝ ⌜ d ⌝ ⌜ f ⌝ᵉ cd dn) refl
    h₂ = simP (length σ) refl dd w₂ ird
              ((atm t-condE ∙ nil) ∙ cd)
              ((atm t-condB ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
    h₃ = one refl (rWeak (≤-reflexive (cong condEStep lt))
                     (step-condE-f t f (proj₁ ff) (proj₁ (proj₂ ff)) (proj₂ (proj₂ ff))
                        (cast≤ lt (inR-condF {e} {c} {d} {f} {σ} ir))
                        ⌜ e ⌝ᵉ ⌜ c ⌝ ⌜ d ⌝ cd dn)) refl

simP {σ = σ} M refl (e-loop {e = e} {D = D} {L = L} {f = f} {t = t} {k = k} {n = n} te dD rest)
     (wf-loop w₁ w₂) ir cd dn =
  _ , pchain-++ (proj₁ (proj₂ h₁))
        (pchain-++ (proj₁ (proj₂ h₂))
          (pchain-++ (proj₁ (proj₂ h₃)) (proj₁ (proj₂ h₄))))
    , lemLoop {S = SL (length σ)} {C = CC (length σ)} {k = k} {n = n} (proj₂ (proj₂ h₁)) (proj₂ (proj₂ h₂))
              (proj₂ (proj₂ h₃)) (proj₂ (proj₂ h₄)) (condLoop (length σ))
  where
    irD = inR-loopˡ {e} {D} {L} {f} {σ} ir
    lt : length t ≡ length σ
    lt = ⇒-length irD dD
    tv = evalT-t σ e te
    h₁ = one refl (step-loop ⌜ e ⌝ᵉ ⌜ D ⌝ ⌜ L ⌝ ⌜ f ⌝ᵉ cd dn σ) refl
    h₂ = one refl (step-lpA-t σ e (proj₁ tv) (proj₁ (proj₂ tv)) (proj₂ (proj₂ tv))
                     (inR-loopT {e} {D} {L} {f} {σ} ir) ⌜ D ⌝ ⌜ L ⌝ ⌜ f ⌝ᵉ cd dn) refl
    h₃ = simP (length σ) refl dD w₁ irD
              ((atm t-lpD ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
    h₄ = simPR (length σ) lt rest w₁ w₂ (cast≤ lt ir) cd dn

simPR {e = e} {D = D} {L = L} {f = f} {σ = σ} M refl (r-exit tf) wfD wfL ir cd dn =
  _ , pchain-++ (proj₁ (proj₂ h₁)) (proj₁ (proj₂ h₂))
    , lemExit {S = SL (length σ)} {C = CC (length σ)} (proj₂ (proj₂ h₁)) (proj₂ (proj₂ h₂)) (condExit (length σ))
  where
    tv = evalT-t σ f tf
    h₁ = one refl (step-lpD-t σ f (proj₁ tv) (proj₁ (proj₂ tv)) (proj₂ (proj₂ tv))
                     (inR-loopF {e} {D} {L} {f} {σ} ir) ⌜ e ⌝ᵉ ⌜ D ⌝ ⌜ L ⌝ cd dn) refl
    h₂ = one refl (step-lpZ ⌜ e ⌝ᵉ ⌜ D ⌝ ⌜ L ⌝ ⌜ f ⌝ᵉ cd dn σ) refl

simPR {e = e} {D = D} {L = L} {f = f} {σ = σ} M refl
      (r-iter {x = x} {y = y} {k = k} {m = m} {n = n} ff dL fe dD rest) wfD wfL ir cd dn =
  _ , pchain-++ (proj₁ (proj₂ h₁))
        (pchain-++ (proj₁ (proj₂ h₂))
          (pchain-++ (proj₁ (proj₂ h₃))
            (pchain-++ (proj₁ (proj₂ h₄))
              (pchain-++ (proj₁ (proj₂ h₅))
                (pchain-++ (proj₁ (proj₂ h₆)) (proj₁ (proj₂ h₇)))))))
    , lemIter {S = SL (length σ)} {C = CC (length σ)} {k = k} {m = m} {n = n} (proj₂ (proj₂ h₁)) (proj₂ (proj₂ h₂)) (proj₂ (proj₂ h₄)) (proj₂ (proj₂ h₅))
              (proj₂ (proj₂ h₃)) (proj₂ (proj₂ h₆)) (proj₂ (proj₂ h₇)) (condIter (length σ))
  where
    fv = evalT-f σ f ff
    evn : evalE σ f ≡ just nil
    evn = trans (proj₁ (proj₂ fv)) (cong just (isNil _ (proj₂ (proj₂ fv))))
    irL = inR-loopʳ {e} {D} {L} {f} {σ} ir
    lx : length x ≡ length σ
    lx = ⇒-length irL dL
    irx : InR (loop e D L f) x
    irx = cast≤ lx ir
    irDx = inR-loopˡ {e} {D} {L} {f} {x} irx
    ly : length y ≡ length x
    ly = ⇒-length irDx dD
    fev = evalT-f x e fe
    evne : evalE x e ≡ just nil
    evne = trans (proj₁ (proj₂ fev)) (cong just (isNil _ (proj₂ (proj₂ fev))))
    h₁ = one refl (step-lpD-f σ f evn (inR-loopF {e} {D} {L} {f} {σ} ir)
                     ⌜ e ⌝ᵉ ⌜ D ⌝ ⌜ L ⌝ cd dn) refl
    h₂ = one refl (step-lpB ⌜ e ⌝ᵉ ⌜ D ⌝ ⌜ L ⌝ ⌜ f ⌝ᵉ cd dn σ) refl
    h₃ = simP (length σ) refl dL wfL irL
              ((atm t-lpC ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              ((atm t-lpB ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
    h₄ = one refl (step-lpC ⌜ e ⌝ᵉ ⌜ D ⌝ ⌜ L ⌝ ⌜ f ⌝ᵉ cd dn x) refl
    h₅ = one refl (rWeak (≤-reflexive (cong lpAStep lx))
                     (step-lpA-f x e evne (cast≤ lx (inR-loopT {e} {D} {L} {f} {σ} ir))
                        ⌜ D ⌝ ⌜ L ⌝ ⌜ f ⌝ᵉ cd dn)) refl
    h₆ = simP (length σ) lx dD wfD irDx
              ((atm t-lpD ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              ((atm t-lpA ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
    h₇ = simPR (length σ) (trans ly lx) rest wfD wfL (cast≤ (trans ly lx) ir) cd dn

------------------------------------------------------------------------
-- THE THEOREM, WITHOUT ASSUMPTIONS.
--
-- The self-interpreter SI is one R-WHILE program.  Started with the todo
-- stack holding the encoded object program and an empty done stack, it
-- terminates with the two stacks swapped -- the object program is
-- REASSEMBLED on the done stack, so `SI` really is a self-interpreter and
-- not a program that consumes its input -- and with the object store
-- transformed exactly as the object semantics prescribes.
--
-- Its cost is at most `(CC M + 2) * k`, where `k` is the object program's
-- own cost and `M` the number of store cells: a LINEAR-TIME simulation
-- whose constant depends only on the store size (via the `Vl` walk).

si-linear : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
          → Σ[ j ∈ ℕ ] (SI ⊢ embM (⌜ c ⌝ ∙ nil) nil σ ⇒ embM nil (⌜ c ⌝ ∙ nil) τ ∣ j
                        × j ≤ (CC (length σ) + 2) * k)
si-linear {c} {σ} {τ} {k} wf ir d =
  _ , e-loop refl e-skip (proj₁ (proj₂ r))
    , ≤-trans (+-monoʳ-≤ 2 (proj₂ (proj₂ r)))
        (≤-trans (≤-reflexive (+-comm 2 (CC (length σ) * k)))
          (≤-trans (+-monoʳ-≤ (CC (length σ) * k) two≤)
                   (≤-reflexive (sym (*-distribʳ-+ k (CC (length σ)) 2)))))
  where
    h = simP (length σ) refl d wf ir nil nil
    pc : PC (embM (⌜ c ⌝ ∙ nil) nil σ) (embM nil (⌜ c ⌝ ∙ nil) τ) (CC (length σ) * k)
    pc = mkPC (proj₁ h) (proj₁ (proj₂ h))
              (≤-trans (m≤m+n (proj₁ h) (SL (length σ))) (proj₂ (proj₂ h)))
    r = pc→rest pc refl
    two≤ : 2 ≤ 2 * k
    two≤ = *-monoʳ-≤ 2 (cost-pos d)
