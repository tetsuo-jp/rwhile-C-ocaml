{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The self-interpreter's MACHINE: a tail-recursive agenda machine over
-- encoded R-WHILE programs, and its simulation theorem.
--
-- This is the abstraction of `examples/ri.rwhile`'s main loop
--
--     from (=? Cd' nil) loop STEP(Cd,Cd') until (=? Cd nil)
--
-- with the same data layout: a TODO stack `td` of tasks, a DONE stack `dn`
-- (Bennett's history -- but a *reassembling* one, so that when the run ends
-- the done stack holds exactly the source program again: `ri` is
-- program-preserving), and the object store.  A task is either an encoded
-- command (a program node) or a runtime MARKER (a continuation).
--
-- Protocol (one dispatch case per tag; `A` = the node's argument):
--
--   skip           pop, push to done                                   1 step
--   x ^= e         evaluate e, reversibly update the store, push        1 step
--   c ; d          push ⌜c⌝ ⌜d⌝ (seqE) on todo, (seqB) on done          2 steps
--   seqE           pop ⌜d⌝ ⌜c⌝ (seqB) off done, push ⌜c;d⌝
--   if e C D f     evaluate e, push the taken branch + (condE b)        2 steps
--   condE b        check the exit assertion f ≡ b, reassemble
--   from e D L f   push ⌜D⌝ + (lpA true A)                              1 step
--   lpA fl A       pop ⌜D⌝ and the context record, test f,             1 step/iter
--                  continue with (lpB A) or exit with (lpZ A)
--   lpB A          push ⌜L⌝ + (lpC A)                                   1 step/iter
--   lpC A          pop ⌜L⌝ + record, push ⌜D⌝ + (lpA false A)           1 step/iter
--   lpZ A          exit: reassemble ⌜from e D L f⌝ onto done            1 step
--
-- THEOREM `sim`:  every terminating object run `c ⊢ σ ⇒ τ ∣ k` is simulated
-- by the machine in `n ≤ 4 * k` steps, ending with ⌜c⌝ on the done stack and
-- the object store updated -- i.e. the machine is a CORRECT, PROGRAM-PRESERVING
-- interpreter whose step count is LINEAR in the object program's.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIMach where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤
        ; m≤m+n; m≤n+m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime
open import RWhileSIEnc

------------------------------------------------------------------------
-- Decoding numerals and evaluating ENCODED expressions.

unnum : V → Maybe ℕ
unnum nil       = just zero
unnum (nil ∙ v) = unnum v >>=M λ n → just (suc n)
unnum _         = nothing

unnum-num : ∀ n → unnum (num n) ≡ just n
unnum-num zero    = refl
unnum-num (suc n) rewrite unnum-num n = refl

evalOV : Store → V → Maybe V
evalOV σ (atm 0 ∙ n) = unnum n >>=M λ x → just (get σ x)   -- t-var
evalOV σ (atm 1 ∙ v) = just v                              -- t-cst
evalOV _ _           = nothing

-- expressions are (tag . (operand1 . operand2)); unary forms ignore operand2
evalEV : Store → V → Maybe V
evalEV σ (atm 2 ∙ (a ∙ _)) = evalOV σ a                                        -- opd
evalEV σ (atm 3 ∙ (a ∙ b)) = evalOV σ a >>=M λ u → evalOV σ b >>=M λ v →
                             just (u ∙ v)                                      -- cons
evalEV σ (atm 4 ∙ (a ∙ _)) = evalOV σ a >>=M hdM                               -- hd
evalEV σ (atm 5 ∙ (a ∙ _)) = evalOV σ a >>=M tlM                               -- tl
evalEV σ (atm 6 ∙ (a ∙ b)) = evalOV σ a >>=M λ u → evalOV σ b >>=M λ v →
                             just (boolV (eqV u v))                            -- =?
evalEV σ (atm 7 ∙ (a ∙ _)) = evalOV σ a >>=M λ u → just (boolV (isCons u))    -- pair?
evalEV _ _                 = nothing

evalTV : Store → V → Maybe Bool
evalTV σ ec = evalEV σ ec >>=M λ v → just (isTrue v)

-- the encoded evaluator agrees with the source-level one
evalOV-ok : ∀ σ a → evalOV σ ⌜ a ⌝ᵒ ≡ just (evalO σ a)
evalOV-ok σ (var x) rewrite unnum-num x = refl
evalOV-ok σ (cst v) = refl

evalEV-ok : ∀ σ e → evalEV σ ⌜ e ⌝ᵉ ≡ evalE σ e
evalEV-ok σ (opd a)   = evalOV-ok σ a
evalEV-ok σ (cns a b) rewrite evalOV-ok σ a | evalOV-ok σ b = refl
evalEV-ok σ (hdE a)   rewrite evalOV-ok σ a = refl
evalEV-ok σ (tlE a)   rewrite evalOV-ok σ a = refl
evalEV-ok σ (eqE a b) rewrite evalOV-ok σ a | evalOV-ok σ b = refl
evalEV-ok σ (prE a)   rewrite evalOV-ok σ a = refl

evalTV-ok : ∀ σ e → evalTV σ ⌜ e ⌝ᵉ ≡ evalT σ e
evalTV-ok σ e rewrite evalEV-ok σ e with evalE σ e
... | just v  = refl
... | nothing = refl

------------------------------------------------------------------------
-- Machine states.

record MSt : Set where
  constructor ⟨_,_,_⟩
  field
    td : V          -- todo stack (encoded list of tasks)
    dn : V          -- done stack
    st : Store      -- the object store

------------------------------------------------------------------------
-- One machine step.  Tags: see RWhileSIEnc (skip 7, ass 8, seq 9, cond 10,
-- loop 11; markers seqB 12, seqE 13, condB 14, condE 15, loopB 16, lpA 17,
-- lpB 18, lpZ 19, lpC 20).

-- `step1 h r d s` : dispatch the head task `h`, with `r` the rest of the todo
-- stack, `d` the done stack and `s` the object store.  It returns the new todo
-- stack, the RECORD to be pushed on the done stack, the new done stack and the
-- new object store.  Factoring the push out this way makes "the done stack is
-- non-empty after a step" structural (`astep-dn` below) -- the invariant the
-- interpreter's main loop needs for its reversibility assertion.

step1 : V → V → V → Store → Maybe (V × V × V × Store)

-- skip
step1 (atm 7 ∙ nil) cd dn σ = just (cd , atm 7 ∙ nil , dn , σ)

-- x ^= e
step1 (atm 8 ∙ (nx ∙ ec)) cd dn σ =
  unnum nx >>=M λ x →
  evalEV σ ec >>=M λ v →
  rupd (get σ x) v >>=M λ u →
  just (cd , atm 8 ∙ (nx ∙ ec) , dn , set σ x u)

-- c ; d   (push both, plus the reassembly marker)
step1 (atm 9 ∙ (cc ∙ dc)) cd dn σ =
  just (cc ∙ (dc ∙ ((atm 13 ∙ nil) ∙ cd)) , atm 12 ∙ nil , dn , σ)

-- seqE : pop ⌜d⌝, ⌜c⌝ and the seqB record; push the reassembled node
step1 (atm 13 ∙ nil) cd (dc ∙ (cc ∙ ((atm 12 ∙ nil) ∙ dn))) σ =
  just (cd , atm 9 ∙ (cc ∙ dc) , dn , σ)

-- if e then C else D fi f
step1 (atm 10 ∙ (ec ∙ (cc ∙ (dc ∙ fc)))) cd dn σ =
  evalTV σ ec >>=M λ b →
  just ((if b then cc else dc) ∙ ((atm 15 ∙ boolV b) ∙ cd)
       , atm 14 ∙ (ec ∙ (cc ∙ (dc ∙ fc))) , dn , σ)

-- condE : check the exit assertion (its truth must equal the entry test's)
step1 (atm 15 ∙ bv) cd (bc ∙ ((atm 14 ∙ (ec ∙ (cc ∙ (dc ∙ fc)))) ∙ dn)) σ =
  evalTV σ fc >>=M λ b′ →
  if eqV (boolV b′) bv
    then just (cd , atm 10 ∙ (ec ∙ (cc ∙ (dc ∙ fc))) , dn , σ)
    else nothing

-- from e do D loop L until f : go to the lpA marker.  The ENTRY TEST is
-- checked there, BEFORE D runs, exactly as the semantics prescribes -- and
-- that is what makes the protocol implementable in R-WHILE: which arrival
-- this is (first or later) is recomputable from the entry test's truth
-- (true only on first entry), so no unerasable bit is needed.
step1 (atm 11 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd dn σ =
  just ((atm 17 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
       , atm 16 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)

-- lpA, first arrival (context record (loopB . A)): the entry test must HOLD
step1 (atm 17 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd ((atm 16 ∙ A) ∙ dn) σ =
  evalTV σ ec >>=M λ b →
  if b then just (Dc ∙ ((atm 6 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                 , atm 17 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)
       else nothing

-- lpA, later arrivals (context record (lpC . A)): the entry test must FAIL
-- (R-WHILE's loop reversibility assertion)
step1 (atm 17 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd ((atm 20 ∙ A) ∙ dn) σ =
  evalTV σ ec >>=M λ b →
  if b then nothing
       else just (Dc ∙ ((atm 6 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
                 , atm 17 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)

-- lpD : D has run -- test the exit condition and branch.  (Tag 6 is free in
-- the TASK tag space: 0-6 number operands and expressions, which never
-- appear as tasks.)
step1 (atm 6 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd (Dc′ ∙ ((atm 17 ∙ A) ∙ dn)) σ =
  evalTV σ fc >>=M λ b →
  just ((if b then (atm 19 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))))
              else (atm 18 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))))) ∙ cd
       , atm 6 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)

-- lpB : continue -- run L, then lpC
step1 (atm 18 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd ((atm 6 ∙ A) ∙ dn) σ =
  just (Lc ∙ ((atm 20 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd)
       , atm 18 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)

-- lpZ : exit -- reassemble the loop node onto the done stack
step1 (atm 19 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd ((atm 6 ∙ A) ∙ dn) σ =
  just (cd , atm 11 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)

-- lpC : the body has run -- back to lpA
step1 (atm 20 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) cd (Lc′ ∙ ((atm 18 ∙ A) ∙ dn)) σ =
  just ((atm 17 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc)))) ∙ cd
       , atm 20 ∙ (ec ∙ (Dc ∙ (Lc ∙ fc))) , dn , σ)

step1 _ _ _ _ = nothing

-- one machine step: split the todo stack, dispatch, push the record
astep : MSt → Maybe MSt
astep ⟨ t , d , σ ⟩ =
  hdM t >>=M λ h → tlM t >>=M λ r → step1 h r d σ >>=M λ q →
  just ⟨ proj₁ q , proj₁ (proj₂ q) ∙ proj₁ (proj₂ (proj₂ q)) , proj₂ (proj₂ (proj₂ q)) ⟩

------------------------------------------------------------------------
-- Machine runs: a chain of steps, with composition.

data Steps : MSt → MSt → ℕ → Set where
  []  : ∀ {m} → Steps m m 0
  _∷_ : ∀ {m m′ m″ n} → astep m ≡ just m′ → Steps m′ m″ n → Steps m m″ (suc n)

infixr 5 _∷_

steps-++ : ∀ {a b c m n} → Steps a b m → Steps b c n → Steps a c (m + n)
steps-++ []       ys = ys
steps-++ (x ∷ xs) ys = x ∷ steps-++ xs ys

-- weakening the step count (we only ever need an upper bound)
steps-≤ : ∀ {a b m n} → Steps a b m → m ≡ n → Steps a b n
steps-≤ xs refl = xs

------------------------------------------------------------------------
-- The simulation theorem.

open MSt

-- Arithmetic of the overhead constant (a = 4, slack 2).

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

lem-seq : ∀ {a b k l} → a + 2 ≤ 4 * k → b + 2 ≤ 4 * l
        → suc (a + (b + 1)) + 2 ≤ 4 * suc (k + l)
lem-seq {a} {b} {k} {l} h₁ h₂
  rewrite solve 2 (λ a′ b′ → con 1 :+ (a′ :+ (b′ :+ con 1)) :+ con 2
                          := (a′ :+ con 2) :+ (b′ :+ con 2)) refl a b
        | solve 2 (λ k′ l′ → con 4 :* (con 1 :+ (k′ :+ l′))
                          := con 4 :+ (con 4 :* k′ :+ con 4 :* l′)) refl k l =
  ≤-trans (+-mono-≤ h₁ h₂) (m≤n+m _ 4)

lem-cond : ∀ {a k} → a + 2 ≤ 4 * k → suc (a + 1) + 2 ≤ 4 * suc k
lem-cond {a} {k} h
  rewrite solve 1 (λ a′ → con 1 :+ (a′ :+ con 1) :+ con 2 := (a′ :+ con 2) :+ con 2) refl a
        | solve 1 (λ k′ → con 4 :* (con 1 :+ k′) := con 4 :* k′ :+ con 4) refl k =
  +-mono-≤ h (s≤s (s≤s z≤n))

lem-loop : ∀ {nD m kD nr} → nD + 2 ≤ 4 * kD → m ≤ 4 * nr + 2
         → suc (suc (nD + m)) + 2 ≤ 4 * suc (kD + nr)
lem-loop {nD} {m} {kD} {nr} h₁ h₂
  rewrite solve 2 (λ d m′ → con 1 :+ (con 1 :+ (d :+ m′)) :+ con 2
                         := (d :+ con 2) :+ (m′ :+ con 2)) refl nD m
        | solve 2 (λ d r → con 4 :* (con 1 :+ (d :+ r))
                        := con 4 :* d :+ (con 4 :* r :+ con 2 :+ con 2)) refl kD nr =
  +-mono-≤ h₁ (+-monoˡ-≤ 2 h₂)

lem-iter : ∀ {nL nD m′ kL mD n′} → nL + 2 ≤ 4 * kL → nD + 2 ≤ 4 * mD → m′ ≤ 4 * n′ + 2
         → suc (suc (nL + suc (suc (nD + m′)))) ≤ 4 * (kL + mD + n′) + 2
lem-iter {nL} {nD} {m′} {kL} {mD} {n′} h₁ h₂ h₃ =
  ≤-trans (≤-reflexive (solve 3 (λ a b c →
             con 1 :+ (con 1 :+ (a :+ (con 1 :+ (con 1 :+ (b :+ c)))))
          := (a :+ con 2) :+ ((b :+ con 2) :+ c)) refl nL nD m′))
    (≤-trans (+-mono-≤ h₁ (+-mono-≤ h₂ h₃))
             (≤-reflexive (solve 3 (λ a b c →
                con 4 :* a :+ (con 4 :* b :+ (con 4 :* c :+ con 2))
             := con 4 :* (a :+ b :+ c) :+ con 2) refl kL mD n′)))

------------------------------------------------------------------------
-- `sim c` : the machine processes the task ⌜c⌝ on top of the todo stack,
-- leaving ⌜c⌝ on the done stack and the store updated exactly as the object
-- semantics prescribes -- in at most 4 machine steps per object step.

sim : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k → ∀ cd dn
    → Σ[ n ∈ ℕ ] (Steps ⟨ ⌜ c ⌝ ∙ cd , dn , σ ⟩ ⟨ cd , ⌜ c ⌝ ∙ dn , τ ⟩ n × n + 2 ≤ 4 * k)

-- the loop's iteration chain, from the lpD marker (D has just run, its code
-- on the done stack above the lpA record) to the reassembled loop node
simR : ∀ {e D L f σ τ n} → Rest e D L f σ τ n → ∀ cd dn (Dc′ : V)
     → Σ[ m ∈ ℕ ]
         (Steps ⟨ (atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
                , Dc′ ∙ ((atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn) , σ ⟩
                ⟨ cd , ⌜ loop e D L f ⌝ ∙ dn , τ ⟩ m
          × m ≤ 4 * n + 2)

sim e-skip cd dn = 1 , (refl ∷ []) , s≤s (s≤s (s≤s z≤n))
sim (e-ass {x} {e} {s} {v} {u} ev ru) cd dn =
  1 , (stp ∷ []) , s≤s (s≤s (s≤s z≤n))
  where
    stp : astep ⟨ ⌜ x ^= e ⌝ ∙ cd , dn , s ⟩ ≡ just ⟨ cd , ⌜ x ^= e ⌝ ∙ dn , set s x u ⟩
    stp rewrite unnum-num x | evalEV-ok s e | ev | ru = refl

sim (e-seq {c} {d} {s} {t} {u} {k} {l} dc dd) cd dn
  with sim dc (⌜ d ⌝ ∙ ((atm 13 ∙ nil) ∙ cd)) ((atm 12 ∙ nil) ∙ dn)
     | sim dd ((atm 13 ∙ nil) ∙ cd) (⌜ c ⌝ ∙ ((atm 12 ∙ nil) ∙ dn))
... | n₁ , st₁ , b₁ | n₂ , st₂ , b₂ =
  suc (n₁ + (n₂ + 1)) , (refl ∷ steps-++ st₁ (steps-++ st₂ (refl ∷ [])))
  , lem-seq {n₁} {n₂} {k} {l} b₁ b₂

sim (e-then {e} {c} {d} {f} {s} {t} {k} et dc ef) cd dn
  with sim dc ((atm 15 ∙ (nil ∙ nil)) ∙ cd)
              ((atm 14 ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
... | n₁ , st₁ , b₁ = suc (n₁ + 1) , (s1 ∷ steps-++ st₁ (s2 ∷ [])) , lem-cond {n₁} {k} b₁
  where
    s1 : astep ⟨ ⌜ cond e c d f ⌝ ∙ cd , dn , s ⟩
       ≡ just ⟨ ⌜ c ⌝ ∙ ((atm 15 ∙ (nil ∙ nil)) ∙ cd)
              , (atm 14 ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , s ⟩
    s1 rewrite evalTV-ok s e | et = refl
    s2 : astep ⟨ (atm 15 ∙ (nil ∙ nil)) ∙ cd
               , ⌜ c ⌝ ∙ ((atm 14 ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn) , t ⟩
       ≡ just ⟨ cd , ⌜ cond e c d f ⌝ ∙ dn , t ⟩
    s2 rewrite evalTV-ok t f | ef = refl

sim (e-else {e} {c} {d} {f} {s} {t} {k} et dc ef) cd dn
  with sim dc ((atm 15 ∙ nil) ∙ cd)
              ((atm 14 ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
... | n₁ , st₁ , b₁ = suc (n₁ + 1) , (s1 ∷ steps-++ st₁ (s2 ∷ [])) , lem-cond {n₁} {k} b₁
  where
    s1 : astep ⟨ ⌜ cond e c d f ⌝ ∙ cd , dn , s ⟩
       ≡ just ⟨ ⌜ d ⌝ ∙ ((atm 15 ∙ nil) ∙ cd)
              , (atm 14 ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , s ⟩
    s1 rewrite evalTV-ok s e | et = refl
    s2 : astep ⟨ (atm 15 ∙ nil) ∙ cd
               , ⌜ d ⌝ ∙ ((atm 14 ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn) , t ⟩
       ≡ just ⟨ cd , ⌜ cond e c d f ⌝ ∙ dn , t ⟩
    s2 rewrite evalTV-ok t f | ef = refl

sim (e-loop {e} {D} {L} {f} {s} {t} {u} {k} {n} et dD rest) cd dn
  with sim dD ((atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              ((atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
... | nD , stD , bD
  with simR rest cd dn ⌜ D ⌝
... | m , stR , bR =
  suc (suc (nD + m)) , (refl ∷ (s2 ∷ steps-++ stD stR)) , lem-loop {nD} {m} {k} {n} bD bR
  where
    s2 : astep ⟨ (atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
               , (atm 16 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , s ⟩
       ≡ just ⟨ ⌜ D ⌝ ∙ ((atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              , (atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , s ⟩
    s2 rewrite evalTV-ok s e | et = refl

simR {e} {D} {L} {f} (r-exit {w} ef) cd dn Dc′ = 2 , (s1 ∷ (refl ∷ [])) , ≤-refl
  where
    s1 : astep ⟨ (atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
               , Dc′ ∙ ((atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn) , w ⟩
       ≡ just ⟨ (atm 19 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
              , (atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , w ⟩
    s1 rewrite evalTV-ok w f | ef = refl

simR {e} {D} {L} {f} (r-iter {w} {x} {y} {z} {k} {m} {n} ff dL ee dD rest) cd dn Dc′
  with sim dL ((atm 20 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              ((atm 18 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
... | nL , stL , bL
  with sim dD ((atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              ((atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn)
... | nD , stD , bD
  with simR rest cd dn ⌜ D ⌝
... | m′ , stR , bR =
  _ , (s1 ∷ (refl ∷ steps-++ stL (refl ∷ (s4 ∷ steps-++ stD stR))))
    , lem-iter {nL} {nD} {m′} {k} {m} {n} bL bD bR
  where
    s1 : astep ⟨ (atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
               , Dc′ ∙ ((atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn) , w ⟩
       ≡ just ⟨ (atm 18 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
              , (atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , w ⟩
    s1 rewrite evalTV-ok w f | ff = refl
    s4 : astep ⟨ (atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd
               , (atm 20 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , x ⟩
       ≡ just ⟨ ⌜ D ⌝ ∙ ((atm 6 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ cd)
              , (atm 17 ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))) ∙ dn , x ⟩
    s4 rewrite evalTV-ok x e | ee = refl

------------------------------------------------------------------------
-- Structural invariants of one machine step.  The interpreter's main loop
--     from (=? Cd' nil) do skip loop STEP until (=? Cd nil)
-- is only a legal R-WHILE program if its entry test is FALSE after every
-- iteration (the done stack is never empty after a step) and its exit test
-- is FALSE whenever a step is taken (the todo stack is non-empty).  Both
-- are structural, because `astep` splits the todo stack and pushes a record.

astep-td : ∀ {t d σ m′} → astep ⟨ t , d , σ ⟩ ≡ just m′
         → Σ[ h ∈ V ] Σ[ r ∈ V ] (t ≡ h ∙ r)
astep-td {nil}   ()
astep-td {atm _} ()
astep-td {h ∙ r} _ = h , r , refl

astep-dn : ∀ {m m′} → astep m ≡ just m′
         → Σ[ a ∈ V ] Σ[ b ∈ V ] (MSt.dn m′ ≡ a ∙ b)
astep-dn {⟨ t , d , σ ⟩} eq with bind-inv (hdM t) _ eq
... | h , _ , eq1 with bind-inv (tlM t) _ eq1
... | r , _ , eq2 with bind-inv (step1 h r d σ) _ eq2
... | (a , b , c , s) , _ , refl = b , c , refl

------------------------------------------------------------------------
-- Corollary: run from the initial machine state (one task, empty done
-- stack), the machine computes the object program's store transformation,
-- leaves the source program reassembled on the done stack (PROGRAM-PRESERVING)
-- and takes at most 4 steps per object step (LINEAR overhead).

machine-linear : ∀ {c σ τ k} → c ⊢ σ ⇒ τ ∣ k
               → Σ[ n ∈ ℕ ]
                   (Steps ⟨ ⌜ c ⌝ ∙ nil , nil , σ ⟩ ⟨ nil , ⌜ c ⌝ ∙ nil , τ ⟩ n × n ≤ 4 * k)
machine-linear d with sim d nil nil
... | n , st , b = n , st , ≤-trans (m≤m+n n 2) b

------------------------------------------------------------------------
-- Tests (checked by the type checker, `refl` = the machine really runs).
--
--   prog = (X0 ^= '5) ; (X1 ^= cons X0 nil)   on the store [nil, nil]
--
-- Object run: 3 command nodes.  Machine run: 4 steps ('seq, ass, ass, 'seqE),
-- ending with the program reassembled on the done stack -- inside the 3·k bound.

private
  prog : Cmd
  prog = (0 ^= opd (cst (atm 5))) ⨾ (1 ^= cns (var 0) (cst nil))

  σ₀ : Store
  σ₀ = nil ∷ nil ∷ []

  σ₁ : Store
  σ₁ = atm 5 ∷ (atm 5 ∙ nil) ∷ []

  test-object : exec 10 prog σ₀ ≡ just (σ₁ , 3)
  test-object = refl

  test-machine : (astep ⟨ ⌜ prog ⌝ ∙ nil , nil , σ₀ ⟩ >>=M astep >>=M astep >>=M astep)
               ≡ just ⟨ nil , ⌜ prog ⌝ ∙ nil , σ₁ ⟩
  test-machine = refl

  -- a loop: from (=? X0 nil) do skip loop (X0 ^= '7) until (=? X0 '7)
  -- runs its body once; object cost 4, machine cost 11
  -- ('loop, lpA, skip, lpD, lpB, L, lpC, lpA, skip, lpD, lpZ) -- 2.75 < 4.
  lp : Cmd
  lp = loop (eqE (var 0) (cst nil)) skip (0 ^= opd (cst (atm 7))) (eqE (var 0) (cst (atm 7)))

  test-loop-object : exec 20 lp (nil ∷ []) ≡ just (atm 7 ∷ [] , 4)
  test-loop-object = refl

  -- pair? at the object level: X0 ^= pair? X1 sets X0 to TRUE when X1 is a
  -- cons cell (and the machine's own expression evaluator agrees, by
  -- `evalEV-ok`)
  test-pair-object : exec 10 (0 ^= prE (var 1)) (nil ∷ (nil ∙ nil) ∷ [])
                   ≡ just ((nil ∙ nil) ∷ (nil ∙ nil) ∷ [] , 1)
  test-pair-object = refl

  test-pair-object-f : exec 10 (0 ^= prE (var 1)) (nil ∷ atm 3 ∷ [])
                     ≡ just (nil ∷ atm 3 ∷ [] , 1)
  test-pair-object-f = refl

  test-loop-machine :
    (astep ⟨ ⌜ lp ⌝ ∙ nil , nil , nil ∷ [] ⟩
       >>=M astep >>=M astep >>=M astep >>=M astep >>=M astep
       >>=M astep >>=M astep >>=M astep >>=M astep >>=M astep)
    ≡ just ⟨ nil , ⌜ lp ⌝ ∙ nil , atm 7 ∷ [] ⟩
  test-loop-machine = refl
