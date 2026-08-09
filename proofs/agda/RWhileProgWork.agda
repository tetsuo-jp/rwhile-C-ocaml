{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE WORK OF A WHOLE PROGRAM, AND THE LAW THE MEASUREMENT OBEYS.
--
-- RWhileWork meters COMMANDS.  `./ri -work` meters a PROGRAM, and
-- `EvalRwhile.evalProgram` does two things around the body that the command
-- relation does not see:
--
--   read X;  ...   `rupdate (x, d)` into an all-nil store -- FREE, because
--                  `rupdate` tests `vy = VNil` first and that test is not
--                  charged;
--   ... write Y;   `rupdate (y, res)` -- the answer slot is cleared against
--                  its own contents, so this CHARGES `eq_work res res`, the
--                  full node count of the answer, and then `all_cleared`.
--
-- Hence   work(p on d) = work(body) + |⟦p⟧d|   (for a non-nil answer), which
-- is `progW` below.  This one extra clearing test is what makes the measured
-- table what it is.
--
-- THE LAW.  p⁺'s output slot holds ⟨⌜p⌝ , ⟦p⟧d⟩ instead of ⟦p⟧d, so the
-- `write` clearing test walks 1 + |⌜p⌝| + |⟦p⟧d| nodes instead of |⟦p⟧d|:
--
--     work(p⁺ on d) = work(p on d) + w_emit + |⌜p⌝| + 1 .
--
-- For the OCaml emit `P-SELF ^= ⌜p⌝ ; OUT-PP <= (P-SELF . Y)` we have
-- w_emit = 0 -- the assignment writes a FRESH (nil) slot, and `CRep`'s
-- variable patterns are read and written free -- giving
--
--     work(p⁺ on d) = work(p on d) + |⌜p⌝| + 1 .            (pp-progW-ocaml)
--
-- `measured-law` below checks that equation against all ELEVEN rows of
-- `./measure_proj jones-self` (the `wk_dir` and `wk_p+` columns, with
-- |⌜p⌝| counted from `./ri -p2d`).  It holds exactly, on the nose, for every
-- row.  For the flat-core emit of RWhileProgPres (four `^=`, which have to
-- pay for the clearings `CRep` gets free) the same law gives w_emit =
-- |⌜p⌝| + |⟦p⟧d| -- RWhileProgPresWork.pp-work.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileProgWork where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import RWhileTime
open import RWhileWorkV using (nodes; rupdW; rupdW-self; rupdW-self-pair; rupdW-fresh)
open import RWhileWork

------------------------------------------------------------------------
-- 1.  A program, and its run.  `read X; body; write Y`.

record Program : Set where
  constructor prog
  field
    inp out : ℕ
    body    : Cmd

-- the work a program charges: the body's work plus the `write` clearing test
progW : ℕ → V → ℕ
progW wbody v = wbody + rupdW v v

-- `p ▷ d ⇒ v ∥ W` : p run on d yields v, charging W work.
--
-- The initial store is `set [] x d`, i.e. all slots nil except the input
-- slot -- which is exactly `rupdate (x, d)` applied to the all-nil store,
-- at zero cost (`rupdW-fresh`).  The last premise is `all_cleared`: every
-- slot but the output is nil when the body finishes.
infix 3 _▷_⇒_∥_
data _▷_⇒_∥_ : Program → V → V → ℕ → Set where
  run : ∀ {x y c d τ k w v}
      → c ⊢ set [] x d ⇒ τ ∣ k ∥ w
      → get τ y ≡ v
      → (∀ z → ¬ (y ≡ z) → get τ z ≡ nil)
      → prog x y c ▷ d ⇒ v ∥ progW w v

-- reading the input is free (the slot is nil): this is the `rupdate` branch
-- that `-work` does not charge, stated so the model can be checked.
read-free : ∀ (d : V) → rupdW nil d ≡ 0
read-free = rupdW-fresh

-- writing the answer is not free: it walks the whole answer.
write-cost : ∀ v → ¬ (v ≡ nil) → progW 0 v ≡ nodes v
write-cost v h = rupdW-self v h

------------------------------------------------------------------------
-- 2.  THE LAW.

private
  open +-*-Solver
  shuffle : ∀ a b n m → (a + b) + (suc (n + m)) ≡ (a + m) + (b + suc n)
  shuffle = solve 4
    (λ a b n m → (a :+ b) :+ (con 1 :+ (n :+ m)) := (a :+ m) :+ (b :+ (con 1 :+ n)))
    refl

-- The general accounting: whatever the emit itself charges (`we`), moving
-- the answer into ⟨⌜p⌝ , answer⟩ adds |⌜p⌝| + 1 to the `write` clearing.
pp-progW : ∀ wbody we pd v → ¬ (v ≡ nil)
         → progW (wbody + we) (pd ∙ v) ≡ progW wbody v + (we + suc (nodes pd))
pp-progW wbody we pd v v≢nil =
  trans (cong (λ z → (wbody + we) + z) (rupdW-self-pair pd v))
        (trans (shuffle wbody we (nodes pd) (nodes v))
               (cong (λ z → (wbody + z) + (we + suc (nodes pd)))
                     (sym (rupdW-self v v≢nil))))

-- THE MEASURED LAW.  The OCaml emit charges nothing (`we = 0`), so
--
--        work(p⁺) = work(p) + |⌜p⌝| + 1 .
pp-progW-ocaml : ∀ wbody pd v → ¬ (v ≡ nil)
               → progW wbody (pd ∙ v) ≡ progW wbody v + suc (nodes pd)
pp-progW-ocaml wbody pd v v≢nil =
  subst (λ z → progW z (pd ∙ v) ≡ progW wbody v + suc (nodes pd))
        (+-identityʳ wbody) (pp-progW wbody 0 pd v v≢nil)

-- ... and stated over actual runs: two programs on the same input, one
-- producing v and the other ⟨⌜p⌝ , v⟩ with an emit charging `we`.
pp-run-law : ∀ {x y c y⁺ c⁺ d v pd wbody we}
           → prog x y  c  ▷ d ⇒ v        ∥ progW wbody v
           → prog x y⁺ c⁺ ▷ d ⇒ (pd ∙ v) ∥ progW (wbody + we) (pd ∙ v)
           → ¬ (v ≡ nil)
           → progW (wbody + we) (pd ∙ v)
             ≡ progW wbody v + (we + suc (nodes pd))
pp-run-law {v = v} {pd = pd} {wbody = wbody} {we = we} _ _ v≢nil =
  pp-progW wbody we pd v v≢nil

------------------------------------------------------------------------
-- 3.  THE LAW AGAINST THE MEASUREMENT.
--
-- `./measure_proj jones-self` (2026-08-09) reports, per subject, the work
-- of p run directly (`wk_dir`), of p⁺ (`wk_p+`) and of the fp1 residual
-- (`wk_res`).  |⌜p⌝| is `nodes` of the value `./ri -p2d <subject>` prints.
-- Each row below is (wk_dir , wk_p+ , |⌜p⌝| , wk_res).

record Row : Set where
  constructor row
  field wk-p wk-p⁺ code wk-res : ℕ
open Row

--                        wk_dir  wk_p+  |⌜p⌝|  wk_res
id            = row          3      23     19      23
id2           = row          3      25     21      25
id3           = row          4      38     33      37
rep           = row          3      25     21      25
swap          = row          3      57     53      57
sx-splitjoin  = row          3      57     53      57
sx-three      = row          6      72     65      71
loop-static2  = row         16     104     87      95
loop-static3  = row         26     118     91     101
reverse       = row         11     103     91    1769
dyncond3      = row          6      78     71     428

measured : List Row
measured = id ∷ id2 ∷ id3 ∷ rep ∷ swap ∷ sx-splitjoin ∷ sx-three
         ∷ loop-static2 ∷ loop-static3 ∷ reverse ∷ dyncond3 ∷ []

-- THE THEOREM PREDICTS EVERY MEASURED NUMBER.  `pp-progW-ocaml` says
-- wk_p+ = wk_dir + |⌜p⌝| + 1; each `refl` below is one measured row.
measured-law : All (λ r → wk-p⁺ r ≡ wk-p r + suc (code r)) measured
measured-law = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl
             ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

-- It is not vacuous: the overhead really does vary from row to row (23-3-1
-- = 19 for `id`, 118-26-1 = 91 for loop_static3), so no constant could have
-- fitted the table.  (RWhileProgPresWork.work-not-constant is the general
-- statement.)
overhead-varies : ¬ (wk-p⁺ id ≡ wk-p id + suc (code loop-static3))
overhead-varies ()

------------------------------------------------------------------------
-- 4.  REVERSIBLE JONES OPTIMALITY ON THE WORK METER, row by row.
--
-- `RevJonesOptimal r p p⁺` demands work(residual) ≤ work(p⁺).  On the NINE
-- subjects of the closed table it HOLDS; on the two DYNAMIC-CONTROL
-- subjects (`reverse`, `dyncond3`, the `jones-self-open` group) it FAILS,
-- by 17x and 5x.  Both directions are recorded, so that neither can be
-- quietly dropped.

closed : List Row
closed = id ∷ id2 ∷ id3 ∷ rep ∷ swap ∷ sx-splitjoin ∷ sx-three
       ∷ loop-static2 ∷ loop-static3 ∷ []

jones-work-holds : All (λ r → wk-res r ≤ wk-p⁺ r) closed
jones-work-holds =
    toWitness {a? =   23 ≤?  23} tt
  ∷ toWitness {a? =   25 ≤?  25} tt
  ∷ toWitness {a? =   37 ≤?  38} tt
  ∷ toWitness {a? =   25 ≤?  25} tt
  ∷ toWitness {a? =   57 ≤?  57} tt
  ∷ toWitness {a? =   57 ≤?  57} tt
  ∷ toWitness {a? =   71 ≤?  72} tt
  ∷ toWitness {a? =   95 ≤? 104} tt
  ∷ toWitness {a? =  101 ≤? 118} tt
  ∷ []

-- the honest other half: dynamic control is still out of reach
reverse-not-work-optimal : ¬ (wk-res reverse ≤ wk-p⁺ reverse)
reverse-not-work-optimal = toWitnessFalse {a? = 1769 ≤? 103} tt

dyncond3-not-work-optimal : ¬ (wk-res dyncond3 ≤ wk-p⁺ dyncond3)
dyncond3-not-work-optimal = toWitnessFalse {a? = 428 ≤? 78} tt

-- ... and the classical criterion (residual ≤ p) fails on the work meter
-- too, for every row -- as RWhileProgPresMin.ext-not-classical predicts,
-- since the residual is an extension of p.
classical-fails : All (λ r → ¬ (wk-res r ≤ wk-p r)) closed
classical-fails =
    toWitnessFalse {a? =  23 ≤?  3} tt
  ∷ toWitnessFalse {a? =  25 ≤?  3} tt
  ∷ toWitnessFalse {a? =  37 ≤?  4} tt
  ∷ toWitnessFalse {a? =  25 ≤?  3} tt
  ∷ toWitnessFalse {a? =  57 ≤?  3} tt
  ∷ toWitnessFalse {a? =  57 ≤?  3} tt
  ∷ toWitnessFalse {a? =  71 ≤?  6} tt
  ∷ toWitnessFalse {a? =  95 ≤? 16} tt
  ∷ toWitnessFalse {a? = 101 ≤? 26} tt
  ∷ []
