{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Program-as-data: the encoding `⌜_⌝` of the R-WHILE core into R-WHILE
-- VALUES, which the self-interpreter of RWhileSI* consumes.  This is the
-- Agda counterpart of `src/Program2DataRwhile.ml` (`./ri -p2d`).
--
--   variables/indices   unary numerals   num 0 = nil, num (1+n) = (nil . num n)
--   operands            ('var . num x)   ('cst . v)
--   expressions         ('opd . a) ('cns . (a.b)) ('hd . a) ('tl . a) ('eq . (a.b))
--   commands            ('skip . nil) ('ass . (num x . e)) ('seq . (c.d))
--                       ('cond . (e.(c.(d.f)))) ('loop . (e.(c.(d.f))))
--   stores              a cons-list of the variables' values
--
-- Tags are atoms; the numeric codes are collected here as `t-*` so the
-- interpreter and the proofs share one table.  `⌜_⌝`-injectivity is not
-- needed: the simulation proof goes by induction on the object derivation,
-- so the code is always known constructor-wise.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIEnc where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime

------------------------------------------------------------------------
-- Tag table.  (Object-language tags below 20; runtime markers from 20.)

t-var t-cst t-opd t-cns t-hd t-tl t-eq : ℕ
t-var = 0
t-cst = 1
t-opd = 2
t-cns = 3
t-hd  = 4
t-tl  = 5
t-eq  = 6

t-skip t-ass t-seq t-cond t-loop : ℕ
t-skip = 7
t-ass  = 8
t-seq  = 9
t-cond = 10
t-loop = 11

-- Runtime markers (continuations); `*B` tags mark a processed node on the
-- done stack, the others are continuation tasks on the todo stack.
-- (Numbered 12..20: Agda only expands numeric literal PATTERNS up to 20,
-- and the machine of RWhileSIMach dispatches by matching on `atm <tag>`.)
-- `t-lpD` reuses number 6: 0-6 number operands and expressions, which never
-- occur as TASK tags, so the task namespace is free there.
t-seqB t-seqE t-condB t-condE t-loopB t-lpA t-lpB t-lpZ t-lpC t-lpD : ℕ
t-seqB  = 12
t-seqE  = 13
t-condB = 14
t-condE = 15
t-loopB = 16
t-lpA   = 17
t-lpB   = 18
t-lpZ   = 19
t-lpC   = 20
t-lpD   = 6

------------------------------------------------------------------------
-- Unary numerals (as in ri.rwhile's `Cnt`).

num : ℕ → V
num zero    = nil
num (suc n) = nil ∙ num n

------------------------------------------------------------------------
-- Encodings.

⌜_⌝ᵒ : Opd → V
⌜ var x ⌝ᵒ = atm t-var ∙ num x
⌜ cst v ⌝ᵒ = atm t-cst ∙ v

-- Expressions are encoded UNIFORMLY as (tag . (operand1 . operand2)); the
-- unary forms carry the dummy operand `'cst . nil`.  The uniformity is what
-- lets the interpreter evaluate both operand slots before dispatching, so
-- every dispatch branch is a single assignment (RWhileSIEval.evalC).
dummyOpd : V
dummyOpd = atm t-cst ∙ nil

⌜_⌝ᵉ : Exp → V
⌜ opd a   ⌝ᵉ = atm t-opd ∙ (⌜ a ⌝ᵒ ∙ dummyOpd)
⌜ cns a b ⌝ᵉ = atm t-cns ∙ (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ)
⌜ hdE a   ⌝ᵉ = atm t-hd  ∙ (⌜ a ⌝ᵒ ∙ dummyOpd)
⌜ tlE a   ⌝ᵉ = atm t-tl  ∙ (⌜ a ⌝ᵒ ∙ dummyOpd)
⌜ eqE a b ⌝ᵉ = atm t-eq  ∙ (⌜ a ⌝ᵒ ∙ ⌜ b ⌝ᵒ)

⌜_⌝ : Cmd → V
⌜ skip         ⌝ = atm t-skip ∙ nil
⌜ x ^= e       ⌝ = atm t-ass  ∙ (num x ∙ ⌜ e ⌝ᵉ)
⌜ c ⨾ d        ⌝ = atm t-seq  ∙ (⌜ c ⌝ ∙ ⌜ d ⌝)
⌜ cond e c d f ⌝ = atm t-cond ∙ (⌜ e ⌝ᵉ ∙ (⌜ c ⌝ ∙ (⌜ d ⌝ ∙ ⌜ f ⌝ᵉ)))
⌜ loop e D L f ⌝ = atm t-loop ∙ (⌜ e ⌝ᵉ ∙ (⌜ D ⌝ ∙ (⌜ L ⌝ ∙ ⌜ f ⌝ᵉ)))

------------------------------------------------------------------------
-- Stores as values: the object store (a list of values) becomes the
-- cons-list the interpreter walks (`Vl` of ri.rwhile).

encS : Store → V
encS []       = nil
encS (v ∷ vs) = v ∙ encS vs

------------------------------------------------------------------------
-- Program measures used by the linear-overhead constant.
--   `vmax c` bounds every variable index occurring in c (the length of the
--   variable list the interpreter has to walk).

vmaxᵒ : Opd → ℕ
vmaxᵒ (var x) = suc x
vmaxᵒ (cst _) = 0

vmaxᵉ : Exp → ℕ
vmaxᵉ (opd a)   = vmaxᵒ a
vmaxᵉ (cns a b) = vmaxᵒ a ⊔ vmaxᵒ b
vmaxᵉ (hdE a)   = vmaxᵒ a
vmaxᵉ (tlE a)   = vmaxᵒ a
vmaxᵉ (eqE a b) = vmaxᵒ a ⊔ vmaxᵒ b

vmax : Cmd → ℕ
vmax skip           = 0
vmax (x ^= e)       = suc x ⊔ vmaxᵉ e
vmax (c ⨾ d)        = vmax c ⊔ vmax d
vmax (cond e c d f) = vmaxᵉ e ⊔ vmax c ⊔ vmax d ⊔ vmaxᵉ f
vmax (loop e D L f) = vmaxᵉ e ⊔ vmax D ⊔ vmax L ⊔ vmaxᵉ f
