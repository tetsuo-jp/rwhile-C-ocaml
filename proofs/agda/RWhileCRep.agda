{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Extend the concrete model to R-WHILE's PATTERN REPLACEMENT `CRep`.
--
-- `q <= r`  (CRep q r, evalCom in src/EvalRwhile.ml):
--     read the source pattern r  (evalPat)      → value v, store σ→σ₁
--     write v into the target pattern q (inv_evalPat) → store σ₁→σ'
-- Inversion (src/InvRwhile.ml):  inv (CRep q r) = CRep r q  (swap patterns).
--
-- We model pattern READ (evalPat) and WRITE (inv_evalPat) as independent
-- relations and PROVE they are mutual converses (read-write / write-read);
-- hence `CRep r q` realises the converse of `CRep q r`, i.e. R-WHILE's
-- syntactic inversion of pattern replacement is semantically the inverse.
--
-- Patterns are LINEAR (each variable occurs once, the two sides disjoint), as
-- enforced by the interpreter (warn_linearity).  Under linearity the two
-- sub-patterns of a cons touch disjoint variables, so read and the
-- (reverse-order, structurally-inverse) write coincide with evalPat /
-- inv_evalPat; we use that structural inverse for the write here.
------------------------------------------------------------------------

module RWhileCRep where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import RWhileValStore using (Val; nil; cons; Store; _≢ℕ_)
import RWhileRevFull
open RWhileRevFull.Core Store

------------------------------------------------------------------------
-- Patterns (AbsRwhile's pat: PVar / PVal / PCons).

data Pat : Set where
  pvar  : ℕ → Pat
  pval  : Val → Pat
  pcons : Pat → Pat → Pat

------------------------------------------------------------------------
-- READ a pattern (evalPat): yields a value, clearing the pattern's variables.

data Read : Pat → Store → Val → Store → Set where
  rd-var  : ∀ {x v σ σ'} → v ≡ σ x → σ' x ≡ nil → (∀ y → x ≢ℕ y → σ y ≡ σ' y)
          → Read (pvar x) σ v σ'
  rd-val  : ∀ {w σ} → Read (pval w) σ w σ
  rd-cons : ∀ {p1 p2 σ v1 σ1 v2 σ2}
          → Read p1 σ v1 σ1 → Read p2 σ1 v2 σ2
          → Read (pcons p1 p2) σ (cons v1 v2) σ2

------------------------------------------------------------------------
-- WRITE a pattern (inv_evalPat): the structural inverse of READ.  A var must
-- be nil before being written; a literal must match; a cons writes its two
-- sub-patterns (reverse order — the structural inverse of read).

data Write : Pat → Store → Val → Store → Set where
  wr-var  : ∀ {x v σ σ'} → σ x ≡ nil → v ≡ σ' x → (∀ y → x ≢ℕ y → σ y ≡ σ' y)
          → Write (pvar x) σ v σ'
  wr-val  : ∀ {w σ} → Write (pval w) σ w σ
  wr-cons : ∀ {p1 p2 σ v1 σ1 v2 σ2}
          → Write p2 σ v2 σ1 → Write p1 σ1 v1 σ2
          → Write (pcons p1 p2) σ (cons v1 v2) σ2

------------------------------------------------------------------------
-- READ and WRITE are mutual converses.

read-write : ∀ {p σ v σ'} → Read p σ v σ' → Write p σ' v σ
read-write (rd-var ve cl fr) = wr-var cl ve (λ y h → sym (fr y h))
read-write rd-val            = wr-val
read-write (rd-cons r1 r2)   = wr-cons (read-write r2) (read-write r1)

write-read : ∀ {p σ v σ'} → Write p σ v σ' → Read p σ' v σ
write-read (wr-var cl ve fr) = rd-var ve cl (λ y h → sym (fr y h))
write-read wr-val            = rd-val
write-read (wr-cons w2 w1)   = rd-cons (write-read w1) (write-read w2)

------------------------------------------------------------------------
-- `CRep lhs rhs` as a store relation: read the source rhs, write the target lhs.

CRepRel : Pat → Pat → Store → Store → Set
CRepRel lhs rhs σ σ' =
  Σ[ v ∈ Val ] Σ[ σ1 ∈ Store ] (Read rhs σ v σ1 × Write lhs σ1 v σ')

-- Reversibility: the syntactic inverse `CRep rhs lhs` realises the converse.
CRep-rev : ∀ {lhs rhs σ σ'} → CRepRel lhs rhs σ σ' → CRepRel rhs lhs σ' σ
CRep-rev (v , σ1 , rd , wr) = (v , σ1 , write-read wr , read-write rd)

------------------------------------------------------------------------
-- As an R-WHILE atom: pattern replacement, and its inverse cancels it.

crepC : Pat → Pat → Cmd
crepC lhs rhs = atom (CRepRel lhs rhs)

crep-reversible : ∀ {lhs rhs s t}
                → crepC lhs rhs ⊢ s ⇒ t → crepC rhs lhs ⊢ t ⇒ s
crep-reversible (e-atom cr) = e-atom (CRep-rev cr)
