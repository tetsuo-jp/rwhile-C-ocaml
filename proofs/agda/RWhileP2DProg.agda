{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- program⇄data round-trip for the R-WHILE CONTROL CORE (gap G4, #6).
--
-- RWhileP2D proved the round-trip for the residual expression language `Code`.
-- Here we extend it to whole programs: expressions (var/val/cons/hd/tl/eq/pairp),
-- patterns (var/val/cons), commands (seq/ass/rep/cond/loop), and the program
-- wrapper — i.e. the constructors that `src/Program2DataRwhile.ml`'s
-- transProgram / data2program handle.  We prove
--
--     dProg (transProg p) ≡ p          (and the exp/pat/com lemmas)
--
-- so decoding undoes encoding on the full control core.
--
-- Modelling notes (vs the OCaml reference):
--   * variable indices use a clean unary `Nat` encoding with `unnat (natV n) ≡ n`.
--     (The OCaml `transRIdent`/`d_ident` have an incidental off-by-one — the
--     round-trip there is identity only up to a *consistent relabelling* of
--     indices; we model the clean encoding, which is the meaningful invariant.)
--   * `Val` is RWhileAVSound's binary tree; constructor tags are distinct header
--     trees Hk (a left spine of k nils), as in RWhileP2D — atoms are not a
--     separate Val constructor here.
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileP2DProg where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import RWhileAVSound using (Val; ⟨⟩; _·_)

------------------------------------------------------------------------
-- AST of the control core (mirrors AbsRwhile's exp / pat / com, the p2d subset).

data Exp : Set where
  eVar   : ℕ → Exp
  eVal   : Val → Exp
  eCons  : Exp → Exp → Exp
  eHd    : Exp → Exp
  eTl    : Exp → Exp
  eEq    : Exp → Exp → Exp
  ePairp : Exp → Exp

data Pat : Set where
  pVar  : ℕ → Pat
  pVal  : Val → Pat
  pCons : Pat → Pat → Pat

data Com : Set where
  cSeq  : Com → Com → Com
  cAss  : ℕ → Exp → Com
  cRep  : Pat → Pat → Com
  cCond : Exp → Com → Com → Exp → Com
  cLoop : Exp → Com → Com → Exp → Com

data Prog : Set where
  prog : ℕ → Com → ℕ → Prog          -- read x; body; write y

------------------------------------------------------------------------
-- clean unary encoding of a variable index, with a left-inverse.

natV : ℕ → Val
natV zero    = ⟨⟩
natV (suc n) = ⟨⟩ · natV n

unnat : Val → ℕ
unnat ⟨⟩            = zero
unnat (⟨⟩ · t)      = suc (unnat t)
unnat ((_ · _) · _) = zero          -- malformed default

unnat-natV : ∀ n → unnat (natV n) ≡ n
unnat-natV zero    = refl
unnat-natV (suc n) = cong suc (unnat-natV n)

------------------------------------------------------------------------
-- header trees Hk (left spine of k nils); each constructor = Hk · payload.

H0 H1 H2 H3 H4 H5 H6 : Val
H0 = ⟨⟩
H1 = ⟨⟩ · ⟨⟩
H2 = (⟨⟩ · ⟨⟩) · ⟨⟩
H3 = ((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩
H4 = (((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩
H5 = ((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩
H6 = (((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩

------------------------------------------------------------------------
-- encode (program2data)

transExp : Exp → Val
transExp (eVar n)    = H0 · natV n
transExp (eVal v)    = H1 · v
transExp (eCons a b) = H2 · (transExp a · transExp b)
transExp (eHd e)     = H3 · transExp e
transExp (eTl e)     = H4 · transExp e
transExp (eEq a b)   = H5 · (transExp a · transExp b)
transExp (ePairp e)  = H6 · transExp e

transPat : Pat → Val
transPat (pVar n)    = H0 · natV n
transPat (pVal v)    = H1 · v
transPat (pCons a b) = H2 · (transPat a · transPat b)

transCom : Com → Val
transCom (cSeq a b)       = H0 · (transCom a · transCom b)
transCom (cAss n e)       = H1 · (natV n · transExp e)
transCom (cRep p q)       = H2 · (transPat p · transPat q)
transCom (cCond e t el f) = H3 · (transExp e · (transCom t · (transCom el · transExp f)))
transCom (cLoop e d l f)  = H4 · (transExp e · (transCom d · (transCom l · transExp f)))

transProg : Prog → Val
transProg (prog x c y) = natV x · (transCom c · natV y)

------------------------------------------------------------------------
-- decode (data2program); malformed inputs fall through to a default.

dExp : Val → Exp
dExp (⟨⟩ · pv)                                          = eVar (unnat pv)
dExp ((⟨⟩ · ⟨⟩) · v)                                    = eVal v
dExp (((⟨⟩ · ⟨⟩) · ⟨⟩) · (a · b))                       = eCons (dExp a) (dExp b)
dExp ((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · e)                      = eHd (dExp e)
dExp (((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · e)               = eTl (dExp e)
dExp ((((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · (a · b))  = eEq (dExp a) (dExp b)
dExp (((((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · e) = ePairp (dExp e)
dExp _                                                  = eVal ⟨⟩

dPat : Val → Pat
dPat (⟨⟩ · pv)                          = pVar (unnat pv)
dPat ((⟨⟩ · ⟨⟩) · v)                    = pVal v
dPat (((⟨⟩ · ⟨⟩) · ⟨⟩) · (a · b))       = pCons (dPat a) (dPat b)
dPat _                                  = pVal ⟨⟩

dCom : Val → Com
dCom (⟨⟩ · (a · b))                                      = cSeq (dCom a) (dCom b)
dCom ((⟨⟩ · ⟨⟩) · (n · e))                              = cAss (unnat n) (dExp e)
dCom (((⟨⟩ · ⟨⟩) · ⟨⟩) · (p · q))                       = cRep (dPat p) (dPat q)
dCom ((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · (e · (t · (el · f))))   = cCond (dExp e) (dCom t) (dCom el) (dExp f)
dCom (((((⟨⟩ · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · (e · (d · (l · f)))) = cLoop (dExp e) (dCom d) (dCom l) (dExp f)
dCom _                                                  = cRep (pVal ⟨⟩) (pVal ⟨⟩)

dProg : Val → Prog
dProg (x · (c · y)) = prog (unnat x) (dCom c) (unnat y)
dProg _             = prog zero (cRep (pVal ⟨⟩) (pVal ⟨⟩)) zero

------------------------------------------------------------------------
-- round-trip: decode undoes encode (G4 for the control core).

dExp∘t : ∀ e → dExp (transExp e) ≡ e
dExp∘t (eVar n)    = cong eVar (unnat-natV n)
dExp∘t (eVal v)    = refl
dExp∘t (eCons a b) = cong₂ eCons (dExp∘t a) (dExp∘t b)
dExp∘t (eHd e)     = cong eHd (dExp∘t e)
dExp∘t (eTl e)     = cong eTl (dExp∘t e)
dExp∘t (eEq a b)   = cong₂ eEq (dExp∘t a) (dExp∘t b)
dExp∘t (ePairp e)  = cong ePairp (dExp∘t e)

dPat∘t : ∀ p → dPat (transPat p) ≡ p
dPat∘t (pVar n)    = cong pVar (unnat-natV n)
dPat∘t (pVal v)    = refl
dPat∘t (pCons a b) = cong₂ pCons (dPat∘t a) (dPat∘t b)

dCom∘t : ∀ c → dCom (transCom c) ≡ c
dCom∘t (cSeq a b)       = cong₂ cSeq (dCom∘t a) (dCom∘t b)
dCom∘t (cAss n e)       = cong₂ cAss (unnat-natV n) (dExp∘t e)
dCom∘t (cRep p q)       = cong₂ cRep (dPat∘t p) (dPat∘t q)
dCom∘t (cCond e t el f) = cong₄ cCond (dExp∘t e) (dCom∘t t) (dCom∘t el) (dExp∘t f)
  where cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
                {a a′ b b′ c c′ d d′}
              → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
        cong₄ f refl refl refl refl = refl
dCom∘t (cLoop e d l f)  = cong₄ cLoop (dExp∘t e) (dCom∘t d) (dCom∘t l) (dExp∘t f)
  where cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
                {a a′ b b′ c c′ d d′}
              → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
        cong₄ f refl refl refl refl = refl

dProg∘t : ∀ p → dProg (transProg p) ≡ p
dProg∘t (prog x c y) = cong₃ prog (unnat-natV x) (dCom∘t c) (unnat-natV y)
  where cong₃ : ∀ {A B C D : Set} (f : A → B → C → D)
               {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
        cong₃ f refl refl refl = refl
