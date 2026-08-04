{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick P1 of the self-interpreter's dispatch body: the interpreter's own
-- variable layout and its stack MACROS, with their run-and-cost lemmas.
--
-- The dispatch body `STEP` of RWhileSIProg.Realises has to be written in the
-- object language itself (that is what makes the interpreter a SELF-
-- interpreter).  R-WHILE has no pattern replacement `<=` in this core, so a
-- stack push/pop is spelled out with reversible assignments only:
--
--   push T X S  =  T ^= cons X S ; S ^= tl T ; X ^= hd T ; S ^= T ; T ^= S
--   pop  T X S  =  T ^= S ; S ^= T ; X ^= hd T ; S ^= tl T ; T ^= cons X S
--
-- (`pop` is `push` reversed -- each `^=` is its own inverse here because the
-- assigned variable never occurs in the assigned expression.)  Both cost 9
-- steps in the implementation's cost model: 5 assignments + 4 `;` nodes.
--
-- The interpreter's store is a fixed 19-slot list (`emb`), so `get`/`set` at
-- the literal indices below COMPUTE; every lemma here is therefore a plain
-- derivation whose intermediate stores Agda checks by evaluation.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIMac where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)

open import RWhileTime
open import RWhileSIWf using (get-set-≡; get-set-≢)

------------------------------------------------------------------------
-- The interpreter's variables.

iCd iDn iVl iTg iAg iT1 iT2 iHd iVv iKk iCn iRv iEl iWw iA1 iA2 iT3 iEt iOt : ℕ
iCd = 0    -- todo stack           (ri.rwhile: Cd)
iDn = 1    -- done stack           (ri.rwhile: Cd')
iVl = 2    -- object store         (ri.rwhile: Vl)
iTg = 3    -- current task's tag
iAg = 4    -- current task's argument
iT1 = 5    -- scratch (push/pop)
iT2 = 6    -- scratch
iHd = 7    -- head register
iVv = 8    -- value register
iKk = 9    -- variable-index numeral
iCn = 10   -- walk counter         (ri.rwhile: Cnt)
iRv = 11   -- walk prefix          (ri.rwhile: Rev)
iEl = 12   -- walk element         (ri.rwhile: Elem)
iWw = 13   -- test truth register
iA1 = 14   -- operand register 1
iA2 = 15   -- operand register 2
iT3 = 16   -- scratch (an expression's argument pair)
iEt = 17   -- an expression's tag
iOt = 18   -- an operand's tag

------------------------------------------------------------------------
-- The interpreter's store, as a record (eta) over its 19 slots.

record ISt : Set where
  constructor mkI
  field cd dn vl tg ag t1 t2 hd vv kk cn rv el ww a1 a2 t3 etg ot : V

emb : ISt → Store
emb (mkI cd dn vl tg ag t1 t2 hd vv kk cn rv el ww a1 a2 t3 etg ot) =
  cd ∷ dn ∷ vl ∷ tg ∷ ag ∷ t1 ∷ t2 ∷ hd ∷ vv ∷ kk ∷ cn ∷ rv ∷ el ∷ ww ∷ a1 ∷ a2 ∷ t3 ∷ etg ∷ ot ∷ []

-- the two stacks really are variables 0 and 1 (RWhileSIProg.Realises needs this)
emb-cd : ∀ r → get (emb r) iCd ≡ ISt.cd r
emb-cd (mkI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl

emb-dn : ∀ r → get (emb r) iDn ≡ ISt.dn r
emb-dn (mkI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl

------------------------------------------------------------------------
-- The macros.

push : ℕ → ℕ → ℕ → Cmd
push t x s = (t ^= cns (var x) (var s))
           ⨾ (s ^= tlE (var t))
           ⨾ (x ^= hdE (var t))
           ⨾ (s ^= opd (var t))
           ⨾ (t ^= opd (var s))

pop : ℕ → ℕ → ℕ → Cmd
pop t x s = (t ^= opd (var s))
          ⨾ (s ^= opd (var t))
          ⨾ (x ^= hdE (var t))
          ⨾ (s ^= tlE (var t))
          ⨾ (t ^= cns (var x) (var s))

-- copy the value of x into the (nil) variable y; running it again clears y
cpy : ℕ → ℕ → Cmd
cpy x y = y ^= opd (var x)

------------------------------------------------------------------------
-- Run lemmas.  `push iT1 iHd iCd` moves the head register onto the todo
-- stack (leaving the register nil), and `pop` is its inverse.

push-hd-cd : ∀ cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot
  → push iT1 iHd iCd
      ⊢ emb (mkI cd       dn vl tg ag nil t2 h   vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI (h ∙ cd) dn vl tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
push-hd-cd cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self cd))
    (e-seq (e-ass refl (rupd-self h))
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (h ∙ cd))))))

pop-hd-cd : ∀ cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot
  → pop iT1 iHd iCd
      ⊢ emb (mkI (h ∙ cd) dn vl tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd       dn vl tg ag nil t2 h   vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
pop-hd-cd cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self (h ∙ cd)))
    (e-seq (e-ass refl refl)
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (h ∙ cd))))))

push-hd-dn : ∀ cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot
  → push iT1 iHd iDn
      ⊢ emb (mkI cd dn       vl tg ag nil t2 h   vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd (h ∙ dn) vl tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
push-hd-dn cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self dn))
    (e-seq (e-ass refl (rupd-self h))
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (h ∙ dn))))))

pop-hd-dn : ∀ cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot
  → pop iT1 iHd iDn
      ⊢ emb (mkI cd (h ∙ dn) vl tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn       vl tg ag nil t2 h   vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
pop-hd-dn cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self (h ∙ dn)))
    (e-seq (e-ass refl refl)
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (h ∙ dn))))))

-- copying into a nil slot, and clearing it again (the same command: `^=` is a
-- partial involution, which is how the interpreter uncomputes)

cpy-hd-vv : ∀ cd dn vl tg ag t1 t2 h kk cn rv el ww a1 a2 t3 etg ot
  → cpy iHd iVv
      ⊢ emb (mkI cd dn vl tg ag t1 t2 h nil kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag t1 t2 h h   kk cn rv el ww a1 a2 t3 etg ot) ∣ 1
cpy-hd-vv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = e-ass refl refl

cpy-hd-vv-clr : ∀ cd dn vl tg ag t1 t2 h kk cn rv el ww a1 a2 t3 etg ot
  → cpy iHd iVv
      ⊢ emb (mkI cd dn vl tg ag t1 t2 h h   kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag t1 t2 h nil kk cn rv el ww a1 a2 t3 etg ot) ∣ 1
cpy-hd-vv-clr _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ = e-ass refl (rupd-self h)

------------------------------------------------------------------------
-- GENERIC push / pop (brick B1/B2).
--
-- The lemmas above are stated at fixed register triples, which does not
-- scale to the eleven dispatch cases.  These two state the same runs for
-- ARBITRARY distinct registers over an ARBITRARY store, using only the
-- separation laws of RWhileSIWf.  At a concrete interpreter store the
-- resulting `set`-chain computes back to a concrete slot list, so every
-- instance is one line (the distinctness proofs are `λ ()`).

push-gen : ∀ (σ : Store) (t x s : ℕ) (vx vs : V)
  → ¬ (t ≡ x) → ¬ (t ≡ s) → ¬ (x ≡ s)
  → get σ t ≡ nil → get σ x ≡ vx → get σ s ≡ vs
  → push t x s
      ⊢ σ ⇒ set (set (set (set (set σ t (vx ∙ vs)) s nil) x nil) s (vx ∙ vs)) t nil ∣ 9
push-gen σ t x s vx vs ntx nts nxs gt gx gs =
  e-seq (e-ass ev1 ru1)
   (e-seq (e-ass ev2 ru2)
    (e-seq (e-ass ev3 ru3)
     (e-seq (e-ass ev4 ru4)
            (e-ass ev5 ru5))))
  where
    v : V
    v = vx ∙ vs
    nst : ¬ (s ≡ t)
    nst e = nts (sym e)
    nxt : ¬ (x ≡ t)
    nxt e = ntx (sym e)
    nsx : ¬ (s ≡ x)
    nsx e = nxs (sym e)

    σ₁ σ₂ σ₃ σ₄ : Store
    σ₁ = set σ  t v
    σ₂ = set σ₁ s nil
    σ₃ = set σ₂ x nil
    σ₄ = set σ₃ s v

    ev1 : evalE σ (cns (var x) (var s)) ≡ just v
    ev1 rewrite gx | gs = refl
    ru1 : rupd (get σ t) v ≡ just v
    ru1 rewrite gt = refl

    g₁t : get σ₁ t ≡ v
    g₁t = get-set-≡ σ t v
    g₁s : get σ₁ s ≡ vs
    g₁s = trans (get-set-≢ σ t s v nts) gs
    g₁x : get σ₁ x ≡ vx
    g₁x = trans (get-set-≢ σ t x v ntx) gx

    ev2 : evalE σ₁ (tlE (var t)) ≡ just vs
    ev2 rewrite g₁t = refl
    ru2 : rupd (get σ₁ s) vs ≡ just nil
    ru2 rewrite g₁s = rupd-self vs

    g₂t : get σ₂ t ≡ v
    g₂t = trans (get-set-≢ σ₁ s t nil nst) g₁t
    g₂x : get σ₂ x ≡ vx
    g₂x = trans (get-set-≢ σ₁ s x nil nsx) g₁x
    g₂s : get σ₂ s ≡ nil
    g₂s = get-set-≡ σ₁ s nil

    ev3 : evalE σ₂ (hdE (var t)) ≡ just vx
    ev3 rewrite g₂t = refl
    ru3 : rupd (get σ₂ x) vx ≡ just nil
    ru3 rewrite g₂x = rupd-self vx

    g₃t : get σ₃ t ≡ v
    g₃t = trans (get-set-≢ σ₂ x t nil nxt) g₂t
    g₃s : get σ₃ s ≡ nil
    g₃s = trans (get-set-≢ σ₂ x s nil nxs) g₂s

    ev4 : evalE σ₃ (opd (var t)) ≡ just v
    ev4 rewrite g₃t = refl
    ru4 : rupd (get σ₃ s) v ≡ just v
    ru4 rewrite g₃s = refl

    g₄s : get σ₄ s ≡ v
    g₄s = get-set-≡ σ₃ s v
    g₄t : get σ₄ t ≡ v
    g₄t = trans (get-set-≢ σ₃ s t v nst) g₃t

    ev5 : evalE σ₄ (opd (var s)) ≡ just v
    ev5 rewrite g₄s = refl
    ru5 : rupd (get σ₄ t) v ≡ just nil
    ru5 rewrite g₄t = rupd-self v

pop-gen : ∀ (σ : Store) (t x s : ℕ) (vx vs : V)
  → ¬ (t ≡ x) → ¬ (t ≡ s) → ¬ (x ≡ s)
  → get σ t ≡ nil → get σ x ≡ nil → get σ s ≡ (vx ∙ vs)
  → pop t x s
      ⊢ σ ⇒ set (set (set (set (set σ t (vx ∙ vs)) s nil) x vx) s vs) t nil ∣ 9
pop-gen σ t x s vx vs ntx nts nxs gt gx gs =
  e-seq (e-ass ev1 ru1)
   (e-seq (e-ass ev2 ru2)
    (e-seq (e-ass ev3 ru3)
     (e-seq (e-ass ev4 ru4)
            (e-ass ev5 ru5))))
  where
    v : V
    v = vx ∙ vs
    nst : ¬ (s ≡ t)
    nst e = nts (sym e)
    nxt : ¬ (x ≡ t)
    nxt e = ntx (sym e)
    nsx : ¬ (s ≡ x)
    nsx e = nxs (sym e)

    σ₁ σ₂ σ₃ σ₄ : Store
    σ₁ = set σ  t v
    σ₂ = set σ₁ s nil
    σ₃ = set σ₂ x vx
    σ₄ = set σ₃ s vs

    ev1 : evalE σ (opd (var s)) ≡ just v
    ev1 rewrite gs = refl
    ru1 : rupd (get σ t) v ≡ just v
    ru1 rewrite gt = refl

    g₁t : get σ₁ t ≡ v
    g₁t = get-set-≡ σ t v
    g₁s : get σ₁ s ≡ v
    g₁s = trans (get-set-≢ σ t s v nts) gs
    g₁x : get σ₁ x ≡ nil
    g₁x = trans (get-set-≢ σ t x v ntx) gx

    ev2 : evalE σ₁ (opd (var t)) ≡ just v
    ev2 rewrite g₁t = refl
    ru2 : rupd (get σ₁ s) v ≡ just nil
    ru2 rewrite g₁s = rupd-self v

    g₂t : get σ₂ t ≡ v
    g₂t = trans (get-set-≢ σ₁ s t nil nst) g₁t
    g₂x : get σ₂ x ≡ nil
    g₂x = trans (get-set-≢ σ₁ s x nil nsx) g₁x
    g₂s : get σ₂ s ≡ nil
    g₂s = get-set-≡ σ₁ s nil

    ev3 : evalE σ₂ (hdE (var t)) ≡ just vx
    ev3 rewrite g₂t = refl
    ru3 : rupd (get σ₂ x) vx ≡ just vx
    ru3 rewrite g₂x = refl

    g₃t : get σ₃ t ≡ v
    g₃t = trans (get-set-≢ σ₂ x t vx nxt) g₂t
    g₃s : get σ₃ s ≡ nil
    g₃s = trans (get-set-≢ σ₂ x s vx nxs) g₂s
    g₃x : get σ₃ x ≡ vx
    g₃x = get-set-≡ σ₂ x vx

    ev4 : evalE σ₃ (tlE (var t)) ≡ just vs
    ev4 rewrite g₃t = refl
    ru4 : rupd (get σ₃ s) vs ≡ just vs
    ru4 rewrite g₃s = refl

    g₄x : get σ₄ x ≡ vx
    g₄x = trans (get-set-≢ σ₃ s x vs nsx) g₃x
    g₄s : get σ₄ s ≡ vs
    g₄s = get-set-≡ σ₃ s vs
    g₄t : get σ₄ t ≡ v
    g₄t = trans (get-set-≢ σ₃ s t vs nst) g₃t

    ev5 : evalE σ₄ (cns (var x) (var s)) ≡ just v
    ev5 rewrite g₄x | g₄s = refl
    ru5 : rupd (get σ₄ t) v ≡ just nil
    ru5 rewrite g₄t = rupd-self v

-- Instantiation template (this is how every dispatch case of P4 will use the
-- generic lemmas): at a concrete interpreter store the `set`-chain computes,
-- and the three distinctness proofs are `λ ()`.
push-gen-cd : ∀ cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot
  → push iT1 iHd iCd
      ⊢ emb (mkI cd       dn vl tg ag nil t2 h   vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI (h ∙ cd) dn vl tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
push-gen-cd cd dn vl tg ag t2 h vv kk cn rv el ww a1 a2 t3 etg ot =
  push-gen (emb (mkI cd dn vl tg ag nil t2 h vv kk cn rv el ww a1 a2 t3 etg ot))
           iT1 iHd iCd h cd (λ ()) (λ ()) (λ ()) refl refl refl
