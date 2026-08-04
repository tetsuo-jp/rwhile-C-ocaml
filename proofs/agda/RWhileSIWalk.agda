{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick P2 (forward half): the OBJECT-STORE WALK.
--
-- The interpreter keeps the object store as the value `Vl` -- a cons-list of
-- the object variables' values, exactly `ri.rwhile`'s `Vl` (there declared
-- with M >= 75 slots).  Reading or updating object variable `k` therefore
-- means WALKING `k` cells down that list, which is the only place where the
-- interpreter's per-step cost depends on the object program: it makes the
-- constant `C` of RWhileSIProg.Realises AFFINE in the store size M, hence
-- Jones' program-dependent constant `a_p`.
--
-- The walk is `ri.rwhile`'s `AUX` macro, spelled with the P1 macros:
--
--     from (=? Cn nil) do skip
--     loop  ( pop T1 Hd Vl ;      -- Hd := head of Vl, Vl := tail
--             push T1 Hd Rv ;     -- Rv := Hd . Rv  (the walked prefix)
--             push T1 Hd Cn )     -- Cn := (nil . Cn)   i.e. Cn := Cn+1
--     until (=? Cn Kk)
--
-- (`Cn := Cn+1` is a push of the nil-valued register onto the counter -- the
-- same macro, which is why the walk needs no extra code.)
--
-- THEOREM `walk-run`: starting with `Vl` holding `pre ++ post`, the counter at
-- 0 and the target index `Kk = |pre|`, the loop ends with `Vl = post`, the
-- prefix reversed onto `Rv`, and it costs exactly `30·|pre| + 2` steps --
-- linear in the index walked, i.e. ≤ 30·M + 1 for a store of M variables.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIWalk where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import RWhileTime
open import RWhileSIEnc using (num; encS)
open import RWhileSIMac

------------------------------------------------------------------------
-- More P1 run lemmas: the stacks the walk uses.

pop-hd-vl : ∀ cd dn v vs tg ag t2 vv kk cn rv el ww a1 a2 t3 etg ot
  → pop iT1 iHd iVl
      ⊢ emb (mkI cd dn (v ∙ vs) tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vs       tg ag nil t2 v   vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
pop-hd-vl cd dn v vs tg ag t2 vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self (v ∙ vs)))
    (e-seq (e-ass refl refl)
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (v ∙ vs))))))

push-hd-vl : ∀ cd dn vs tg ag t2 v vv kk cn rv el ww a1 a2 t3 etg ot
  → push iT1 iHd iVl
      ⊢ emb (mkI cd dn vs       tg ag nil t2 v   vv kk cn rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (v ∙ vs) tg ag nil t2 nil vv kk cn rv el ww a1 a2 t3 etg ot) ∣ 9
push-hd-vl cd dn vs tg ag t2 v vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self vs))
    (e-seq (e-ass refl (rupd-self v))
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (v ∙ vs))))))

push-hd-rv : ∀ cd dn vl tg ag t2 v vv kk cn rv el ww a1 a2 t3 etg ot
  → push iT1 iHd iRv
      ⊢ emb (mkI cd dn vl tg ag nil t2 v   vv kk cn rv       el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag nil t2 nil vv kk cn (v ∙ rv) el ww a1 a2 t3 etg ot) ∣ 9
push-hd-rv cd dn vl tg ag t2 v vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self rv))
    (e-seq (e-ass refl (rupd-self v))
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (v ∙ rv))))))

-- incrementing the counter IS a push of the (nil) head register
inc-cn : ∀ cd dn vl tg ag t2 vv kk cn rv el ww a1 a2 t3 etg ot
  → push iT1 iHd iCn
      ⊢ emb (mkI cd dn vl tg ag nil t2 nil vv kk cn         rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag nil t2 nil vv kk (nil ∙ cn) rv el ww a1 a2 t3 etg ot) ∣ 9
inc-cn cd dn vl tg ag t2 vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self cn))
    (e-seq (e-ass refl refl)
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (nil ∙ cn))))))

------------------------------------------------------------------------
-- Numerals: the loop's exit test compares the counter with the target index.

num-eq : ∀ j → eqV (num j) (num j) ≡ true
num-eq j = eqV-refl (num j)

num-neq : ∀ j n → eqV (num j) (num (suc (j + n))) ≡ false
num-neq zero    n = refl
num-neq (suc j) n = num-neq j n

------------------------------------------------------------------------
-- The walk.

wbody : Cmd
wbody = pop iT1 iHd iVl ⨾ push iT1 iHd iRv ⨾ push iT1 iHd iCn

walk : Cmd
walk = loop (eqE (var iCn) (cst nil)) skip wbody (eqE (var iCn) (var iKk))

-- the walked prefix, reversed onto an accumulator
revOnto : List V → V → V
revOnto []       acc = acc
revOnto (v ∷ vs) acc = revOnto vs (v ∙ acc)

wbody-run : ∀ cd dn v vs tg ag t2 vv kk j rv el ww a1 a2 t3 etg ot
  → wbody
      ⊢ emb (mkI cd dn (v ∙ vs) tg ag nil t2 nil vv kk (num j)       rv       el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vs       tg ag nil t2 nil vv kk (num (suc j)) (v ∙ rv) el ww a1 a2 t3 etg ot)
      ∣ 29
wbody-run cd dn v vs tg ag t2 vv kk j rv el ww a1 a2 t3 etg ot =
  e-seq (pop-hd-vl  cd dn v vs tg ag t2 vv kk (num j) rv el ww a1 a2 t3 etg ot)
   (e-seq (push-hd-rv cd dn vs tg ag t2 v vv kk (num j) rv el ww a1 a2 t3 etg ot)
          (inc-cn     cd dn vs tg ag t2 vv kk (num j) (v ∙ rv) el ww a1 a2 t3 etg ot))

------------------------------------------------------------------------
-- The iteration chain: walking `pre` while the counter climbs from j to
-- j + |pre|, with the target index fixed at `num (j + |pre|)`.

walk-rest : ∀ (pre post : List V) (j : ℕ) cd dn tg ag t2 vv rv el ww a1 a2 t3 etg ot
  → Rest (eqE (var iCn) (cst nil)) skip wbody (eqE (var iCn) (var iKk))
      (emb (mkI cd dn (encS (pre ++ post)) tg ag nil t2 nil vv
                (num (j + length pre)) (num j) rv el ww a1 a2 t3 etg ot))
      (emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                (num (j + length pre)) (num (j + length pre)) (revOnto pre rv) el ww a1 a2 t3 etg ot))
      (length pre * 30)
walk-rest [] post j cd dn tg ag t2 vv rv el ww a1 a2 t3 etg ot
  rewrite +-identityʳ j = r-exit exit
  where
    exit : evalT (emb (mkI cd dn (encS post) tg ag nil t2 nil vv (num j) (num j) rv el ww a1 a2 t3 etg ot))
                 (eqE (var iCn) (var iKk)) ≡ just true
    exit rewrite num-eq j = refl
walk-rest (v ∷ pre) post j cd dn tg ag t2 vv rv el ww a1 a2 t3 etg ot
  rewrite +-suc j (length pre) =
  r-iter notyet
         (wbody-run cd dn v (encS (pre ++ post)) tg ag t2 vv
                    (num (suc (j + length pre))) j rv el ww a1 a2 t3 etg ot)
         notnil
         e-skip
         (walk-rest pre post (suc j) cd dn tg ag t2 vv (v ∙ rv) el ww a1 a2 t3 etg ot)
  where
    notyet : evalT (emb (mkI cd dn (encS (v ∷ pre ++ post)) tg ag nil t2 nil vv
                             (num (suc (j + length pre))) (num j) rv el ww a1 a2 t3 etg ot))
                   (eqE (var iCn) (var iKk)) ≡ just false
    notyet rewrite num-neq j (length pre) = refl
    notnil : evalT (emb (mkI cd dn (encS (pre ++ post)) tg ag nil t2 nil vv
                             (num (suc (j + length pre))) (num (suc j)) (v ∙ rv) el ww a1 a2 t3 etg ot))
                   (eqE (var iCn) (cst nil)) ≡ just false
    notnil = refl

------------------------------------------------------------------------
-- The whole walk: entry assertion (counter at zero) + the chain.

walk-run : ∀ (pre post : List V) cd dn tg ag t2 vv rv el ww a1 a2 t3 etg ot
  → walk
      ⊢ emb (mkI cd dn (encS (pre ++ post)) tg ag nil t2 nil vv
                (num (length pre)) (num 0) rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                (num (length pre)) (num (length pre)) (revOnto pre rv) el ww a1 a2 t3 etg ot)
      ∣ suc (1 + length pre * 30)
walk-run pre post cd dn tg ag t2 vv rv el ww a1 a2 t3 etg ot =
  e-loop refl e-skip (walk-rest pre post 0 cd dn tg ag t2 vv rv el ww a1 a2 t3 etg ot)

------------------------------------------------------------------------
-- The RETURN walk: `Rv` is emptied back onto `Vl` and the counter runs down
-- to zero.  It is the inverse loop of `walk` (entry and exit tests swapped,
-- body inverted), i.e. `ri.rwhile`'s `INV-AUX`.

bbody : Cmd
bbody = pop iT1 iHd iCn ⨾ pop iT1 iHd iRv ⨾ push iT1 iHd iVl

back : Cmd
back = loop (eqE (var iCn) (var iKk)) skip bbody (eqE (var iCn) (cst nil))

-- decrementing the counter IS a pop into the (nil) head register
dec-cn : ∀ cd dn vl tg ag t2 vv kk cn rv el ww a1 a2 t3 etg ot
  → pop iT1 iHd iCn
      ⊢ emb (mkI cd dn vl tg ag nil t2 nil vv kk (nil ∙ cn) rv el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag nil t2 nil vv kk cn         rv el ww a1 a2 t3 etg ot) ∣ 9
dec-cn cd dn vl tg ag t2 vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self (nil ∙ cn)))
    (e-seq (e-ass refl refl)
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (nil ∙ cn))))))

pop-hd-rv : ∀ cd dn vl tg ag t2 v vv kk cn rv el ww a1 a2 t3 etg ot
  → pop iT1 iHd iRv
      ⊢ emb (mkI cd dn vl tg ag nil t2 nil vv kk cn (v ∙ rv) el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn vl tg ag nil t2 v   vv kk cn rv       el ww a1 a2 t3 etg ot) ∣ 9
pop-hd-rv cd dn vl tg ag t2 v vv kk cn rv el ww a1 a2 t3 etg ot =
  e-seq (e-ass refl refl)
   (e-seq (e-ass refl (rupd-self (v ∙ rv)))
    (e-seq (e-ass refl refl)
     (e-seq (e-ass refl refl)
            (e-ass refl (rupd-self (v ∙ rv))))))

bbody-run : ∀ cd dn v vs tg ag t2 vv kk n rv el ww a1 a2 t3 etg ot
  → bbody
      ⊢ emb (mkI cd dn vs       tg ag nil t2 nil vv kk (num (suc n)) (v ∙ rv) el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (v ∙ vs) tg ag nil t2 nil vv kk (num n)       rv       el ww a1 a2 t3 etg ot)
      ∣ 29
bbody-run cd dn v vs tg ag t2 vv kk n rv el ww a1 a2 t3 etg ot =
  e-seq (dec-cn     cd dn vs tg ag t2 vv kk (num n) (v ∙ rv) el ww a1 a2 t3 etg ot)
   (e-seq (pop-hd-rv  cd dn vs tg ag t2 v vv kk (num n) rv el ww a1 a2 t3 etg ot)
          (push-hd-vl cd dn vs tg ag t2 v vv kk (num n) rv el ww a1 a2 t3 etg ot))

-- reversing onto an accumulator, on lists
revApp : List V → List V → List V
revApp []       ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

-- `revOnto` (on values) is `revApp` (on lists) under the store encoding
revOnto-encS : ∀ pre acc → revOnto pre (encS acc) ≡ encS (revApp pre acc)
revOnto-encS []       acc = refl
revOnto-encS (v ∷ pre) acc = revOnto-encS pre (v ∷ acc)

-- walking out and back restores the store
revApp-revApp : ∀ (xs ys zs : List V) → revApp (revApp xs ys) zs ≡ revApp ys (xs ++ zs)
revApp-revApp []       ys zs = refl
revApp-revApp (x ∷ xs) ys zs = revApp-revApp xs (x ∷ ys) zs

back-rest : ∀ (rs post : List V) (K d : ℕ) → K ≡ length rs + d
  → ∀ cd dn tg ag t2 vv el ww a1 a2 t3 etg ot
  → Rest (eqE (var iCn) (var iKk)) skip bbody (eqE (var iCn) (cst nil))
      (emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                (num K) (num (length rs)) (encS rs) el ww a1 a2 t3 etg ot))
      (emb (mkI cd dn (encS (revApp rs post)) tg ag nil t2 nil vv
                (num K) (num 0) nil el ww a1 a2 t3 etg ot))
      (length rs * 30)
back-rest [] post K d eq cd dn tg ag t2 vv el ww a1 a2 t3 etg ot = r-exit refl
back-rest (v ∷ rs) post K d eq cd dn tg ag t2 vv el ww a1 a2 t3 etg ot =
  r-iter refl
         (bbody-run cd dn v (encS post) tg ag t2 vv (num K) (length rs) (encS rs) el ww a1 a2 t3 etg ot)
         notdone
         e-skip
         (back-rest rs (v ∷ post) K (suc d) eq′ cd dn tg ag t2 vv el ww a1 a2 t3 etg ot)
  where
    eq′ : K ≡ length rs + suc d
    eq′ = trans eq (sym (+-suc (length rs) d))
    notdone : evalT (emb (mkI cd dn (encS (v ∷ post)) tg ag nil t2 nil vv
                              (num K) (num (length rs)) (encS rs) el ww a1 a2 t3 etg ot))
                    (eqE (var iCn) (var iKk)) ≡ just false
    notdone rewrite eq′ | +-suc (length rs) d | num-neq (length rs) d = refl

back-run : ∀ (rs post : List V) cd dn tg ag t2 vv el ww a1 a2 t3 etg ot
  → back
      ⊢ emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                (num (length rs)) (num (length rs)) (encS rs) el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (encS (revApp rs post)) tg ag nil t2 nil vv
                (num (length rs)) (num 0) nil el ww a1 a2 t3 etg ot)
      ∣ suc (1 + length rs * 30)
back-run rs post cd dn tg ag t2 vv el ww a1 a2 t3 etg ot =
  e-loop entry e-skip
    (back-rest rs post (length rs) 0 (sym (+-identityʳ (length rs)))
               cd dn tg ag t2 vv el ww a1 a2 t3 etg ot)
  where
    entry : evalT (emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                            (num (length rs)) (num (length rs)) (encS rs) el ww a1 a2 t3 etg ot))
                  (eqE (var iCn) (var iKk)) ≡ just true
    entry rewrite num-eq (length rs) = refl
