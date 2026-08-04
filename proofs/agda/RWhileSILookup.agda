{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Brick P2c: LOOKUP and UPDATE -- reading and reversibly updating an object
-- variable, assembled from the walk of RWhileSIWalk.
--
--   lkE   = walk ; pop Vl→Hd ; Vv ^= Hd    ; push Hd→Vl ; back
--   updE  = walk ; pop Vl→Hd ; Hd ^= Vv    ; push Hd→Vl ; back
--
-- These are `ri.rwhile`'s `LOOKUP(Vl,J,X)` / `UPDATE(Vl,J,X)`.  Note what
-- makes the interpreter a *self*-interpreter of a *reversible* language: the
-- object program's reversible update `X ^= E` is implemented by the
-- interpreter's OWN reversible update (`Hd ^= Vv`), so the object-level
-- partial involution is inherited rather than simulated.
--
-- Cost: `56·k + 27` for object variable k, i.e. AFFINE in the store size M --
-- the sole source of the store-dependence of `Realises.C`.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSILookup where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-refl; ≤-reflexive)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

open import RWhileTime
open import RWhileSIEnc using (num; encS)
open import RWhileSIMac
open import RWhileSIWalk

------------------------------------------------------------------------
-- Bridging the two views of the walked prefix.

length-revApp : ∀ (xs ys : List V) → length (revApp xs ys) ≡ length xs + length ys
length-revApp []       ys = refl
length-revApp (x ∷ xs) ys rewrite length-revApp xs (x ∷ ys) = +-suc (length xs) (length ys)

length-rev0 : ∀ (xs : List V) → length (revApp xs []) ≡ length xs
length-rev0 xs = trans (length-revApp xs []) (+-identityʳ (length xs))

-- the walk, with its output prefix presented as an encoded list
walk-run0 : ∀ (pre post : List V) cd dn tg ag t2 vv el ww a1 a2 t3 etg ot
  → walk
      ⊢ emb (mkI cd dn (encS (pre ++ post)) tg ag nil t2 nil vv
                (num (length pre)) (num 0) nil el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
      ∣ suc (1 + length pre * 28)
walk-run0 pre post cd dn tg ag t2 vv el ww a1 a2 t3 etg ot
  rewrite sym (revOnto-encS pre []) =
  walk-run pre post cd dn tg ag t2 vv nil el ww a1 a2 t3 etg ot

-- the return walk, restoring the store
back-run0 : ∀ (pre post : List V) cd dn tg ag t2 vv el ww a1 a2 t3 etg ot
  → back
      ⊢ emb (mkI cd dn (encS post) tg ag nil t2 nil vv
                (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (encS (pre ++ post)) tg ag nil t2 nil vv
                (num (length pre)) (num 0) nil el ww a1 a2 t3 etg ot)
      ∣ suc (1 + length pre * 28)
back-run0 pre post cd dn tg ag t2 vv el ww a1 a2 t3 etg ot
  rewrite sym (revApp-revApp pre [] post) | sym (length-rev0 pre) =
  back-run (revApp pre []) post cd dn tg ag t2 vv el ww a1 a2 t3 etg ot

------------------------------------------------------------------------
-- LOOKUP: read object variable k (the k-th cell of Vl) into Vv.

lkE : Cmd
lkE = walk ⨾ pop iT1 iHd iVl ⨾ cpy iHd iVv ⨾ push iT1 iHd iVl ⨾ back

lk-run : ∀ (pre post : List V) (v : V) cd dn tg ag t2 el ww a1 a2 t3 etg ot
  → lkE
      ⊢ emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil nil
                (num (length pre)) (num 0) nil el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil v
                (num (length pre)) (num 0) nil el ww a1 a2 t3 etg ot)
      ∣ 3 + (length pre * 28 + (24 + length pre * 28))
lk-run pre post v cd dn tg ag t2 el ww a1 a2 t3 etg ot =
  e-seq (walk-run0 pre (v ∷ post) cd dn tg ag t2 nil el ww a1 a2 t3 etg ot)
   (e-seq (pop-hd-vl cd dn v (encS post) tg ag t2 nil
                     (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
    (e-seq (cpy-hd-vv cd dn (encS post) tg ag nil t2 v
                      (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
     (e-seq (push-hd-vl cd dn (encS post) tg ag t2 v v
                        (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
            (back-run0 pre (v ∷ post) cd dn tg ag t2 v el ww a1 a2 t3 etg ot))))

------------------------------------------------------------------------
-- UPDATE: apply the object-level reversible update to variable k, using the
-- interpreter's own `^=` -- this is where R-WHILE interprets itself.

updE : Cmd
updE = walk ⨾ pop iT1 iHd iVl ⨾ (iHd ^= opd (var iVv)) ⨾ push iT1 iHd iVl ⨾ back

upd-run : ∀ (pre post : List V) (v w u : V) cd dn tg ag t2 el ww a1 a2 t3 etg ot
  → rupd v w ≡ just u
  → updE
      ⊢ emb (mkI cd dn (encS (pre ++ v ∷ post)) tg ag nil t2 nil w
                (num (length pre)) (num 0) nil el ww a1 a2 t3 etg ot)
      ⇒ emb (mkI cd dn (encS (pre ++ u ∷ post)) tg ag nil t2 nil w
                (num (length pre)) (num 0) nil el ww a1 a2 t3 etg ot)
      ∣ 3 + (length pre * 28 + (24 + length pre * 28))
upd-run pre post v w u cd dn tg ag t2 el ww a1 a2 t3 etg ot ru =
  e-seq (walk-run0 pre (v ∷ post) cd dn tg ag t2 w el ww a1 a2 t3 etg ot)
   (e-seq (pop-hd-vl cd dn v (encS post) tg ag t2 w
                     (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
    (e-seq (e-ass refl ru)
     (e-seq (push-hd-vl cd dn (encS post) tg ag t2 u w
                        (num (length pre)) (num (length pre)) (encS (revApp pre [])) el ww a1 a2 t3 etg ot)
            (back-run0 pre (u ∷ post) cd dn tg ag t2 w el ww a1 a2 t3 etg ot))))

------------------------------------------------------------------------
-- Connecting the split view (pre ++ v ∷ post) with the store operations
-- `get`/`set` at index k, and a splitting lemma for in-range indices.

get-split : ∀ (pre : List V) (v : V) (post : List V)
          → get (pre ++ v ∷ post) (length pre) ≡ v
get-split []       v post = refl
get-split (x ∷ pre) v post = get-split pre v post

set-split : ∀ (pre : List V) (v : V) (post : List V) (u : V)
          → set (pre ++ v ∷ post) (length pre) u ≡ pre ++ u ∷ post
set-split []        v post u = refl
set-split (x ∷ pre) v post u = cong (x ∷_) (set-split pre v post u)

-- every in-range index splits the store
split : ∀ (σ : List V) (k : ℕ) → k Data.Nat.< length σ
      → Σ[ pre ∈ List V ] Σ[ v ∈ V ] Σ[ post ∈ List V ]
          ((σ ≡ pre ++ v ∷ post) × (length pre ≡ k))
split (x ∷ σ) zero    _        = [] , x , σ , refl , refl
split (x ∷ σ) (suc k) (s≤s lt) with split σ k lt
... | pre , v , post , eq , len =
      x ∷ pre , v , post , cong (x ∷_) eq , cong suc len

------------------------------------------------------------------------
-- The cost, in closed form: 56·k + 27.

lk-cost : ∀ k → 3 + (k * 28 + (24 + k * 28)) ≡ k * 56 + 27
lk-cost = solve 1 (λ k → con 3 :+ (k :* con 28 :+ (con 24 :+ k :* con 28))
                      := k :* con 56 :+ con 27) refl
