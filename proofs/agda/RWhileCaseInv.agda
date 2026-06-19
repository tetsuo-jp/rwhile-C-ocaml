{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Soundness of the symmetric `case` sugar (Rwhile.cf CCase / src/Desugar.ml).
--
--   case Scrut yields Result of  InPat => Body => OutPat | ... | Rest end
--
-- desugars to a NEST of reversible conditionals: arm i becomes
--   cond (test InPat_i Scrut)
--        (InPat_i <= Scrut ; Body_i ; Result <= OutPat_i)
--        <rest>
--        (test OutPat_i Result)
-- and the last arm is the test-free fall-through.  We model the desugared form
-- with the verified reversible core of RWhileRev (atom / _⨾_ / cond) and prove
-- the two properties that justify `case` as a reversible construct:
--
--   1. case-reversible : the desugared case is reversible
--                        (a direct corollary of inv-sound).
--   2. inv-commute     : inverting a desugared case = desugaring the SWAPPED
--                        case (scrutinee<->result, each arm InPat<->OutPat, Body
--                        inverted) -- SEMANTICALLY (the two differ only by the
--                        associativity of ; that inversion introduces).  Hence
--                        the inverse of a `case` is again a `case`, matching how
--                        InvRwhile inverts the desugared CCond/CRep.
--   3. invArm-inv      : the per-arm swap is an involution (so invCase∘invCase=id).
--
-- `--safe`, no postulates/holes; reuses RWhileRev's machine-checked inv.
------------------------------------------------------------------------

module RWhileCaseInv where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import RWhileRev

module M (S : Set) where
  open RWhileRev.Core S

  ------------------------------------------------------------------------
  -- A case arm:  entry test e, read atom R (InPat <= Scrut), body B,
  -- write atom W (Result <= OutPat), exit test f.
  record Arm : Set₁ where
    constructor arm
    field e : S → Bool
          R : Rel
          B : Cmd
          W : Rel
          f : S → Bool

  -- the per-arm body:  InPat <= Scrut ; Body ; Result <= OutPat
  abody : Arm → Cmd
  abody (arm _ R B W _) = atom R ⨾ (B ⨾ atom W)

  -- desugar (first arm + rest): the last arm is the test-free fall-through.
  desugar : Arm → List Arm → Cmd
  desugar a []          = abody a
  desugar a (b ∷ rest)  = cond (Arm.e a) (abody a) (desugar b rest) (Arm.f a)

  -- per-arm inversion: swap entry/exit tests, swap read/write (converse), invert body.
  invArm : Arm → Arm
  invArm (arm e R B W f) = arm f (conv W) (inv B) (conv R) e

  ------------------------------------------------------------------------
  -- semantic equivalence of two core commands
  _≋_ : Cmd → Cmd → Set₁
  c ≋ d = ∀ {s t} → (c ⊢ s ⇒ t → d ⊢ s ⇒ t) × (d ⊢ s ⇒ t → c ⊢ s ⇒ t)

  -- associativity of sequencing (the only gap inversion introduces)
  seq-assoc : ∀ x y z → ((x ⨾ y) ⨾ z) ≋ (x ⨾ (y ⨾ z))
  seq-assoc x y z =
    (λ { (e-seq (e-seq xs ys) zs) → e-seq xs (e-seq ys zs) }) ,
    (λ { (e-seq xs (e-seq ys zs)) → e-seq (e-seq xs ys) zs })

  -- congruence: swapping the branches of a cond by ≋ preserves its runs
  cond-cong : ∀ {e f c c′ d d′} → c ≋ c′ → d ≋ d′
            → cond e c d f ≋ cond e c′ d′ f
  cond-cong cc dd =
    (λ { (e-then es cs ft) → e-then es (proj₁ cc cs) ft
       ; (e-else es ds ft) → e-else es (proj₁ dd ds) ft }) ,
    (λ { (e-then es cs ft) → e-then es (proj₂ cc cs) ft
       ; (e-else es ds ft) → e-else es (proj₂ dd ds) ft })
    where open Data.Product using (proj₁; proj₂)

  ------------------------------------------------------------------------
  -- body-level commute:  inv (abody a)  ≋  abody (invArm a)
  -- LHS = (atom(conv W) ⨾ inv B) ⨾ atom(conv R)   [left-nested, from inv]
  -- RHS =  atom(conv W) ⨾ (inv B ⨾ atom(conv R))  [right-nested, from desugar]
  body-commute : ∀ a → inv (abody a) ≋ abody (invArm a)
  body-commute (arm _ R B W _) = seq-assoc (atom (conv W)) (inv B) (atom (conv R))

  ------------------------------------------------------------------------
  -- MAIN: inverting a desugared case = desugaring the swapped case (semantically).
  inv-commute : ∀ a rest → inv (desugar a rest) ≋ desugar (invArm a) (map invArm rest)
  inv-commute a []          = body-commute a
  inv-commute a (b ∷ rest)  = cond-cong (body-commute a) (inv-commute b rest)

  ------------------------------------------------------------------------
  -- the desugared case is reversible (corollary of inv-sound).
  case-reversible : ∀ a rest {s t}
                  → desugar a rest ⊢ s ⇒ t → inv (desugar a rest) ⊢ t ⇒ s
  case-reversible a rest d = inv-sound d

  -- combined: running the SWAPPED case backwards undoes the original case.
  case-inv-undoes : ∀ a rest {s t}
                  → desugar a rest ⊢ s ⇒ t
                  → desugar (invArm a) (map invArm rest) ⊢ t ⇒ s
  case-inv-undoes a rest d =
    let open Data.Product using (proj₁)
    in proj₁ (inv-commute a rest) (inv-sound d)

  ------------------------------------------------------------------------
  -- the per-arm swap is an involution (hence invCase ∘ invCase = id).
  invArm-inv : ∀ a → invArm (invArm a) ≡ a
  invArm-inv (arm e R B W f) rewrite RWhileRev.Core.inv-inv S B = refl
