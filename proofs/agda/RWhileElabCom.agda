{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Command-level translation correctness (R-WHILE -> R-CORE), FULL control.
--
-- Completing the "small core + semantics-preserving translation" methodology
-- at the CONTROL level (RWhileCoreExp did expressions/patterns).
--
-- The command-level desugaring is the OPTIONAL branch: R-WHILE's omitted
-- branches (BThenNone / BElseNone / BDoNone / BLoopNone) elaborate to a SKIP.
-- We model source commands `SCom` with optional branches (`Maybe SCom`),
-- elaborate them into RWhileRevFull's core `Cmd` (an empty branch becomes the
-- identity atom `Id` = skip), and prove the elaboration preserves the big-step
-- semantics for atom / seq / the reversible conditional AND the reversible loop:
--
--   elab-sound    : c ⊨ s ⇒ t → elab c ⊢ s ⇒ t
--   elab-complete : elab c ⊢ s ⇒ t → c ⊨ s ⇒ t
------------------------------------------------------------------------

module RWhileElabCom where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import RWhileRevFull

module Elab (S : Set) where
  open RWhileRevFull.Core S

  Id : Rel
  Id s t = s ≡ t

  ----------------------------------------------------------------------
  -- SOURCE commands with optional branches, and elaboration to the core
  -- (an omitted branch becomes `atom Id` = skip).

  data SCom : Set₁ where
    sAtom : Rel → SCom
    sSeq  : SCom → SCom → SCom
    sCond : (S → Bool) → Maybe SCom → Maybe SCom → (S → Bool) → SCom
    sLoop : (S → Bool) → Maybe SCom → Maybe SCom → (S → Bool) → SCom

  elabM : Maybe SCom → Cmd
  elab  : SCom → Cmd
  elabM nothing  = atom Id
  elabM (just c) = elab c
  elab (sAtom A)        = atom A
  elab (sSeq c d)       = elab c ⨾ elab d
  elab (sCond e t el f) = cond e (elabM t) (elabM el) f
  elab (sLoop e d l f)  = loop e (elabM d) (elabM l) f

  ----------------------------------------------------------------------
  -- SOURCE big-step semantics.  `Br` runs an optional branch (omitted = skip);
  -- `sRest` is the loop iteration (mirrors RWhileRevFull.Rest).

  data _⊨_⇒_ : SCom → S → S → Set₁
  data Br : Maybe SCom → S → S → Set₁
  data sRest (e : S → Bool) (d l : Maybe SCom) (f : S → Bool) : S → S → Set₁

  data Br where
    br-skip : ∀ {s} → Br nothing s s
    br-cmd  : ∀ {c s t} → c ⊨ s ⇒ t → Br (just c) s t

  data _⊨_⇒_ where
    s-atom : ∀ {A s t} → A s t → sAtom A ⊨ s ⇒ t
    s-seq  : ∀ {c d s u t} → c ⊨ s ⇒ u → d ⊨ u ⇒ t → sSeq c d ⊨ s ⇒ t
    s-cond-t : ∀ {e t el f s u} → e s ≡ true  → Br t  s u → f u ≡ true  → sCond e t el f ⊨ s ⇒ u
    s-cond-e : ∀ {e t el f s u} → e s ≡ false → Br el s u → f u ≡ false → sCond e t el f ⊨ s ⇒ u
    s-loop : ∀ {e d l f s u v} → e s ≡ true → Br d s u → sRest e d l f u v → sLoop e d l f ⊨ s ⇒ v

  data sRest e d l f where
    sr-exit : ∀ {w} → f w ≡ true → sRest e d l f w w
    sr-iter : ∀ {w u v x} → f w ≡ false → Br l w u → e u ≡ false → Br d u v
            → sRest e d l f v x → sRest e d l f w x

  ----------------------------------------------------------------------
  -- elaboration preserves semantics (sound direction).

  elab-sound : ∀ {c s t} → c ⊨ s ⇒ t → elab c ⊢ s ⇒ t
  br-sound   : ∀ {m s t} → Br m s t → elabM m ⊢ s ⇒ t
  rest-sound : ∀ {e d l f w u} → sRest e d l f w u → Rest e (elabM d) (elabM l) f w u

  br-sound br-skip      = e-atom refl
  br-sound (br-cmd c)   = elab-sound c

  elab-sound (s-atom a)          = e-atom a
  elab-sound (s-seq cs ds)       = e-seq (elab-sound cs) (elab-sound ds)
  elab-sound (s-cond-t es bt ft) = e-then es (br-sound bt) ft
  elab-sound (s-cond-e es be ft) = e-else es (br-sound be) ft
  elab-sound (s-loop es bd rest) = e-loop es (br-sound bd) (rest-sound rest)

  rest-sound (sr-exit fw)              = r-exit fw
  rest-sound (sr-iter fw bl eu bd rs)  = r-iter fw (br-sound bl) eu (br-sound bd) (rest-sound rs)

  ----------------------------------------------------------------------
  -- elaboration preserves semantics (complete direction).

  elab-complete : ∀ c {s t} → elab c ⊢ s ⇒ t → c ⊨ s ⇒ t
  br-complete   : ∀ m {s t} → elabM m ⊢ s ⇒ t → Br m s t
  rest-complete : ∀ {e f} d l {w u} → Rest e (elabM d) (elabM l) f w u → sRest e d l f w u

  br-complete nothing  (e-atom refl) = br-skip
  br-complete (just c) der           = br-cmd (elab-complete c der)

  elab-complete (sAtom A)        (e-atom a)        = s-atom a
  elab-complete (sSeq c d)       (e-seq cs ds)     = s-seq (elab-complete c cs) (elab-complete d ds)
  elab-complete (sCond e t el f) (e-then es bt ft) = s-cond-t es (br-complete t bt) ft
  elab-complete (sCond e t el f) (e-else es be ft) = s-cond-e es (br-complete el be) ft
  elab-complete (sLoop e d l f)  (e-loop es bd rest) =
    s-loop es (br-complete d bd) (rest-complete d l rest)

  rest-complete d l (r-exit fw)              = sr-exit fw
  rest-complete d l (r-iter fw lw eu dv rs)  =
    sr-iter fw (br-complete l lw) eu (br-complete d dv) (rest-complete d l rs)
