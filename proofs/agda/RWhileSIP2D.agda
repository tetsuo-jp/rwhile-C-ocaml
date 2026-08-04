{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- DIFFERENTIAL TEST against the OCaml implementation's `-p2d`.
--
-- `RWhileSIEnc.⌜_⌝` is a UNIFORM encoding (every expression is
-- `(tag . (o1 . o2))`), chosen to keep the interpreter's dispatch regular.
-- `src/Program2DataRwhile.ml` uses a NON-uniform one (`('hd . e)` has a
-- single field, a bare operand is written without a wrapper, `'cond`/`'loop`
-- carry a trailing nil, constants are tagged `'val`).
--
-- To make sure the formalisation is talking about the real encoding and not
-- an idealised one, this module MODELS the implementation's encoder in Agda
-- (`⌜_⌝ᵖ`), prints it in the implementation's concrete syntax (`showV`), and
-- checks the result against the actual output of `./ri -p2d` -- verbatim,
-- with the type checker doing the comparison.
--
-- Correspondence (implementation ↔ this development), verified below:
--
--   variable index      ('var . num k)         impl. numbers from 1, Agda from 0
--   constant            ('val . v)             ⌜ cst v ⌝ᵒ = ('cst . v)   [name only]
--   bare operand E      ('var . ..)/('val . ..) uniform: ('opd . (o . dummy))
--   cons/=?             (tag . (o1 . o2))      same
--   hd/tl/pair?         (tag . o)              uniform: (tag . (o . dummy))
--   X ^= E              ('ass . (('var . k) . E))          same
--   C ; D               ('seq . (C . D))                   same
--   if/from             (tag . (e . (C . (D . (f . nil))))) uniform: no trailing nil
--   skip                ('ass . (('var . nil) . ('val . nil)))  -- the impl's
--                       `doNothing`; costs 1 step, exactly like `skip`
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIP2D where

open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RWhileTime
open import RWhileSIEnc using (num; ⌜_⌝ᵒ; ⌜_⌝ᵉ; ⌜_⌝; dummyOpd; t-var; t-cst; t-cns
                             ; t-hd; t-tl; t-eq; t-pr; t-opd; t-ass; t-seq; t-cond; t-loop)

------------------------------------------------------------------------
-- The implementation's encoder, modelled.

⌜_⌝ᵖᵒ : Opd → V
⌜ var x ⌝ᵖᵒ = atm t-var ∙ num x
⌜ cst v ⌝ᵖᵒ = atm t-cst ∙ v          -- printed `'val`

⌜_⌝ᵖᵉ : Exp → V
⌜ opd a   ⌝ᵖᵉ = ⌜ a ⌝ᵖᵒ              -- no wrapper
⌜ cns a b ⌝ᵖᵉ = atm t-cns ∙ (⌜ a ⌝ᵖᵒ ∙ ⌜ b ⌝ᵖᵒ)
⌜ hdE a   ⌝ᵖᵉ = atm t-hd  ∙ ⌜ a ⌝ᵖᵒ  -- single field
⌜ tlE a   ⌝ᵖᵉ = atm t-tl  ∙ ⌜ a ⌝ᵖᵒ
⌜ eqE a b ⌝ᵖᵉ = atm t-eq  ∙ (⌜ a ⌝ᵖᵒ ∙ ⌜ b ⌝ᵖᵒ)
⌜ prE a   ⌝ᵖᵉ = atm t-pr  ∙ ⌜ a ⌝ᵖᵒ

⌜_⌝ᵖ : Cmd → V
⌜ skip ⌝ᵖ           = atm t-ass ∙ ((atm t-var ∙ nil) ∙ (atm t-cst ∙ nil))
⌜ x ^= e ⌝ᵖ         = atm t-ass ∙ ((atm t-var ∙ num x) ∙ ⌜ e ⌝ᵖᵉ)
⌜ c ⨾ d ⌝ᵖ          = atm t-seq ∙ (⌜ c ⌝ᵖ ∙ ⌜ d ⌝ᵖ)
⌜ cond e c d f ⌝ᵖ   = atm t-cond ∙ (⌜ e ⌝ᵖᵉ ∙ (⌜ c ⌝ᵖ ∙ (⌜ d ⌝ᵖ ∙ (⌜ f ⌝ᵖᵉ ∙ nil))))
⌜ loop e D L f ⌝ᵖ   = atm t-loop ∙ (⌜ e ⌝ᵖᵉ ∙ (⌜ D ⌝ᵖ ∙ (⌜ L ⌝ᵖ ∙ (⌜ f ⌝ᵖᵉ ∙ nil))))

-- the whole program: (input var . (command . output var))
progV : ℕ → Cmd → ℕ → V
progV x c y = (atm t-var ∙ num x) ∙ (⌜ c ⌝ᵖ ∙ (atm t-var ∙ num y))

------------------------------------------------------------------------
-- Printing, in the implementation's concrete syntax.

tagName : ℕ → String
tagName 0  = "'var"
tagName 1  = "'val"
tagName 3  = "'cons"
tagName 4  = "'hd"
tagName 5  = "'tl"
tagName 6  = "'eq"
tagName 7  = "'pairp"
tagName 8  = "'ass"
tagName 9  = "'seq"
tagName 10 = "'cond"
tagName 11 = "'loop"
tagName _  = "'?"

showV : V → String
showV nil     = "nil"
showV (atm n) = tagName n
showV (a ∙ b) = "(" ++ showV a ++ " . " ++ showV b ++ ")"

------------------------------------------------------------------------
-- The tests.  Each right-hand side is the VERBATIM output of
--     cd src && ./ri -p2d <prog>
-- for the program named in the comment (the implementation numbers the
-- variables from 1 in reverse order of appearance, so X ↦ Agda index 1 and
-- Y ↦ 0 in a two-variable program).

private
  -- read X;  X ^= Y;  write X
  d-ass : showV (progV 1 (1 ^= opd (var 0)) 1)
         ≡ "(('var . (nil . nil)) . (('ass . (('var . (nil . nil)) . ('var . nil))) . ('var . (nil . nil))))"
  d-ass = refl

  -- read X;  X ^= cons Y Z;  write X
  d-cons : showV (progV 2 (2 ^= cns (var 1) (var 0)) 2)
         ≡ "(('var . (nil . (nil . nil))) . (('ass . (('var . (nil . (nil . nil))) . ('cons . (('var . (nil . nil)) . ('var . nil))))) . ('var . (nil . (nil . nil)))))"
  d-cons = refl

  -- read X;  X ^= hd Y;  write X
  d-hd : showV (progV 1 (1 ^= hdE (var 0)) 1)
        ≡ "(('var . (nil . nil)) . (('ass . (('var . (nil . nil)) . ('hd . ('var . nil)))) . ('var . (nil . nil))))"
  d-hd = refl

  -- read X;  X ^= pair? Y;  write X
  d-pairp : showV (progV 1 (1 ^= prE (var 0)) 1)
        ≡ "(('var . (nil . nil)) . (('ass . (('var . (nil . nil)) . ('pairp . ('var . nil)))) . ('var . (nil . nil))))"
  d-pairp = refl

  -- read X;  X ^= =? Y Z;  write X
  d-eq : showV (progV 2 (2 ^= eqE (var 1) (var 0)) 2)
        ≡ "(('var . (nil . (nil . nil))) . (('ass . (('var . (nil . (nil . nil))) . ('eq . (('var . (nil . nil)) . ('var . nil))))) . ('var . (nil . (nil . nil)))))"
  d-eq = refl

  -- read X;  X ^= Y; Y ^= Z;  write X
  d-seq : showV (progV 2 ((2 ^= opd (var 1)) ⨾ (1 ^= opd (var 0))) 2)
        ≡ "(('var . (nil . (nil . nil))) . (('seq . (('ass . (('var . (nil . (nil . nil))) . ('var . (nil . nil)))) . ('ass . (('var . (nil . nil)) . ('var . nil))))) . ('var . (nil . (nil . nil)))))"
  d-seq = refl

  -- read X;  if =? X Y then X ^= Y else Y ^= X fi =? X Y;  write X
  d-cond : showV (progV 1 (cond (eqE (var 1) (var 0)) (1 ^= opd (var 0)) (0 ^= opd (var 1))
                                (eqE (var 1) (var 0))) 1)
         ≡ "(('var . (nil . nil)) . (('cond . (('eq . (('var . (nil . nil)) . ('var . nil))) . (('ass . (('var . (nil . nil)) . ('var . nil))) . (('ass . (('var . nil) . ('var . (nil . nil)))) . (('eq . (('var . (nil . nil)) . ('var . nil))) . nil))))) . ('var . (nil . nil))))"
  d-cond = refl

  -- read X;  from =? X Y do X ^= Y loop Y ^= X until =? X Y;  write X
  d-loop : showV (progV 1 (loop (eqE (var 1) (var 0)) (1 ^= opd (var 0)) (0 ^= opd (var 1))
                                (eqE (var 1) (var 0))) 1)
         ≡ "(('var . (nil . nil)) . (('loop . (('eq . (('var . (nil . nil)) . ('var . nil))) . (('ass . (('var . (nil . nil)) . ('var . nil))) . (('ass . (('var . nil) . ('var . (nil . nil)))) . (('eq . (('var . (nil . nil)) . ('var . nil))) . nil))))) . ('var . (nil . nil))))"
  d-loop = refl

------------------------------------------------------------------------
-- FROM THE IMPLEMENTATION'S ENCODING TO THE UNIFORM ONE.
--
-- The two encodings carry the same information: a total translation turns
-- the implementation's output into what the verified interpreter eats.
-- Operands already agree (`('var . num k)` and `('cst . v)` = `('val . v)`),
-- so only the wrapping differs.
--
-- `skip` is the one command the implementation does not have; its `-p2d`
-- counterpart is `doNothing` = `X0 ^= nil`, which is a no-op exactly when
-- X0 is nil (and costs the same one step).  `deskip` makes that explicit.

p→uE : V → V
p→uE (atm 3 ∙ (a ∙ b)) = atm t-cns ∙ (a ∙ b)
p→uE (atm 4 ∙ a)       = atm t-hd  ∙ (a ∙ dummyOpd)
p→uE (atm 5 ∙ a)       = atm t-tl  ∙ (a ∙ dummyOpd)
p→uE (atm 6 ∙ (a ∙ b)) = atm t-eq  ∙ (a ∙ b)
p→uE (atm 7 ∙ a)       = atm t-pr  ∙ (a ∙ dummyOpd)
p→uE o                 = atm t-opd ∙ (o ∙ dummyOpd)

p→uC : V → V
p→uC (atm 8  ∙ ((atm 0 ∙ k) ∙ e))            = atm t-ass  ∙ (k ∙ p→uE e)
p→uC (atm 9  ∙ (c ∙ d))                      = atm t-seq  ∙ (p→uC c ∙ p→uC d)
p→uC (atm 10 ∙ (e ∙ (c ∙ (d ∙ (f ∙ nil))))) = atm t-cond ∙ (p→uE e ∙ (p→uC c ∙ (p→uC d ∙ p→uE f)))
p→uC (atm 11 ∙ (e ∙ (c ∙ (d ∙ (f ∙ nil))))) = atm t-loop ∙ (p→uE e ∙ (p→uC c ∙ (p→uC d ∙ p→uE f)))
p→uC v                                       = v

deskip : Cmd → Cmd
deskip skip           = 0 ^= opd (cst nil)
deskip (x ^= e)       = x ^= e
deskip (c ⨾ d)        = deskip c ⨾ deskip d
deskip (cond e c d f) = cond e (deskip c) (deskip d) f
deskip (loop e D L f) = loop e (deskip D) (deskip L) f

-- operands are encoded identically by both
opd-same : ∀ a → ⌜ a ⌝ᵖᵒ ≡ ⌜ a ⌝ᵒ
opd-same (var x) = refl
opd-same (cst v) = refl

private
  ∙₂ : ∀ {t a b c d} → a ≡ b → c ≡ d → (atm t ∙ (a ∙ c)) ≡ (atm t ∙ (b ∙ d))
  ∙₂ refl refl = refl

p→uE-ok : ∀ e → p→uE ⌜ e ⌝ᵖᵉ ≡ ⌜ e ⌝ᵉ
p→uE-ok (opd (var x)) = refl
p→uE-ok (opd (cst v)) = refl
p→uE-ok (cns a b)     = ∙₂ (opd-same a) (opd-same b)
p→uE-ok (hdE a)       = ∙₂ (opd-same a) refl
p→uE-ok (tlE a)       = ∙₂ (opd-same a) refl
p→uE-ok (eqE a b)     = ∙₂ (opd-same a) (opd-same b)
p→uE-ok (prE a)       = ∙₂ (opd-same a) refl

p→u-ok : ∀ c → p→uC ⌜ c ⌝ᵖ ≡ ⌜ deskip c ⌝
p→u-ok skip           = refl
p→u-ok (x ^= e)       = ∙-cong₂ refl (p→uE-ok e)
  where
    ∙-cong₂ : ∀ {a b c d} → a ≡ b → c ≡ d → (atm t-ass ∙ (a ∙ c)) ≡ (atm t-ass ∙ (b ∙ d))
    ∙-cong₂ refl refl = refl
p→u-ok (c ⨾ d)        = go (p→u-ok c) (p→u-ok d)
  where
    go : ∀ {a b c′ d′} → a ≡ b → c′ ≡ d′ → (atm t-seq ∙ (a ∙ c′)) ≡ (atm t-seq ∙ (b ∙ d′))
    go refl refl = refl
p→u-ok (cond e c d f) = go (p→uE-ok e) (p→u-ok c) (p→u-ok d) (p→uE-ok f)
  where
    go : ∀ {e₁ e₂ c₁ c₂ d₁ d₂ f₁ f₂} → e₁ ≡ e₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → f₁ ≡ f₂
       → (atm t-cond ∙ (e₁ ∙ (c₁ ∙ (d₁ ∙ f₁)))) ≡ (atm t-cond ∙ (e₂ ∙ (c₂ ∙ (d₂ ∙ f₂))))
    go refl refl refl refl = refl
p→u-ok (loop e D L f) = go (p→uE-ok e) (p→u-ok D) (p→u-ok L) (p→uE-ok f)
  where
    go : ∀ {e₁ e₂ c₁ c₂ d₁ d₂ f₁ f₂} → e₁ ≡ e₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → f₁ ≡ f₂
       → (atm t-loop ∙ (e₁ ∙ (c₁ ∙ (d₁ ∙ f₁)))) ≡ (atm t-loop ∙ (e₂ ∙ (c₂ ∙ (d₂ ∙ f₂))))
    go refl refl refl refl = refl
