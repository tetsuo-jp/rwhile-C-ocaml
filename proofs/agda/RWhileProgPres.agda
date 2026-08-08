{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- p⁺ IN THE TIMED CORE: the construction, its specification, and its cost.
--
-- `src/Simp.ml: program_preserving` turns
--
--     read X; C; write Y      into      read X; C; emit; write OUT-PP
--
-- so that the new program computes  ⟦p⁺⟧ d = ⟨ ⌜p⌝ , ⟦p⟧ d ⟩ .  This is the
-- basis of REVERSIBLE Jones optimality (RWhileJonesRev): the fp1 residual of
-- a program-preserving interpreter has to emit ⌜p⌝ too, so `p` is the wrong
-- thing to compare it with and p⁺ is the right one.
--
-- Here the construction is carried out inside RWhileTime — the cost-annotated
-- semantics whose ℕ is exactly `./ri -steps` (one unit per executed command
-- node) — and three things are proved:
--
--   * `pp-sem`         the output slot ends up holding ⟨⌜p⌝ , ⟦p⟧ d⟩, and the
--                      two scratch slots are nil again (R-WHILE's
--                      `all_cleared` store invariant survives);
--   * `pp-cost`        the run costs  cost(p) + 8  — a CONSTANT more than p,
--                      independent of the input;
--   * `pp-cost-exact`  and that is the only cost it can have (determinism).
--
-- MODELLING NOTE (the honest gap).  The OCaml emit is two commands, a `CAss`
-- and a pattern replacement `CRep (OUT-PP, cons P-SELF Y)`; the timed core has
-- no `<=`, only the flat XOR assignment `^=`.  The same effect is obtained
-- here with four assignments — set P-SELF, build the pair into OUT-PP, clear
-- P-SELF (XOR with the same constant), clear Y (XOR with `tl OUT-PP`).  Both
-- versions leave the store clean and both add a CONSTANT; only the value of
-- the constant differs (8 here, 4 in the `-steps` meter of the OCaml, which
-- charges 1 per CSeq/CAss/CRep).  What the theorems below establish is the
-- constancy, which is what the criterion needs — not the particular 8.
--
-- The two fresh slot indices are the counterparts of `P-SELF` / `OUT-PP`.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileProgPres where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import RWhileTime
open import RWhileSIWf using (get-set-≡; get-set-≢)
open import RWhileTimeDet using (⇒-det)

------------------------------------------------------------------------
-- The construction is parameterised by the three slot indices it touches:
--   y     the source program's output variable
--   self  the fresh slot holding ⌜p⌝            (OCaml `P-SELF`)
--   out   the fresh output slot of p⁺            (OCaml `OUT-PP`)
-- and by the encoded program `pd = ⌜p⌝` itself (a constant of the program
-- text, exactly as in `Simp.program_preserving`, which calls
-- `Program2DataRwhile.program2data` at construction time).

module PP (y self out : ℕ) (pd : V)
          (self≢y   : ¬ (self ≡ y))
          (self≢out : ¬ (self ≡ out))
          (out≢y    : ¬ (out ≡ y))
          where

  y≢self : ¬ (y ≡ self)
  y≢self e = self≢y (sym e)

  out≢self : ¬ (out ≡ self)
  out≢self e = self≢out (sym e)

  y≢out : ¬ (y ≡ out)
  y≢out e = out≢y (sym e)

  con : V → Exp
  con v = opd (cst v)

  ----------------------------------------------------------------------
  -- The emit suffix, and p⁺ itself.

  emit : Cmd
  emit = (self ^= con pd)                  -- P-SELF := ⌜p⌝
       ⨾ (out  ^= cns (var self) (var y))  -- OUT-PP := (⌜p⌝ . answer)
       ⨾ (self ^= con pd)                  -- clear P-SELF (XOR with ⌜p⌝)
       ⨾ (y    ^= tlE (var out))           -- clear Y      (XOR with tl OUT-PP)

  ppBody : Cmd → Cmd
  ppBody body = body ⨾ emit

  ----------------------------------------------------------------------
  -- The four intermediate stores.

  s1 : Store → Store
  s1 τ = set τ self pd

  s2 : Store → V → Store
  s2 τ v = set (s1 τ) out (pd ∙ v)

  s3 : Store → V → Store
  s3 τ v = set (s2 τ v) self nil

  final : Store → V → Store
  final τ v = set (s3 τ v) y nil

  ----------------------------------------------------------------------
  -- The four steps.  Each is one `e-ass`, i.e. cost 1.

  step1 : ∀ τ → get τ self ≡ nil → (self ^= con pd) ⊢ τ ⇒ s1 τ ∣ 1
  step1 τ hs = e-ass refl r
    where
      r : rupd (get τ self) pd ≡ just pd
      r = subst (λ w → rupd w pd ≡ just pd) (sym hs) refl

  step2 : ∀ τ v → get τ out ≡ nil → get τ y ≡ v
        → (out ^= cns (var self) (var y)) ⊢ s1 τ ⇒ s2 τ v ∣ 1
  step2 τ v ho hy = e-ass ev r
    where
      gself : get (s1 τ) self ≡ pd
      gself = get-set-≡ τ self pd
      gy : get (s1 τ) y ≡ v
      gy = trans (get-set-≢ τ self y pd self≢y) hy
      gout : get (s1 τ) out ≡ nil
      gout = trans (get-set-≢ τ self out pd self≢out) ho
      ev : evalE (s1 τ) (cns (var self) (var y)) ≡ just (pd ∙ v)
      ev = cong just (cong₂ _∙_ gself gy)
      r : rupd (get (s1 τ) out) (pd ∙ v) ≡ just (pd ∙ v)
      r = subst (λ w → rupd w (pd ∙ v) ≡ just (pd ∙ v)) (sym gout) refl

  step3 : ∀ τ v → (self ^= con pd) ⊢ s2 τ v ⇒ s3 τ v ∣ 1
  step3 τ v = e-ass refl r
    where
      g : get (s2 τ v) self ≡ pd
      g = trans (get-set-≢ (s1 τ) out self (pd ∙ v) out≢self)
                (get-set-≡ τ self pd)
      r : rupd (get (s2 τ v) self) pd ≡ just nil
      r = subst (λ w → rupd w pd ≡ just nil) (sym g) (rupd-self pd)

  step4 : ∀ τ v → get τ y ≡ v
        → (y ^= tlE (var out)) ⊢ s3 τ v ⇒ final τ v ∣ 1
  step4 τ v hy = e-ass ev r
    where
      gout : get (s3 τ v) out ≡ pd ∙ v
      gout = trans (get-set-≢ (s2 τ v) self out nil self≢out)
                   (get-set-≡ (s1 τ) out (pd ∙ v))
      gy : get (s3 τ v) y ≡ v
      gy = trans (get-set-≢ (s2 τ v) self y nil self≢y)
           (trans (get-set-≢ (s1 τ) out y (pd ∙ v) out≢y)
           (trans (get-set-≢ τ self y pd self≢y) hy))
      ev : evalE (s3 τ v) (tlE (var out)) ≡ just v
      ev = subst (λ w → tlM w ≡ just v) (sym gout) refl
      r : rupd (get (s3 τ v) y) v ≡ just nil
      r = subst (λ w → rupd w v ≡ just nil) (sym gy) (rupd-self v)

  ----------------------------------------------------------------------
  -- The emit suffix runs in exactly 7 steps (4 assignments + 3 `⨾` nodes).

  emit-run : ∀ τ v → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
           → emit ⊢ τ ⇒ final τ v ∣ 7
  emit-run τ v hs ho hy =
    e-seq (step1 τ hs)
          (e-seq (step2 τ v ho hy)
                 (e-seq (step3 τ v) (step4 τ v hy)))

  ----------------------------------------------------------------------
  -- What the final store looks like.

  final-out : ∀ τ v → get (final τ v) out ≡ pd ∙ v
  final-out τ v =
    trans (get-set-≢ (s3 τ v) y out nil y≢out)
    (trans (get-set-≢ (s2 τ v) self out nil self≢out)
           (get-set-≡ (s1 τ) out (pd ∙ v)))

  final-self : ∀ τ v → get (final τ v) self ≡ nil
  final-self τ v =
    trans (get-set-≢ (s3 τ v) y self nil y≢self) (get-set-≡ (s2 τ v) self nil)

  final-y : ∀ τ v → get (final τ v) y ≡ nil
  final-y τ v = get-set-≡ (s3 τ v) y nil

  -- every OTHER slot is untouched by the emit: p⁺ adds no garbage.
  final-frame : ∀ τ v z → ¬ (y ≡ z) → ¬ (self ≡ z) → ¬ (out ≡ z)
              → get (final τ v) z ≡ get τ z
  final-frame τ v z zy zs zo =
    trans (get-set-≢ (s3 τ v) y z nil zy)
    (trans (get-set-≢ (s2 τ v) self z nil zs)
    (trans (get-set-≢ (s1 τ) out z (pd ∙ v) zo)
           (get-set-≢ τ self z pd zs)))

  ----------------------------------------------------------------------
  -- MAIN THEOREM (semantics + cost).
  --
  -- If p's body takes σ to τ in k steps, leaving its answer in `y` and the
  -- two fresh slots nil, then p⁺'s body takes σ to a store in which
  --     out  = ⟨ ⌜p⌝ , the answer ⟩ ,   self = nil ,   y = nil
  -- in exactly k + 8 steps.

  pp-run : ∀ {body σ τ k} v → body ⊢ σ ⇒ τ ∣ k
         → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
         → ppBody body ⊢ σ ⇒ final τ v ∣ suc (k + 7)
  pp-run {τ = τ} v d hs ho hy = e-seq d (emit-run τ v hs ho hy)

  pp-cost : ∀ {body σ τ k} v → body ⊢ σ ⇒ τ ∣ k
          → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
          → ppBody body ⊢ σ ⇒ final τ v ∣ (k + 8)
  pp-cost {body} {σ} {τ} {k} v d hs ho hy =
    subst (λ n → ppBody body ⊢ σ ⇒ final τ v ∣ n)
          (sym (+-suc k 7)) (pp-run v d hs ho hy)

  -- the packaged form: ⟦p⁺⟧ d = ⟨ ⌜p⌝ , ⟦p⟧ d ⟩, at constant extra cost,
  -- with the store left clean.
  pp-sem : ∀ {body σ τ k} → body ⊢ σ ⇒ τ ∣ k
         → get τ self ≡ nil → get τ out ≡ nil
         → Σ[ ρ ∈ Store ] (ppBody body ⊢ σ ⇒ ρ ∣ (k + 8))
                        × (get ρ out ≡ pd ∙ get τ y)
                        × (get ρ self ≡ nil)
                        × (get ρ y ≡ nil)
  pp-sem {τ = τ} d hs ho =
      final τ (get τ y)
    , pp-cost (get τ y) d hs ho refl
    , final-out τ (get τ y)
    , final-self τ (get τ y)
    , final-y τ (get τ y)

  ----------------------------------------------------------------------
  -- The overhead is not just AN answer but THE answer: by determinism no
  -- other run of p⁺ exists, so the constant 8 is exact, not an upper bound.

  pp-cost-exact : ∀ {body σ τ ρ k m} v → body ⊢ σ ⇒ τ ∣ k
                → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
                → ppBody body ⊢ σ ⇒ ρ ∣ m
                → m ≡ k + 8
  pp-cost-exact v d hs ho hy dpp =
    sym (proj₂ (⇒-det (pp-cost v d hs ho hy) dpp))

  pp-store-exact : ∀ {body σ τ ρ k m} v → body ⊢ σ ⇒ τ ∣ k
                 → get τ self ≡ nil → get τ out ≡ nil → get τ y ≡ v
                 → ppBody body ⊢ σ ⇒ ρ ∣ m
                 → ρ ≡ final τ v
  pp-store-exact v d hs ho hy dpp =
    sym (proj₁ (⇒-det (pp-cost v d hs ho hy) dpp))

------------------------------------------------------------------------
-- Worked example: the construction RUN inside the type checker.
--
-- p  =  read V0;  V0 ^= 'seven;  write V0                  (1 command node)
-- p⁺ =  read V0;  V0 ^= 'seven;  emit;      write V2       (9 command nodes)
--
-- with V1 = P-SELF, V2 = OUT-PP and ⌜p⌝ modelled by the atom 42.  `run-pp`
-- is the fuel-indexed evaluator agreeing with the k + 8 theorem, checked by
-- `refl`; documentation + regression.

module Examples where

  open PP 0 1 2 (atm 42) (λ ()) (λ ()) (λ ())

  σ₀ : Store                                  -- three empty slots
  σ₀ = nil ∷ nil ∷ nil ∷ []

  bodyEx : Cmd
  bodyEx = 0 ^= con (atm 7)

  τ₀ : Store                                  -- p's answer sits in V0
  τ₀ = atm 7 ∷ nil ∷ nil ∷ []

  -- p costs 1 ...
  run-p : bodyEx ⊢ σ₀ ⇒ τ₀ ∣ 1
  run-p = exec-sound 1 bodyEx σ₀ τ₀ 1 refl

  -- ... and p⁺ costs 9 = 1 + 8, as `pp-cost` says.
  run-pp : ppBody bodyEx ⊢ σ₀ ⇒ final τ₀ (atm 7) ∣ (1 + 8)
  run-pp = pp-cost (atm 7) run-p refl refl refl

  -- the evaluator computes the very same store and cost.
  run-pp-exec : exec 12 (ppBody bodyEx) σ₀ ≡ just (final τ₀ (atm 7) , 9)
  run-pp-exec = refl

  -- the output slot holds ⟨⌜p⌝ , answer⟩ ...
  out-value : get (final τ₀ (atm 7)) 2 ≡ atm 42 ∙ atm 7
  out-value = refl

  -- ... and both scratch slots are nil again (`all_cleared`).
  clean : (get (final τ₀ (atm 7)) 1 ≡ nil) × (get (final τ₀ (atm 7)) 0 ≡ nil)
  clean = refl , refl
