{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- fp3 for the REAL spec_av CONTRACT, from that contract ALONE.
--
-- RWhileFutamura2 proves the hierarchy from two hypotheses: H1 (the
-- specialiser is correct) and H2 (a program specP IMPLEMENTS it).  This
-- module is the artifact-faithful sharpening used by the IEICE paper's
-- fp2/fp3 tests (rproj-IEICE2026 src/TestSuite.ml `second-projection` /
-- `reversible-spec`):
--
--   * the specialiser is not an abstract function with a separate
--     implementation — `spec p s` is DEFINED as running the program
--     specP (= spec_av.rwhile as data), so H2 is definitional and
--     disappears as a hypothesis;
--   * the pairing carries the binding-time tag: spec_av's input is
--     (Prog . ('S . Src)), while a residual's input is plain (Src . d).
--     With RWhileFutamura2's single untagged ⟨_,_⟩ the real comp2/comp3
--     equations ([comp2](('S.op)), [comp3](('S.ri_min))) cannot even be
--     stated; here `tagS` makes them verbatim.
--
-- The ONE hypothesis is spec_av's contract (FINDINGS §1, basic equation)
--
--   contract : run (run specP ⟨ p , tagS s ⟩) d ≡ run p ⟨ s , d ⟩
--     -- i.e.  [[spec_av]((p.('S.s)))](d) = [p]((s.d))
--
-- and from it alone we derive, for comp2 = [specP]((specP.('S.int)))
-- and comp3 = [specP]((specP.('S.specP))):
--
--   fp2       [comp2](('S.src))            = [specP]((int.('S.src)))
--   fp3       [comp3](('S.p))              = [specP]((specP.('S.p)))
--   fp3-cogen [comp3](('S.int))            = comp2
--   fp3-run   [[[comp3]('S.int)]('S.src)](d) = [int]((src.d))
--
-- fp3-run is "fp3 is always correct": for EVERY interpreter int, source
-- src and dynamic input d — the ∀-closure of the point checks
-- test_fp3_cogen / test_fp3_rev_cogen.  Everything is parametric in
-- specP, so one instantiation covers spec_av and another spec_av_rev.
--
-- Honest scope: the contract itself — that the 42KB spec_av.rwhile
-- satisfies its basic equation on ALL inputs — is exactly what remains
-- unproved for the artifact (its AV core is verified in RWhileAVSpec /
-- RWhileH2WorklistAV / RWhileSpecAVWire*, and the OCaml tests check it
-- pointwise); this module shows the fp2/fp3 hierarchy adds NO further
-- proof obligation beyond that contract.  The Closure witness below
-- discharges the contract by refl, so the theory is non-vacuous.
------------------------------------------------------------------------

module RWhileFutamura3 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

module Contract
  (U      : Set)                    -- programs = data = residuals
  (⟨_,_⟩  : U → U → U)              -- cons pairing  (a . b)
  (tagS   : U → U)                  -- binding-time tag  ('S . s)
  (run    : U → U → U)              -- [p](d)
  (specP  : U)                      -- spec_av (or spec_av_rev) as a program
  -- H1, the basic equation of spec_av: [[specP]((p.('S.s)))](d) = [p]((s.d))
  (contract : ∀ p s d → run (run specP ⟨ p , tagS s ⟩) d ≡ run p ⟨ s , d ⟩)
  where

  -- specialisation IS running the specialiser program (H2 by definition)
  spec : U → U → U
  spec p s = run specP ⟨ p , tagS s ⟩

  module _ (int : U) where          -- any interpreter (ri_min, ri_seq, ri_ip, …)

    -- the three artefacts, exactly as computed by the OCaml tests
    target : U → U
    target src = spec int src                    -- fp1 residual B

    comp2 : U
    comp2 = spec specP int                       -- [spec_av]((spec_av.('S.int)))

    comp3 : U
    comp3 = spec specP specP                     -- [spec_av]((spec_av.('S.spec_av)))

    --------------------------------------------------------------------
    -- fp1: the residual computes the interpreter.
    fp1 : ∀ src d → run (target src) d ≡ run int ⟨ src , d ⟩
    fp1 src d = contract int src d

    --------------------------------------------------------------------
    -- fp2: the compiler maps each ('S.src) to the fp1 residual.
    --   OCaml check: [comp2](('S.op)) == B
    fp2 : ∀ src → run comp2 (tagS src) ≡ target src
    fp2 src = contract specP int (tagS src)

    --------------------------------------------------------------------
    -- fp3: the cogen maps each ('S.p) to the compiler for p.
    fp3 : ∀ p → run comp3 (tagS p) ≡ spec specP p
    fp3 p = contract specP specP (tagS p)

    -- OCaml check: [comp3](('S.ri_min)) == comp2
    fp3-cogen : run comp3 (tagS int) ≡ comp2
    fp3-cogen = fp3 int

    --------------------------------------------------------------------
    -- fp3 is ALWAYS correct, end to end: the program produced by the
    -- cogen's compiler computes the interpreter, for every int, src, d.
    --   OCaml check (pointwise): [[comp3]('S.ri_min)]('S.'swap) == B
    fp3-run : ∀ src d →
      run (run (run comp3 (tagS int)) (tagS src)) d ≡ run int ⟨ src , d ⟩
    fp3-run src d =
      trans (cong (λ c → run (run c (tagS src)) d) fp3-cogen)
      (trans (cong (λ c → run c d) (fp2 src))
             (fp1 src d))

------------------------------------------------------------------------
-- Non-vacuity witness: a universal type with a TAGGED self-applicable
-- specialiser discharging the contract by refl (the closure realisation
-- of RWhileFutamura2Inst, extended with the binding-time tag).
------------------------------------------------------------------------

module Closure where

  data U : Set where
    pair : U → U → U      -- ⟨ a , b ⟩
    tagS : U → U          -- ('S . s)
    papp : U → U → U      -- residual of specialising p to s
    mkspec : U            -- the specialiser as a program
    idP : U               -- a placeholder interpreter

  -- Only the papp case recurses (on a smaller first argument): run is total.
  run : U → U → U
  run (papp p s) d                 = run p ⟨ s , d ⟩ where ⟨_,_⟩ = pair
  run mkspec (pair p (tagS s))     = papp p s
  run mkspec (pair p (pair a b))   = mkspec
  run mkspec (pair p (papp a b))   = mkspec
  run mkspec (pair p mkspec)       = mkspec
  run mkspec (pair p idP)          = mkspec
  run mkspec (tagS a)              = mkspec
  run mkspec (papp a b)            = mkspec
  run mkspec mkspec                = mkspec
  run mkspec idP                   = mkspec
  run (tagS a) d                   = d
  run (pair a b) d                 = d
  run idP d                        = d

  open Contract U pair tagS run mkspec (λ p s d → refl) public

  -- concrete computations witnessing the theorems (test-first checks):
  _ : comp3 idP ≡ papp mkspec mkspec
  _ = refl

  _ : run (comp3 idP) (tagS idP) ≡ comp2 idP
  _ = refl

  _ : ∀ d → run (run (run (comp3 idP) (tagS idP)) (tagS mkspec)) d
            ≡ run idP (pair mkspec d)
  _ = λ d → refl
