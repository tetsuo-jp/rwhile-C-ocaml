# R-WHILE reversibility — machine-checked proofs (Agda)

A first formalisation of R-WHILE's central correctness property: for a
*reversible* language, "correct" means the syntactic program inversion
`inv` (`src/InvRwhile.ml`) really is the inverse of execution
(`src/EvalRwhile.ml`).

## What is proved

For the core reversible control constructs, modelled exactly as in the
interpreter, with an **abstract** store `S` and abstract tests `S → Bool`
and atomic reversible operations (so the results hold for *any* concrete
store / atoms — in particular R-WHILE's binary-tree value store and the
reversible XOR-update `rupdate`):

| construct        | model                              | inversion (matches `InvRwhile.ml`)        |
|------------------|------------------------------------|-------------------------------------------|
| `CRep` / `CAss`  | atomic relation `A : S → S → Set`  | converse relation `conv A`                |
| `CSeq c d`       | `c ⨾ d`                            | `inv d ⨾ inv c`                           |
| `CCond e c d f`  | `cond e c d f`                     | `cond f (inv c) (inv d) e`                |
| `CLoop e D L f`  | `loop e D L f`                     | `loop f (inv D) (inv L) e`                |

Big-step semantics `_⊢_⇒_` mirrors `EvalRwhile.ml`, including the exit
assertion of the conditional (`f` true after `then`, false after `else`)
and the loop's reversibility assertions (`e` true on entry, `e` false
after each loop body, `f` the exit test).

Theorems (all `--safe`, no postulates / holes / termination pragmas):

- **`inv-sound`**  `c ⊢ s ⇒ t → inv c ⊢ t ⇒ s` — running the inverted
  program backwards undoes the original.
- **`inv-inv`**  `inv (inv c) ≡ c` — inversion is a syntactic involution.
- **`inv-complete`**  `inv c ⊢ t ⇒ s → c ⊢ s ⇒ t` — the converse direction
  (corollary of the two above).

The loop case is the crux: inverting it reverses the whole iteration chain,
done by the accumulator induction `rev-rest`.

## Files (in dependency order)

- `RWhileRev.agda` — core reversibility: atom / seq / cond.
- `RWhileRevFull.agda` — adds the reversible loop `CLoop` (the crux).
- `RWhileValStore.agda` — **step (1)**: instantiate the abstract atom with
  R-WHILE's concrete value trees + the reversible XOR-update `rupdate`;
  prove `rupdate` is a partial involution (`RAss-sym`), hence the concrete
  assignment is reversible.
- `RWhileDet.agda` — **step (2)**: determinism of `_⊢_⇒_` (given
  deterministic atoms, collected by `Det⟨ c ⟩`) and the function-level
  inverse law `inv-cancels` (running `inv c` on c's output returns to start).
- `RWhileDetConcrete.agda` — **step (2), concrete**: `rupdate` is
  deterministic (`RAss-det`, under a `funext` hypothesis), so the concrete
  assignment's inverse cancels (`assign-inv-cancels`).
- `RWhileCRep.agda` — **pattern replacement** `CRep`: models pattern READ
  (`evalPat`) and WRITE (`inv_evalPat`) as independent relations, proves they
  are mutual converses (`read-write`/`write-read`), and concludes
  `inv (CRep q r) = CRep r q` is semantically the inverse (`crep-reversible`).
  Broadens the concrete model from `rupdate` alone to R-WHILE's other atomic
  reversible operation.
- `RWhileCRepDet.agda` — `CRep` in the determinism layer: pattern read/write
  are deterministic (`Read-det`/`Write-det`, under `funext`), hence `CRep` and
  its inverse are deterministic and the function-level inverse law holds for
  pattern replacement (`crep-inv-cancels`).
- `RWhileExec.agda` — **bridge to the implementation**: an EXECUTABLE
  functional interpreter `frun` (the form `evalCom` takes — atoms are partial
  functions, sequencing is Maybe-bind, the conditional checks its exit
  assertion), proved EQUIVALENT to the relational semantics
  (`frun-sound`/`frun-complete`: `frun p s ≡ just t ↔ compile p ⊢ s ⇒ t`).
  Corollary `frun-reversible`: the executable interpreter inherits
  reversibility. This certifies the interpreter *algorithm*, not just an
  abstract relation.
- `RWhileExecConcrete.agda` — removes the last abstraction: `rupdF`, the
  reversible XOR-update as ordinary executable code (`Store → Maybe Store`,
  mirroring `rupdate`), proved equivalent to the relational `RAss`
  (`rupdF-sound` without funext; `rupdF-complete` with funext). So the
  executable assignment `frun (fatom (rupdF x v))` computes exactly the
  reversible, deterministic semantics — no abstract atom left.
- `RWhileIL.agda` — **step (3)**: a reversible Intermediate Language with
  flat (list) sequencing, its own big-step semantics, a translation `trS`
  to R-WHILE proved **semantics-preserving** (`tr-soundS`/`tr-completeS`),
  and **IL reversibility** (`il-revS`). Demonstrates the layered-correctness
  architecture (prove in an efficient IL, transport via a verified
  translation).
- `RWhileCoreExp.agda` — reflects the implementation's Core IR
  expression/pattern NORMALIZATION (`src/Core.ml`: `norm_exp`/`norm_pat`/
  `eval_cexp`) and proves it semantics-preserving: `norm-correct`
  (`evalC σ (norm e) ≡ evalS σ e`) for expressions and `read-norm-correct`
  (`readC σ (normP p) ≡ readS σ p`) for patterns — desugaring list sugar to
  cons-chains keeps meaning. Certifies what the `core-ir` differential tests
  check empirically.
- `RWhileElabCom.agda` — command-level translation correctness (the CONTROL
  layer of R-WHILE → R-CORE): models source commands with OPTIONAL branches
  (omitted branch = skip), elaborates them to the core (empty branch → `atom
  Id`), and proves the elaboration preserves the big-step semantics both ways
  (`elab-sound`/`elab-complete`) for atom / seq / cond / loop. Together with
  `RWhileCoreExp` (exp/pat), the whole surface→core translation is now proved
  semantics-preserving — completing the "small verified core + meaning-
  preserving translation" methodology.
- `RWhileMacroSubst.agda` — towards `expMacProgram` correctness (R-WHILE-M →
  R-WHILE). Macros expand by INLINING: a call is replaced by the body with the
  formal parameters RENAMED to the actual variables. Proves the SUBSTITUTION
  LEMMA for expressions, `subst-exp : evalC σ (ren ρ e) ≡ evalC (σ ∘ ρ) e` —
  renaming a term equals renaming the store — for ANY `ρ` (expressions only
  READ, so inlining their expressions is unconditionally sound). For the WRITE
  side (`subst-upd`) it proves a store write commutes with renaming EXACTLY when
  `ρ` is injective on the live variables — precisely R-WHILE's hygiene condition
  (`-hygienic-macros`) — and `capture` exhibits the converse: a collapsing
  rename (merging two variables) breaks the commutation, i.e. variable capture
  really does change meaning. So expMacProgram is sound iff expansion is
  hygienic, now a theorem rather than a caveat.
- `RWhileRevProj2Lift.agda` — C-layer hint for the B-layer 2nd reversible
  projection (compiler generation by self-application). Models the reversible
  XOR-assign of the real specialiser (spec_av's `'10` check: set / clear /
  rupdate-different) and the `lift`-then-clear idiom that closes the residual
  (`ASSEMBLE-FP1`). Proves the idiom round-trips IFF `lift` preserves its
  operand (`idiom-ok` / `idiom-drift`), reproduces the actual fp2 `'10` with the
  observed drift (`bug-reproduces-'10` — scratch left as the lift machinery's
  own `(LfTag.LfPay)`), and states the repair as a theorem (`fix-roundtrips`).
  So: making AV-LIFT preserve its operand's abstract slot is necessary AND
  sufficient — the precise fix the production specialiser needs (see
  `../../plan_fp1_stage_c.md` 6.3.2). Also refutes a tempting FALSE fix
  (`selfClear-masks`): clearing the scratch with its own value (`AsAV ^= AsAV`)
  succeeds for ANY drift, so it only silences the `'10` while leaving the
  corrupted residual — confirmed on the real spec_av (fp2 then emits a broken
  compiler), so the only correct repair is restoring lift-preservation.
- `RWhileRevProj2BT.agda` — the design spec for the fp2 fix: BINDING-TIME
  correctness. After ruling out every clear-side fix, the true root cause was
  localised to the specialiser tagging its own static input `'S`
  UNCONDITIONALLY (spec_av.rwhile:1051 `cons 'S Src`). Models a minimal
  specialisation step over annotated values and proves: `fp1-ok` (static input —
  the unconditional tag agrees with a binding-time-aware one), `fp2-buggy-mistags`
  (under self-application the input is dynamic, so the unconditional `'S`
  mis-tags), and the consequence `buggy-ignores-input` / `correct-uses-input` /
  `overstatic-wrong` (a statically-committed residual bakes a constant and
  ignores its runtime input — the observed over-static degeneration — whereas a
  binding-time-aware residual uses it). So the precise repair is a binding-time-
  aware (BTA / two-level) partial input, the self-applicability requirement.
- `RWhileRevProj2Self.agda` — the CONSTRUCTIVE counterpart: a small self-
  applicable specialiser for the op-list language where the 2nd projection
  actually goes through, with REAL residualisation. The residual `uComp ops` is
  a genuine compiled program (it carries the source ops and runs them on the
  RUNTIME data — the interpreter is ELIMINATED, not re-run via a closure as in
  `RWhileFutamura2Inst`). Binding-time discipline is built in (source static,
  data dynamic). `fp1`/`fp2`/`fp3` all hold by `refl`, and
  `compiler-residual-uses-input` / `fp2-correct` witness that the generated
  compiler's residual USES its runtime input (no over-static degeneration) —
  the small-core realisation of the fix `RWhileRevProj2BT` specifies.
- `RWhileAVSound.agda` — **soundness of spec_av's annotated-value (AV) algebra**
  (the executable specialiser's actual mechanism, not a closure/op-list stand-in).
  Models AV (`S` static / `D` dynamic-code / `C` partial-static cons), a residual-
  code language with semantics `⟦_⟧c`, and concretisation `γ : AV → Val → Val`
  (fill dynamic holes with the runtime input).  Proves every AV operation
  (mirroring the macros `AV-HD`/`AV-TL`/`AV-CONS`/`AV-EQ`/`AV-PAIRP`/`AV-LIFT`)
  commutes with concretisation: e.g. `avHd-sound : γ (avHd a) ρ ≡ hd (γ a ρ)`,
  and `lift-sound : ⟦ lift a ⟧c ρ ≡ γ a ρ`.  These congruences are the machine-
  checked core of "spec_av specialises correctly" — the H1 (`spec-correct`)
  obligation of the modular hierarchy `RWhileFutamura2`, for the REAL AV
  machinery.  Remaining for full G1 (see `../../AGDA_CORRESPONDENCE.md`): assemble
  an AV specialisation STEP from these sound ops and discharge H1/H2 end-to-end so
  the executable spec_av becomes an instance of the proved fp2/fp3.
- `RWhileAVSpec.agda` — **spec-correct (H1) for the real AV mechanism** (N2 step 2).
  Assembles RWhileAVSound's ops into the symbolic evaluator `aeval` and proves it
  sound (`aeval-sound : γ (aeval c a) ρ ≡ ⟦ c ⟧c (γ a ρ)`).  Defines the AV
  residualiser with the BINDING-TIME SPLIT (head static, tail dynamic:
  `C (S s) (D cVar)`, spec_av's MKAV discipline) and proves
  `spec-correct : ⟦ spec p s ⟧c d ≡ ⟦ p ⟧c (s · d)` — the H1 hypothesis of
  `RWhileFutamura2`, now discharged for the ACTUAL AV algebra (not the closure of
  RWhileFutamura2Inst nor the op-list table of RWhileRevProj2Self), with the
  dynamic tail genuinely used (`residual-uses-input`, no over-static degeneration).
  Remaining for a full fp2/fp3 instance: H2 (spec-impl) — representing this
  specialiser in its own object language (self-application), the engineering the
  IEICE draft also leaves open.  H1, the correctness core, is now machine-checked.
- `RWhileCaseInv.agda` — **soundness of the symmetric `case` sugar** (Rwhile.cf
  CCase / src/Desugar.ml).  Models the desugaring to the verified reversible core
  (atom/_⨾_/cond) and proves: `case-reversible` (a desugared case is reversible,
  via `inv-sound`); `inv-commute` (inverting a desugared case = desugaring the
  SWAPPED case — scrutinee↔result, each arm InPat↔OutPat, body inverted —
  SEMANTICALLY, the two differing only by the ; -associativity that inversion
  introduces, discharged by `seq-assoc` + `cond-cong`); `case-inv-undoes`
  (running the swapped case backwards undoes the original); and `invArm-inv` (the
  per-arm swap is an involution).  So the inverse of a `case` is again a `case`.
- `RWhileGarbageBound.agda` — a **quantitative lower bound on garbage** (sharpens
  the qualitative `RWhileRevProjGen.garbage-necessary`).  A reversible residual
  keeps `(result , garbage) = (S x , g x)`; reversibility = that pair map is
  injective.  Proves `garbage-distinguishes-fiber` / `garbage-injective-on-fiber`:
  on a FIBER of `S` (inputs sharing a result) the garbage alone must distinguish
  them, so the garbage is injective per fiber, i.e. `|fiber| ≤ |Gar|` (≥ log|fiber|
  bits) — the minimal information any reversible simulation must retain
  (Landauer/Bennett).  Witness: for the constant (maximally non-injective) source
  the whole input must be kept — the NECESSITY counterpart of
  `input-preserving-inj`'s sufficiency.  UIP-free, so `--safe`.

- `RWhileP2D.agda` — **program⇄data encoding for the residual `Code`** (gap G4,
  the prerequisite of self-application H2).  `program2data : Code → Val` /
  `data2program : Val → Code` with the round-trip `d2p∘p2d : data2program ∘
  program2data ≡ id` and the corollary `p2d-injective` (a program is uniquely
  recoverable from its data form — the injectivity the paper's `rspec` relies on).

- `RWhileP2DProg.agda` — **program⇄data round-trip for the control core** (gap G4,
  extends RWhileP2D from the residual `Code` to whole programs): expressions
  (var/val/cons/hd/tl/eq/pairp), patterns (var/val/cons), commands
  (seq/ass/rep/cond/loop) and the program wrapper, with
  `dProg (transProg p) ≡ p` (and the exp/pat/com lemmas).  Models the clean
  variable-index encoding (`unnat (natV n) ≡ n`); the OCaml `transRIdent` has an
  incidental off-by-one, so its round-trip is identity only up to a consistent
  index relabelling — the clean encoding is the meaningful invariant.

- `RWhileAVSelfApp.agda` — **the hierarchy for the real AV machinery in ONE value
  type** (case 2).  Sets `U = Val` and uses RWhileP2D to make the real residual
  evaluator act on a single type: `runU pv d = ⟦ data2program pv ⟧c d`,
  `specU pv sv = program2data (spec (data2program pv) sv)`.  **Discharges H1 for
  this unified real machinery** (`specU-correct`, from the round-trip +
  `RWhileAVSpec.spec-correct`), so **fp1 holds unconditionally for the real AV
  specialiser in the value type** (`fp1U`).  `WithSelfApp` then instantiates
  RWhileFutamura2's modular fp2/fp3 at the real `runU`/`specU`, taking H2
  (`spec-impl`) as its one hypothesis — now a single concrete equation
  `runU specP (pv·sv) ≡ specU pv sv`.  The header documents why H2 stays open:
  the first-order `Code` cannot express `spec`, and a total `--safe` `runU`
  cannot be a universal interpreter for a Turing-complete object language (the
  closure constructor of `RWhileFutamura2Inst` is exactly the sidestep).

- `RWhileH2.agda` — **H2's recursive core, discharged WITHOUT the closure
  stand-in** (the genuine prize beyond `RWhileFutamura2Inst`).  Defines the AV-
  expression object language `E` (= spec_av's AV macros AV-HD/AV-TL/AV-CONS/
  AV-EQ/AV-PAIRP over the holes {static input, two child results, payload}), a
  *specialiser program* as a finite algebra `Alg` (one `E`-term per Code
  constructor, mirroring spec_av's `SPEC-EXP-AV-STEP`), and a uniform TOTAL
  interpreter `cata` (structural fold on Code — total because the modelled
  `aeval` is structurally terminating, exactly where a Turing-complete `run`
  could not be).  Proves `self-rep : cata specAlg c a ≡ aeval c a` — the real
  symbolic evaluator IS a genuine data program under a generic interpreter (no
  `papp` primitive) — and `specByProg-correct : specByProg ≡ RWhileAVSpec.spec`,
  so the program-driven specialiser inherits H1.  What is left for a full
  hierarchy instance on the actual `spec_av` is only its non-structural part
  (bounded worklist / looping), needing a fuel-indexed model (route A, future).

- `RWhileH2Hier.agda` — **a full, total, NON-closure instance of the Futamura
  hierarchy** (Phase A1): replaces `RWhileFutamura2Inst`'s bespoke `papp`/`mkpapp`
  constructors with REAL program construction.  Defines a small applicative
  language `Tm` (input/quote/pair/car/cdr/application + program-builder ops), a
  GENERIC total interpreter `run`, the trivial specialiser `spec p s =
  apT (quo p) (pr (quo s) inp)` (the paper's rspec: embed p,s and run), and
  `specP` — a genuine `Tm` program that *constructs* those residuals from its
  input.  H1 (`spec-correct`) and H2 (`spec-impl`) both hold by computation
  (`refl`), so `open RWhileFutamura2.Hierarchy` yields fp1/fp2/fp3 as proven
  theorems with real, inspectable residuals (`compiler`/`cogen` are concrete
  programs).  Totality without fuel: application is of literally quoted programs
  (`run (apT (quo p) a) x = run p (run a x)` recurses on subterm `p`), which is
  all the trivial specialiser emits.  General first-class application (a
  non-quoted function) and the looping AV specialiser need fuel — Phase A2.

- `RWhileH2Hier2.agda` — **Phase A2 (step 1): the hierarchy with GENERAL
  first-class application**, via a big-step evaluation RELATION `prog · x ⇓ v`
  on the same language `Tm` (no fuel, no quote restriction).  Its `⇓ap` rule
  evaluates the function position to a program value and applies it — genuine
  general application; a relation is fine in `--safe` (inductive family,
  partiality = "no derivation") and dodges the totality wall.  Proves the
  relation deterministic (`⇓-det`), discharges H1 (both directions) and H2 for
  the trivial specialiser, and derives fp1/fp2/fp3 as relational theorems with
  general application.  Remaining: the LOOPING AV specialiser of spec_av in this
  model (route A, future) — its recursive structure is in RWhileH2.

- `RWhileFutamura3.agda` — **fp3 from the real spec_av CONTRACT alone (H2-free,
  BT-tagged)**.  Artifact-faithful sharpening of `RWhileFutamura2`: `spec p s`
  is DEFINED as `run specP ⟨ p , tagS s ⟩` (running the specialiser program on
  the implementation's actual input shape `(Prog . ('S . Src))`), so H2 is
  definitional and the ONLY hypothesis is spec_av's basic equation
  `[[specP]((p.('S.s)))](d) ≡ [p]((s.d))` (FINDINGS §1).  From it alone:
  `fp2` (`[comp2](('S.src))` = fp1 residual), `fp3-cogen`
  (`[comp3](('S.int))` = comp2, the OCaml `test_fp3_cogen` equation ∀-closed)
  and the headline `fp3-run` — `[[[comp3]('S.int)]('S.src)](d) ≡ [int]((src.d))`
  for EVERY interpreter, source and input.  Parametric in `specP`, so one
  statement covers spec_av and spec_av_rev.  `Closure` discharges the contract
  by `refl` (tagged papp/mkspec universe) — non-vacuous.  What remains for the
  artifact is exactly the contract itself (pointwise: the OCaml
  `second-projection`/`reversible-spec` tests; its AV core: `RWhileAVSpec`,
  `RWhileH2WorklistAV`, `RWhileSpecAVWire*`) — the hierarchy adds NO further
  proof obligation beyond it.

- `RWhileWireSem.agda` — **C1: big-step semantics for the wire AST** (Pat/Com/
  Prog of RWhileSpecAVWireCom), mirroring `src/EvalRwhile.ml` clause by clause:
  reversible-XOR assignment (rupdate), CRep = clearing read + nil-checked
  write, the conditional's exit ASSERTION (true after then / false after
  else), the loop's entry/re-entry assertions, and the whole-program
  store-cleared check.  Fuel-indexed (`--safe`), fuel-monotone
  (`evalC-mono`/`evalL-mono`/`evalProg-mono`).  Cross-tested against the
  production interpreter by the OCaml `wire-sem` differential group
  (src/TestSuite.ml): the same p2d wire tree run by both must agree whenever
  the interpreter succeeds, and the failure modes coincide.

- `RWhileSpecCom.agda` — **C2: the command-level AV specialiser, γ-sound**
  (the semantic half of the spec_av bridge, static-control fragment = the
  fp1 regime).  A partial-static MULTI-SLOT store (List AV) drives specEx
  (multi-slot SPEC-EXP-AV, `specEx-sound`), pattern read/write on AVs
  (dynamic values split by avHd/avTl), reversible-XOR updates decided
  statically, static conditionals resolved (dead branch dropped), loops
  unrolled while the exit test is static (RWhileLoopBTA's rule).  The
  SUCCESS-SIMULATION `specCom-sim` yields the HEADLINE `spec-contract`:
  `specProg n p s ≡ just cr → evalProg m p (s·d) ≡ just w → ⟦cr⟧c d ≡ w` —
  RWhileFutamura3's contract PROVEN on the model, for every p, s, d in the
  fragment.  Witness: swap residualises to `(cons cVar 'vtrue)` by refl.
  Out of fragment (refused, blueprints exist): dynamic tests → residual
  conditionals/loops (OfflineBTA8 / LoopBTA), dynamic update conflicts.

- `RWhileSpecProg.agda` — **C3: the hierarchy over a REALLY-RESIDUALISING
  specialiser** — the partial-run refinement of RWhileFutamura3.Contract
  with H1 discharged: universe U = values / wire programs / residual Code /
  closures / `specP`; running `specP` on `(wp p . ('S . val s))` invokes the
  VERIFIED specProg (real residual, genuine Futamura gain), other shapes
  (self-application) resolve by the closure constructor (Futamura2Inst's
  papp — representing specProg itself as a wire program remains the
  research item, exercised on the real spec_av by the OCaml fp2/fp3 tests).
  `fp3-run`: cogen ⇓ compiler (refl) ⇓ verified residual (fragment commit)
  ⇓ the source's result (spec-contract).  Witness: swap through the whole
  hierarchy by refl.

- `RWhileSpecComDyn.agda` — **C2-dyn: the command-level specialiser with
  DYNAMIC CONDITIONALS** (the first step past the static-control fragment,
  OfflineBTA8's keep-both-branches rule at the wire level).  The residual
  language RC adds `rIf`; a dynamic test specialises BOTH branches and joins
  the AV stores POINTWISE: slot k = `DD (rIf tc (lift σt[k]) (lift σe[k]))`
  (per-slot conditional expressions — spec_av's residual conditional COMMAND
  is the production O3 item).  A partial-static-cons test is statically
  truthy (resolves to then).  `joinσ-γ-t/f` reduce the joined store to the
  branch the runtime took; `spec-contract-dyn` is the same contract shape,
  now over programs whose control depends on the dynamic input.  Witness: a
  dynamic dispatch residualises to a single `rIf` over the input, both
  branch instances checked by refl.  Loops still need a static exit (the
  residual-LOOP emission is production O1, implemented in spec_av_bti).

- `RWhileSimpSound.agda` — **soundness of the residual simplifier `src/Simp.ml`**
  (idea 1, Phase 2a).  Machine-checks the semantic core of its two transforms:
  (1) the constant-folding rewrites on the residual expression language
  (`hd`/`tl`/`pairp` of a cons fold to the subresult — meaning-preserving), and
  (2) dead reversible-branch elimination — models the reversible conditional's
  forward semantics (`condF`, partial via `Maybe`, mirroring EvalRwhile's CCond,
  asserting the exit test) and proves that constant-true entry+exit tests reduce
  it to the THEN branch (`deadbranch-true`) and constant-false to the ELSE branch
  (`deadbranch-false`) — exactly Simp's `if (const) then C else D fi (const) ⇒
  C|D`, with the dropped branch unreachable and assertions trivially held.

- `RWhileH2HierRec.agda` — **Phase B / #5 (step 1): a recursion-capable big-step
  hierarchy**, the enabler for the LOOPING AV specialiser (beyond RWhileH2Hier2's
  embed-and-apply).  Extends `_·_⇓_` with a structural fold `cata z f` recursing
  on the input's cons-structure; proves the relation deterministic (`⇓-det`) and
  gives a worked, machine-checked recursive program (`mirrorP`, a recursive tree
  mirror) with full correctness (`mirror-correct`) and involution.  A recursive
  specialiser is a `cata` folding a program into residual code; its fp1/2/3
  follow by the H1-then-hierarchy route (continuing work of #5).

- `RWhileOfflineBTA.agda` … `RWhileOfflineBTA9.agda` — the **offline binding-time
  blueprint** for the "real fp2" (removing spec_av's over-static bug); see the
  dedicated section below.

- `RWhileMain.agda` — **capstone**: re-exports the headline machine-checked
  results (spec-correct/H1, the p2d round-trips + injectivity, fp1U, self-rep,
  the two Futamura-hierarchy instances `hier-*`/`gen-*`, simplifier soundness,
  and the offline-BTA blueprint stages 1–9),
  so importing one module type-checks all the marquee theorems together.

## Checking

```
cd proofs/agda
for f in RWhile*.agda; do
  agda --safe "$f"
done
# or, equivalently, the bundled runner which reports PASS/FAIL counts:
./check.sh          # currently: PASS=61 FAIL=0
```

`RWhileMain.agda` transitively imports the marquee results (including the
offline-BTA blueprint `RWhileOfflineBTA1`–`9`), so `agda --safe RWhileMain.agda`
type-checks them together.

Requires Agda + agda-stdlib (the `standard-library` library, as used by
`rev-alg-agda`).  All files are `--safe`: no postulates, holes, `TERMINATING`
pragmas, or `trustMe` (the only assumption is `funext`, taken as an explicit
module hypothesis in `RWhileDetConcrete`).

## Status / further work

Done: reversibility of `inv` (atom/seq/cond/loop); concrete `rupdate`
instantiation; determinism + function-level inverse; a verified flat-IL → R-WHILE
translation with IL reversibility.

## First Futamura projection (verified + extracted)

`RWhileFutamura.agda` (`--safe`) realises the **first Futamura projection** for
the small reversible op-language used in R-WHILE's fp1 (the `ri_seq`/swap
language): `mix` specialises the interpreter `int` to a source op-program,
producing a residual in which the interpretive dispatch is gone, and

```
fp1 : ∀ src p → run (mix src) p ≡ int src p
```

is proved.  `mix-length-≤` shows specialisation shrinks code.
`ExtractFutamura.agda` compiles `mix`/`int`/`run` to a native binary:

```
./build-extract.sh ExtractFutamura && ./ExtractFutamura
#  source program     [swap,id,swap,id]  (len 4)
#  compiled residual  [doSwap,doSwap]    (len 2)  -- dispatch & id removed
#  int src dat       = (nil , (nil.nil))
#  runC (mix src) dat = (nil , (nil.nil))         (equal, by the proved fp1)
```

So the interpreter→compiler transformation (fp1) is machine-checked AND runs
as an extracted native program.

## Futamura hierarchy fp2 / fp3 (modular)

`RWhileFutamura2.agda` (`--safe`) proves the **second and third** Futamura
projections modularly. With one universal type `U` and a specialiser
`spec : U → U → U`, the whole hierarchy follows from two facts:

- **H1** `spec-correct : run (spec p s) d ≡ run p ⟨ s , d ⟩` — the specialiser
  is correct (this is fp1 in general form; realised concretely by `mix` in
  `RWhileFutamura`).
- **H2** `spec-impl : run specP ⟨ p , s ⟩ ≡ spec p s` — the specialiser is
  itself a program `specP` (self-application).

Then `fp2 : run compiler src ≡ target src` and
`fp3 : run cogen p ≡ spec specP p` are each two `trans` steps.

`RWhileFutamura2Inst.agda` gives a **concrete, non-vacuous instance**: a
universal type `U` with a closure constructor `papp` (= `spec p s`) and a
program `mkpapp` (= `specP`) that builds it, so **both H1 and H2 hold by
`refl`** and fp1/fp2/fp3 hold for actual distinct programs (witnessed by
`compiler-is`, `fp2-example`, `fp3-example`). This shows a self-applicable
specialiser *exists* (here via a built-in closure constructor); doing it for
R-WHILE without built-in closures — residualising structurally — is the
engineering still open.

## Reversible Futamura projection

`RWhileRevFutamura.agda` (`--safe`) proves that the first Futamura projection
is *reversible*: specialising a reversible interpreter to a source yields a
reversible compiled program, and the projection commutes with inversion
(`invSrc`/`invComp` = reverse the sequence + invert each step):

- `mix-commute`    : `mix (invSrc src) ≡ invComp (mix src)`  — inversion
  commutes with the projection (compile-then-invert = invert-then-compile).
- `run-rev`        : `run (invComp cs) (run cs p) ≡ p`        — every compiled
  program is reversible.
- `int-rev`        : `int (invSrc src) (int src p) ≡ p`       — the interpreter
  is reversible.
- `reversible-fp1` : `run (mix (invSrc src)) (run (mix src) p) ≡ p` — combining
  the above: compiling the inverse source inverts the compiled program.

## Reversible projections of the IEICE 2025 paper (Okubo–Yokoyama)

A faithful Agda rendering of "2025_Reversible_Projection_IEICE_D" — a fourth
independent check beside the paper's Isabelle/HOL, Rocq and Lean developments.

- `RWhileRevProjPaper.agda` — the three reversible projections from the paper's
  assumptions `def-rint` (the reversible interpreter keeps the program in its
  output) and `def-spec` (the mix equation, with `rspec` itself a program):
  `rev-proj1/2/3` give `snd ∘ ⟦·⟧ ≡ ⟦src⟧_S` for `tgt''`, `comp''`, `cogen'`.
- `RWhileRevProjInst.agda` — a concrete, **executable** instance (closure ctor
  `papp`, specialiser-program `mkpapp`, program-preserving `rintP`); both
  hypotheses hold by `refl`. `ExtractRevProj.agda` compiles it to a native
  binary that **computes and runs the second reversible projection**:
  ```
  ./build-extract.sh ExtractRevProj && ./ExtractRevProj
  #  comp'' = run rspec (rspec.rint)  = papp(rspec,rint)
  #  target = comp''(swap)            = papp(rint,swap)
  #  target((*.(*.*)))                = (swap . ((*.*).*))   (program . result)
  #  snd                              = ((*.*).*) = srcSem swap data ✓
  ```
- `RWhileRevProjGen.agda` — the motivation and generalisations:
  - `proj1-needs-trivial` (paper Thm proj1_fail): a reversible interpreter that
    realises the source directly forces the source semantics to be injective
    (trivial) — so non-trivial sources need the reversible *projection* (rint).
  - general `proj` and arbitrary `srcSem` (covers **non-reversible source**):
    `GeneralRevProjection.rev-proj1/2/3` (`snd` is the special case).
  - **garbage dichotomy**: `garbage-necessary` — a reversible residual
    simulating a non-injective source forces `proj` to discard information;
    `input-preserving-inj` — keeping the input as garbage is always injective,
    so a reversible simulation exists for any source (rint⁺).

## Extraction demo (verified code → native binary)

`Extract.agda` imports the verified `rupdF` and compiles, via Agda's GHC
backend, to a native executable — demonstrating the "replace the
implementation by extraction" route: the *same* Agda code that carries the
`--safe` reversibility proofs is ordinary runnable code.

```
./build-extract.sh      # agda --compile (exposes the `text` pkg, finds libffi)
./Extract
#  V0 initially            = nil
#  V0 after  x ^= (nil.nil) = (nil . nil)
#  V0 after  toggling twice = nil      ← reversibility, at runtime
```

`Extract.agda` uses `--guardedness` (for IO) instead of `--safe`, but it only
*imports* and runs the `--safe`-checked `rupdF`; no proof is weakened.

## Honest scope (what is NOT yet proved)

These are results about an Agda **model** of R-WHILE's core, hand-written to
mirror the OCaml. `RWhileExec` closes part of the gap — it certifies the
interpreter *algorithm* (an executable functional interpreter equivalent to
the proven semantics) — but the *literal* OCaml is still not certified: the
Agda `frun` is hand-written to mirror `evalCom` rather than generated from it
(closing that fully needs extraction, or a verified parser + evaluator). Also
out of scope so far: the expression language
(`cons`/`hd`/`tl`/`=?`/`pair?`), macro expansion, parsing, `p2d`, the
`all_cleared` store invariant, and functional correctness / termination
(we prove *reversibility* and *determinism*, the properties that matter for a
reversible language).

Next: extend the IL with loops; instantiate determinism without `funext` via a
first-order store; and connect the model to the OCaml (extraction, or an
equivalence with a formal model of `eval`/`inv`) so the *implementation* — not
only the model — is certified.

## Offline binding-time blueprint (`RWhileOfflineBTA1`–`9`)

`comp2 = [spec_av]((spec_av . ri_min))` is *incorrect* even after the loop-BTA fix:
`[comp2]('S.swap)` keeps ri_min's echo but drops the `if =? Op 'swap` then-branch
(the swap body).  A live trace (`../../TRACE_comp2_root_cause.md`) pins the cause to
spec_av's **online control agenda**: a conditional is handled by pushing the taken
branch onto `Cd` (`Cd <= cons C Cd`), which cannot be residualised once the test is
dynamic under self-application.  These nine `--safe` modules prove the diagnosis and
the fix as a blueprint for the production agenda offline-isation (all re-exported by
`RWhileMain`):

- `RWhileOfflineBTA.agda` — **stage 1**: the over-static bug *is* a binding-time
  congruence violation.  A fully-static AV is ρ-independent (`static-stable`), so no
  static AV can abstract a dynamic slot (`over-commit-unsound`); the BT-driven `mkAV`
  never freezes a dynamic slot (`mkAV-dyn-nonstatic`); the honest offline `spec2` is
  sound (`spec2-sound`) and congruent (`spec2-static`).
- `RWhileOfflineBTA2.agda` — **stage 2**: the self-application step.  `spec2g`
  (source as a possibly-symbolic AV) is sound for any source (`spec2g-sound`); the
  freeze is invisible on static sources (`spec2bug-ok-on-static`) but unsound on
  symbolic ones (`spec2bug-wrong-on-symbolic`).
- `RWhileOfflineBTA3.agda` — **stage 3**: the Futamura gain — a fully-static
  subexpression collapses to one leaf (`gain`); static dispatch resolves
  (`dispatch-resolved`), dynamic parts survive as holes (`dyn-survives`).
- `RWhileOfflineBTA4.agda` — **stage 4**: the two-stage `comp2` with the Futamura
  **fp2 equation** (`fp2-eq`, compile ∘ generate = eval); the correct compiler keeps
  its source symbolic (`spec1-keeps-source-symbolic`), freezing it is unsound
  (`spec1bug-wrong-on-source`).
- `RWhileOfflineBTA5.agda` — **stage 5**: the three-stage cogen with the Futamura
  **fp3 equation** (`fp3-eq`); the correct cogen keeps the interpreter symbolic
  (`gen-keeps-int-symbolic`), freezing it is unsound (`genbug-wrong-on-int`).
- `RWhileOfflineBTA6.agda` — **stage 6**: the production fix locus.  The observed
  `('val.'swap)` embed is `AV-LIFT` of a static leaf (`prodThen-car-const`); the
  BT-driven fix is byte-identical under `'S` (`fix-agrees-on-fp1`, no fp1 regression)
  and residualises under `'D` (`fixThen-car-tracks`).
- `RWhileOfflineBTA7.agda` — **stage 7**: dispatch preservation.  With an opcode
  dispatch, the correct compiler dispatches (`comp-swap` ≠ `comp-id`) while freezing
  the opcode collapses it and is wrong (`compbug-wrong`).
- `RWhileOfflineBTA8.agda` — **stage 8**: the agenda design rule.  Unconditional
  structure may be flattened onto the agenda (`seq-flatten-ok`); a dynamic conditional
  must stay a residual node with **both** branches specialised
  (`specOff-keeps-branches`), never one branch pushed — doing so drops a branch and is
  unsound (`specBug-riM`/`specBug-wrong`, matching comp2's 39-node output).
- `RWhileOfflineBTA9.agda` — **stage 9**: reversibility / no information loss.
  Residuals are reversible (`rexec-exec`, `swapV-invol`); the correct offline
  specialiser is information-preserving hence **injective** (`specOff-injective`),
  while the branch-dropping bug destroys information and is **not** injective
  (`specBug-not-injective`) — so comp2's dropped branch is a *reversibility* violation
  (the reversible-specialiser injectivity requirement), not merely a soundness bug.

Status: the **blueprint** (fix shape, fp1-safety, dispatch preservation, agenda rule,
reversibility=injectivity) is proved; the production agenda offline-isation
(`spec_av_bti.rwhile`'s `SPEC-CMD-AV` 'cond dynamic path, :972-993) is **not yet
implemented**.  See `../../RESEARCH_ROADMAP.md` and the paper's
`mechanization.tex` §`sec:agda-offline`.

------------------------------------------------------------------------

## Linear-time self-interpretation (2026-08-04)

Nineteen modules (~5,200 lines) formalise the headline claim of Glück &
Yokoyama, *A linear-time self-interpreter of a reversible imperative
language*.  The self-interpreter is **not** an abstract machine: it is one
fixed R-WHILE program `SI`, and the theorem bounds its cost in the very step
count `src/EvalRwhile.ml` increments.  Full write-up: `../../LINEAR_TIME_SI.md`.

**The theorem** (`RWhileSISim.si-linear`, no assumptions, `--safe`):

    Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
      ⟹  SI ⊢ ⟨⌜c⌝ :: todo, [] :: done, σ⟩ ⇒ ⟨[], ⌜c⌝ :: done, τ⟩ ∣ j
          with  j ≤ (CC M + 2) · k        and   CC M = 2940·M + 3184

for a FIXED program `SI` and `M = length σ`: linear time, with a constant that
is affine in the store size (the object store's *walk* is the only part that
scans).  The done stack ends holding exactly `⌜c⌝`, so `SI` reassembles its
input — it is a self-*interpreter*, not a consumer.

- `RWhileTime.agda` — a **timed** (cost-annotated) big-step semantics
  `c ⊢ σ ⇒ τ ∣ k`, where `k` counts executed command nodes exactly as
  `EvalRwhile.evalCom`'s `incr eval_steps` (i.e. `./ri -steps`) does,
  so the theorem is about the cost model the implementation measures.
  Ships an executable fuel-indexed evaluator `exec` with `exec-sound`
  (a computed run *is* a derivation), the tool that makes concrete
  straight-line interpreter fragments provable by `refl`.  Expressions are
  flat (operands = variable or constant); the four reversible control
  constructs, the conditional's exit assertion and the loop's entry/iteration
  assertions are modelled exactly as in `EvalRwhile.ml`.
- `RWhileSIEnc.agda` — the program-as-data encoding `⌜_⌝` (the Agda
  counterpart of `src/Program2DataRwhile.ml`), unary numerals, store encoding
  and the shared tag table.
- `RWhileSIWf.agda` — the static side conditions (`Wf`: `X ∉ Vars(E)` at every
  assignment; `InR`: every variable is inside the store), store separation,
  frame lemmas for expression evaluation, and `⇒-length` / `Rest-length`
  (a run never changes the number of store cells — the invariant the walk needs).
- `RWhileSIMach.agda` — the **agenda machine** behind `examples/ri.rwhile`'s
  main loop: a todo stack, a *reassembling* done stack (so the source program
  is restored — `ri` is program-preserving), and the object store.  Theorems:
  `sim` / `machine-linear` — every terminating object run is simulated
  correctly in at most **4 machine steps per object step**, ending with `⌜c⌝`
  on the done stack.  `astep-td`/`astep-dn` give the structural invariants the
  interpreter's loop assertions need.  Includes executable tests.
- `RWhileSIRun.agda` — `Run c s t B`: a derivation together with a cost bound,
  with combinators (`_»_`, `rSeq`, `rThen`, `rElse`, `rWeak`) that make long
  straight-line interpreter code composable without arithmetic noise.
- `RWhileSIMac.agda` — the interpreter's 19-slot register file, `emb`, and
  generic `push`/`pop` (implemented with `^=` only; cost 9 each).
- `RWhileSIWalk.agda` — walking the encoded object store `Vl` down and back
  (28 steps per cell, both directions), the reversible core of variable access.
- `RWhileSILookup.agda` — `LOOKUP` / `UPDATE` for object variables, cost
  exactly `56k + 27` for variable `k`, plus the store split/rebuild lemmas.
- `RWhileSIEval.agda` — operand evaluation `opdC` (`56M + 36`) and expression
  evaluation `evalC` for all five flat forms, bound `evalB M = 224M + 179`.
  These are **partial involutions** (compute–use–uncompute), so re-running the
  same code uncomputes — the Agda counterpart of `ri.rwhile`'s `INV-` macros.
- `RWhileSIStep.agda` — the dispatch body `STEP` as real R-WHILE code (a
  12-level conditional nest) and **17 run theorems**, one per case, each with
  its exact cost bound and its agreement with the machine's `astep`.  The
  tag algebra (each case leaves a unique final tag) is what makes every exit
  assertion in the nest hold — reversibility and the proof are the same fact.
- `RWhileSIArith.agda` — the pure-ℕ bound bookkeeping of the composition
  (one lemma per object case), kept apart so the big machine-state types stay
  out of the arithmetic.
- `RWhileSISim.agda` — the main loop `SI = loop (=? Cd' nil) skip STEP (=? Cd nil)`,
  the composable iteration chains `PChain`/`PC`, their conversion into the
  loop's `Rest` derivation, the uniform per-step constant `CC`, the induction
  `simP`/`simPR` that strings the 17 case theorems along an object derivation,
  and the closed theorem **`si-linear`** above.
- `RWhileTimeInv.agda` — **program inversion for the timed semantics** (the
  Agda counterpart of `src/InvRwhile.ml`) and its soundness, with the cost
  preserved *exactly*:

      Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k  ⟹  inv c ⊢ τ ⇒ σ ∣ k     (the same k)

  Assignments are their own inverse because `rupd` is a partial involution
  (`rupd-invol`); a conditional swaps test and assertion; a loop swaps entry
  test and exit assertion.  The loop case is the interesting one: the backward
  run visits the same stores in reverse, but its iterations are **shifted by
  one** — each backward iteration pairs `inv L` of one forward iteration with
  `inv D` of the *previous* one — so `inv-rest` walks the forward `Rest` while
  accumulating the backward one.  Includes round-trip `exec` tests.
  (Distinct from `RWhileRev`, which proves the same for the *untimed* main
  syntax.)
- `RWhileSIInv.agda` — the corollary: feeding `SI` the encoded **inverse**
  program undoes the run, within the same bound (`si-inverse-linear`), and
  forward-then-backward through one and the same interpreter stays linear
  (`si-round-trip`).  Reversible languages get backwards execution at no
  asymptotic cost — machine-checked.  And since `SI` is itself an R-WHILE
  program, `si-uncompute` applies `inv` to the INTERPRETER: `inv SI` returns
  the interpreter from its final state to its initial one in **exactly the
  same number of steps** the interpretation took.
- `RWhileTimeDec.agda` — `Wf` and `InR` are **decidable** (`wf?`, `inR?`), so a
  concrete program's static conditions are discharged by evaluation rather
  than by hand (`Wf!`, `InR!`).  `Wf SI` takes 3.9 s / 405 MB.
- `RWhileSIProg.agda` — the same statement in modular form: the dispatch body
  is a parameter (`record Realises`), giving `j ≤ (4(C+1)+2)·k` for any `STEP`
  that realises one machine step at cost `C`.  `RWhileSISim` discharges it
  concretely; this module records the shape of the argument.
- `RWhileSIShow.agda` / `RWhileSIP2D.agda` — the two halves of the
  differential story against the OCaml implementation: `showC` prints a `Cmd`
  in R-WHILE's concrete syntax (so `./extract-si.sh` can write the verified
  interpreter out as `extracted/SI.rwhile`, 2124 lines, which `src/ri` parses
  and runs), and `⌜_⌝ᵖ`/`showV` model `src/Program2DataRwhile.ml` closely
  enough that the printed encoding matches `./ri -p2d` VERBATIM on eight
  programs, with `p→u-ok` proving the translation into this development's
  uniform encoding.
- `RWhileSITest.agda` — executable tests: the type checker runs `exec` on
  concrete interpreter stores and checks both the result and the step count
  against the proved cost formulas (push/pop 9, walk 58, `lkE` 83/27, `updE`
  87 and its involution, `opdC` 92/6, `evalC` 227 and its involution).

Scope: expressions are flat and `<=` is not in the object language, so the
constant is larger than the real `ri.rwhile` (measured a-rev ≈ 364); the
design — agenda, reassembly, tag algebra, compute–use–uncompute — is the same.
