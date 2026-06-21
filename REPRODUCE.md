# Reproducing the results

One command reproduces the machine-checkable claims (see also `README.md`,
`FINDINGS_reversible_projections.md`, `AGDA_CORRESPONDENCE.md`):

```bash
./reproduce.sh          # fast: build + fp1 residual sizes + Agda --safe check
./reproduce.sh full     # also comp2 (fp2) size + the Simp reduction (slow, minutes)
```

Requirements: OCaml + `ocamlfind`/`extlib` and BNFC (for `src/`), and Agda +
`standard-library` (for `proofs/agda/`). See `README.md`.

## Expected results

### Futamura-projection residual sizes (`src/measure_proj`)

| quantity | value | meaning |
|---|---|---|
| `|spec_av|` | 817,701 nodes | the specialiser, as data |
| `|ri_min|` | 163 nodes | the minimal interpreter |
| fp1 residual `[spec_av]((ri_min.swap))` | **103 nodes (0.63× ri_min)** | specialisation is effective (residual < interpreter) |
| fp1 residual `[spec_av]((ri_min.id))` | 63 nodes | |
| comp2 `[spec_av]((spec_av.ri_min))` | 812,515 (0.994×\|spec_av\|) | trivial self-application |
| comp2 after `Simp` | 597,961 (−26.4%, 0.731×) | semantics- & reversibility-preserving simplification |
| `[comp2_simp](('S.swap)) == B` | true | meaning preserved |

(`comp2` rows require `./reproduce.sh full`.) Diagnosis of why comp2 does not
shrink further (125 dynamic store-index loops) is in
`analysis_store_bti.md` (`measure_proj full` prints the constructor breakdown).

### Machine-checked proofs (`proofs/agda/check.sh`)

```
PASS=35 FAIL=0
```

All modules typecheck under `--safe` (no postulates beyond one `funext`). The
module ↔ result inventory is in `proofs/agda/README.md` and
`AGDA_CORRESPONDENCE.md`.

## Notes

- `src/` ships build artifacts gitignored; a fresh checkout runs BNFC via `make`.
- The OCaml test suite (`make run-tests`, Alcotest) covers store ops, evaluation,
  inversion, macro expansion, program-to-data, Core-IR equivalence, and the
  Futamura/specialisation tests; run a single group via `./test-suite <group>`.
