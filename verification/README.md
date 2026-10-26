# Yang–Mills specification verification

`yang-mills/` imports the full proposed specification, supporting Lean proofs,
source records and proof-admission tools from
[`alxwest/ym-lean` at `fffe6e5`](https://github.com/alxwest/ym-lean/tree/fffe6e5ab43faa8625aff0d10e6333717384a424).
The exact revision and SHA-256 of every imported file are recorded in
`yang-mills-source.json`. The imported files are unchanged from that snapshot.

This is a separate Lake project pinned to **Lean 4.25.0** and its original
Mathlib revision. The repository's main project remains on **Lean 4.31.0**.
Lean compiled modules cannot be shared across those versions, so the imported
library is checked in its own environment rather than imported by `Problems`.
No equivalence with `MillenniumYangMills.ClayYangMills` is asserted. That legacy
sketch and its `statement_incomplete` registry status remain unchanged.

## Run the checks

Install Lean's `elan` toolchain manager and Python 3.10 or newer. From the
repository root, obtain the pinned dependency cache once:

```bash
(cd verification/yang-mills && lake exe cache get)
python3 scripts/yang_mills.py check --report verification-report.json
```

The command checks the import hashes, runs the Python verifier regressions,
builds the full imported library, runs the Lean axiom-audit and compiled
invalid-submission cases, and checks the compiled specification's shape.
CI runs the same command in a dedicated job on pushes to `main` and `ym`, and
on pull requests. Its report is uploaded as a workflow artifact.

For just the source integrity or specification check:

```bash
python3 scripts/yang_mills.py integrity
python3 scripts/yang_mills.py verify --claim specification
```

For a future proof file outside the imported snapshot:

```bash
python3 scripts/yang_mills.py verify --claim yangmills \
  --proof-file submissions/MyProof.lean --theorem MyNamespace.myProof \
  --report verification-report.json
```

File arguments are resolved relative to the calling directory. The wrapper
preserves the verifier's exit codes: 0 for accepted specification/proof checks,
1 for rejection or infrastructure errors, and 2 for an incomplete specification
or missing proof. Do not add submissions inside the pinned source snapshot.

## What is checked

The imported target is `YangMills.YangMillsExistenceAndMassGap.{u}`:
for every `CompactSimpleGaugeGroup.{u}`, a `FilteredGeneratedCandidate` exists.
The inspector checks the actual compiled declaration, universe generality and
transitive axioms. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
It rejects proof holes, extra assumptions, wrong targets and fixed-universe
substitutes. The official Jaffe–Witten PDF is also checked against its pinned hash.

**No Yang–Mills existence proof is included.** `SPECIFICATION_READY` is the
upstream verifier's internal status, not independent validation that the formal
statement captures the source problem. The report keeps `clay_certificate`
false. See the imported [contract](yang-mills/CERTIFICATION.md),
[witness audit](yang-mills/source/WITNESS_AUDIT.md),
[direct source comparisons](yang-mills/source/SOURCE_ANALYSIS.md), and
[AI disclosure](yang-mills/README.md#6-ai-disclosure) for scope and provenance.

The integrity manifest detects accidental drift; it is not a security boundary
against someone who can edit both code and manifest. The verifier assumes a
trusted checkout/toolchain and is not a sandbox for hostile Lean programs.

## Updating the import

Choose and record an exact upstream commit, replace the tracked source snapshot,
and regenerate every file hash in `yang-mills-source.json`. Review mathematical
and verifier changes together and run `scripts/yang_mills.py check` before
accepting the update. Keep the upstream model-attribution and source-review
records with the code; a successful build does not replace that review.
