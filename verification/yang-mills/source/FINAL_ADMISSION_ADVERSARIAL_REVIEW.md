# Internal review of proof-admission tooling

> **Review status:** This is an internal AI-assisted assessment, not independent
> human expert validation. Its historical conclusions remain revisable;
> `FINAL` and `READINESS` in file names are workflow labels. See the
> [witness audit and open validation questions](WITNESS_AUDIT.md).

> **Current disposition:** The concrete source/action, canonical reconstruction,
> Fourier/Taylor, normalization, insertion/OPE uniqueness and stress-transport
> checks are recorded as completed. See the [verification record](VERIFICATION_RECORD.md).
> No existence proof or external acceptance is asserted.

The review below preserves the staged findings and their subsequent repairs.
Instructions to keep admission closed refer to that earlier stage; use the [current policy](STATEMENT_POLICY.md)
for present admission rules.

The malformed-proof reporting issue was subsequently corrected with six added
regressions.

This review concerns the proof-admission software: what it reads from Lean, which
theorem shapes it accepts, and which invalid submissions it rejects. Its evidence
consists of declaration inspection and rejection tests, not a positive existence
theorem.

Read the kernel checks before the reporting rules. The staged activation instructions
and original reporting defect are historical; the current disposition and verification
record describe their resolution.

For terminology, start with the [relevant glossary section](GLOSSARY.md#reading-a-formalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

Reviewed staged admission handoff SHA
1c45ca70a1835d71cd08d35fc94383b0bbffd1041bacdad88a207db14ae2f605, InspectProof.lean SHA
b58c9559b3630be442d6d78db21463e2ddfc3aef59f120c44c8a20fe1bf69b55, verify_submission.py
SHA 5d3b56da8f963a8cde340fc1bd16033d35192d0ec4df25da2ef3b42d114263d5, and Audit.lean SHA
54256ff19a65f535599eb758e4f5a1ae784f1911bd555542a94ac3059691db24. No owner source files
were edited. This is an admission-mechanism review, not an existence proof or external
acceptance decision.

## Kernel admission

InspectProof obtains declarations from the imported checked kernel environment, not
submitted audit commands or submitted success text. It requires the actual YM target to
be a definition, a closed Prop with exactly one [universe parameter](GLOSSARY.md#reading-a-formalization), and raw body forall G :
CompactSimpleGaugeGroup.{u}, Nonempty (FilteredGeneratedCandidate.{u} G). It rejects a
True placeholder, a different candidate, an axiom target, a conditional wrapper or a
fixed group universe. Nonempty's argument universe is checked by Lean's declaration
typing; it is not an independent untyped string.

The submitted YM declaration must be a theorem with exactly one universe parameter used
as that very target's universe argument. A fixed-zero theorem, a fixed-zero theorem
carrying an unused universe parameter, and a theorem carrying two universe parameters
are rejected. Extra term hypotheses, including an assumed target or False premise, fail
the raw target-type check. Definitions, opaque proof values and axiom declarations fail
the theorem-kind check.

CollectAxioms traverses the submitted theorem's dependencies. Only propext,
Classical.choice and Quot.sound are allowed; sorryAx and an assumed custom oracle are
rejected transitively. Honest definitionally equivalent proof presentations can submit
an unconditional wrapper theorem of the exact target. This strict submission syntax adds
no new physics assumption.

The interactive YM Audit command independently requires theorem kind, the same
one-used-universe exact target type and the same axiom allowlist. It imports the trusted
actual specification. The independent inspector also checks the definition's raw shape
and is the public runner's acceptance authority. Neither mechanism is advertised as a
hostile-IO or modified-toolchain sandbox. The checkout/toolchain must remain trusted, as
the handoff explicitly states.

## Policy and status separation

Both staged trusted activation flags remain false. Metadata labels and proof text cannot
activate the runner. A complete coverage inventory is insufficient without explicit
activation and successful actual build/compiled target-shape inspection. Root must flip
both flags only after integrating and checking the final reviewed mathematical source.
The full integration suite checks the Audit command's status against the runner's
activation state.

Specification-only readiness requires no existence proof and does not claim one was run.
With no proof, the YM proof mode reports PROOF_NOT_SUBMITTED and not-run [kernel verification](GLOSSARY.md#reading-a-formalization).
Accepted exact proof status is distinct from specification readiness and distinct from
[QFT](GLOSSARY.md#quantum-fields-and-distributions)-only acceptance. The clay name is only a compatibility alias:
clay_certificate remains false and external acceptance remains not_assessed on every
branch. No [CMI](GLOSSARY.md#notation-and-source-abbreviations) acceptance is claimed.

The corrected QFT mode explicitly reports YM readiness and semantic review as
not_assessed_in_qft_mode, with full_target_defined null and no YM shape check. It
therefore does not falsely call a globally reviewed target incomplete.
Formalization/provenance labels remain distinct from trusted semantic-review readiness;
interpretedModel does not falsely become literal source text.

## Small report-state issue reported to root

After successful YM shape/readiness checks, malformed proof arguments (only a theorem
name, an invalid name, unreadable or non-.lean source) return failure but leave the
initial top-level status INVALID_SPECIFICATION, while readiness is already ready. These
are invalid proof submissions, not invalid specifications. Set an appropriate
invalid-submission status at those argument checks and retain the successful
specification fields. This issue is a misleading failure label, not a [kernel acceptance](GLOSSARY.md#reading-a-formalization) bypass.

No owner file was modified by this reviewer.

## Independent validation

The 28 Python unit tests independently pass with
`YM_VERIFIER_TEST_ROOT` set to the repository root. Mocked inspector outcomes in these
tests exercise runner branches only; they are not Lean existence proofs. The first
attempted run against [PRIMARY](GLOSSARY.md#notation-and-source-abbreviations) scratch lacked the pinned PDF and failed source setup;
rerunning against the intended actual repository passed. This setup failure is not
reported as a mathematical regression.

The real compiled inspector suite independently completed with exit 0 against the actual
repository: the literal all-group target-shape check passed, and all 12 real negative
cases were rejected. These cover wrong type/True, direct sorry, monomorphic fixed zero,
fixed zero carrying an unused parameter, extra universe, custom assumed target, axiom
kind, conditional target, False-premise elimination, and non-theorem definition. The
spoofed audit syntax in the fixture did not replace the independently run inspector.

No positive proof of either existence theorem is fabricated by these tests. Root's
post-integration build, full proof-audit suite and activation tests remain required
before the staged patch is activated.

## Verdict

No kernel acceptance loophole was found in the reviewed scope. The staged exact-target
mechanism is suitable for integration after correcting the small invalid-proof status
label and passing root's actual combined checks. Keep the activation flags disabled
until that integration is complete. This verdict certifies neither an existence theorem
nor external/CMI acceptance.
