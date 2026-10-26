# Final verification record

This record reports checks already performed on the reviewed specification and its
proof-admission tools. It is not a record of a Yang–Mills existence proof. [Kernel verification](GLOSSARY.md#reading-a-formalization) of
a future existence submission has not run; external acceptance is not assessed, and no
Clay certificate is claimed.

For the meaning of the statuses, see the [certification contract](../CERTIFICATION.md). For unfamiliar mathematical terms,
use the [glossary](GLOSSARY.md). The results below are historical run results; editing this document
does not constitute rerunning those checks.

## What was checked mathematically?

The pinned Lean 4.25.0/mathlib environment compiled the central supporting bridges with
warnings treated as errors. These connect the definitions at several stages:

- Canonical high-[UV](GLOSSARY.md#scales-and-renormalization) reconstruction and literal Fourier/Taylor recovery.
- Integrated versus computed pointwise normalization, including [marginal](GLOSSARY.md#scales-and-renormalization)
  and [Ward](GLOSSARY.md#graded-gauge-symmetry) normalization.
- Single- and multiple-insertion uniqueness, scalar [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) extraction and
  [ultraviolet](GLOSSARY.md#scales-and-renormalization)-limit uniqueness.
- Transport of the same physical [stress tensor](GLOSSARY.md#scales-and-renormalization) across scales.

Earlier integrated runs also checked the `C∞` corrections, canonical smooth
insertion [determinacy](GLOSSARY.md#analysis-and-asymptotics) and centered stress-trace changes. They passed 3163 build jobs, 21
runner regressions, 15 proof-audit cases and the inspector checks then in use. These are
supporting lemmas and specification checks.

## Staging results and independent review

The final activated combined suite passed in the isolated staging copy: 34 runner
regressions, the default strict build with 3182 jobs, 15 proof-audit cases, the compiled
literal all-group target-shape check, and all 12 real kernel rejection cases. Initial
audit-list namespace typos were corrected before the final run.

Independent source and adversarial reviews of that assembly found no concrete remaining
mathematical blocker. They checked the links among the same group, action,
normalization, composite map, fields, vacuum words, OPE, stress tensor and translations.
They also checked the degree-four stress versus degree-five [BRST](GLOSSARY.md#graded-gauge-symmetry) response and the
use of `C∞` smoothness. The [source crosswalk](CURRENT_JW4_READINESS_CROSSWALK.md) records framework-access qualifications.

## Actual-repository results

Guarded integration copied 40 reviewed files. Before the final record and crosswalk
wording update, all 40 were byte-identical to their tested staging versions. The
actual-repository default strict build passed all 3182 jobs, including the new central
bridge axiom audits. The 34 runner tests and all 15 proof-audit cases passed.

The public reports returned the following results:

| Invocation | Result | What remains unproved |
| --- | --- | --- |
| `--claim specification` | `SPECIFICATION_READY`; readiness `ready`; source PDF hash verified; exact target shape `passed`; no incomplete coverage clauses; fixed all-group target defined. | Existence of a candidate for every allowed group. |
| `--claim yangmills` without a submission | `PROOF_NOT_SUBMITTED`, expected exit 2; specification readiness stays `ready`. | No proof was submitted or kernel-verified. |
| Both modes | Proof `not_submitted`; existence-kernel verification `not_run`; external acceptance `not_assessed`; `clay_certificate=false`. | No external acceptance is asserted. |

The independent compiled kernel suite passed the literal all-group definition-shape
check and rejected all 12 malformed submissions. The complete actual-repository
verification command exited 0. These negative fixtures do not fabricate a positive
existence proof.

## Scope of the recorded result

The final verification record and last historical crosswalk wording update were
documentation-only changes after that successful run. Mathematical sources,
proof-admission implementation and metadata were unchanged by those updates. For the
current claim and its interpretation, consult the [statement policy](STATEMENT_POLICY.md) and [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md).
