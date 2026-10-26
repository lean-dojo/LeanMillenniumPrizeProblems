# Provenance and readiness answer different questions

**Provenance** records where a formal requirement comes from. **Readiness** records
whether the repository regards its proposed specification as complete under the
documented interpretation. A provenance label is neither a physics assumption nor a
readiness verdict.

The source is Jaffe–Witten §4, printed p.6, with its action, [QFT](GLOSSARY.md#quantum-fields-and-distributions) context and
cited mathematical standards. Each row in the [source registry](requirements.json) has both an acceptance role and
a provenance classification. The [requirements table](REQUIREMENTS.md) explains the roles; the classifications are
described below.

## How to read the classifications

| Registry value | Meaning | Example |
| --- | --- | --- |
| `literal_form` | Mathematical shape written directly in the source. | The universal group quantifier, full four-dimensional spacetime, or the physical spectral gap interval. |
| `cited_framework` | Meaning delegated to a cited axiom system. | The complete [Wightman](GLOSSARY.md#quantum-fields-and-distributions) formulation of QFT. |
| `interpretation_needed` | A phrase requiring mathematical interpretation. This legacy name does not mean a definition is still missing. | The fixed, reviewed interpretation of prescribed quantum predictions. |
| `nonbinding_guidance` | Guidance retained without turning it into an extra mandatory theorem. | Footnote 1's expectation of a dimension-filtered observable relationship. |

For terminology, see the glossary entries on [formalization](GLOSSARY.md#reading-a-formalization) and [filtrations](GLOSSARY.md#gauge-fields-and-observables).

## Where the interpretation is recorded

[SourceClassification.lean](../YangMills/SourceClassification.lean) records declaration origins. Its `interpretiveScope` list documents presentation
choices. The legacy name `interpretationStillNeeded` is a compatibility alias, not a list of outstanding
gaps. Optional lattice, holonomy and other construction lemmas remain possible methods
rather than compulsory parts of the target.

The [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md), [current crosswalk](CURRENT_JW4_READINESS_CROSSWALK.md) and [final adversarial review](FINAL_ADVERSARIAL_REVIEW.md) record present readiness and the supporting
interpretation.

## Why metadata cannot certify a proof

The verifier separately checks source roles, trusted review activation, the compiled
target shape and any submitted proof. Editing a label does not supply a mathematical
argument or activate admission. Compilation and agent agreement also do not establish
[source fidelity](GLOSSARY.md#reading-a-formalization).

No interpretation supplies an existence assumption, and no kernel result asserts
external acceptance. The [certification contract](../CERTIFICATION.md) sets out those distinct checks.
