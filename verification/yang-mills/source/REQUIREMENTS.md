# Current source-clause coverage

This table is an index of the requirements in the proposed specification. All required
meanings are fixed in the same-theory assembly. Here **formalized** means that a
reviewed definition is present; it does not mean an existence theorem has been proved or
externally accepted.

Read the [source crosswalk](CURRENT_JW4_READINESS_CROSSWALK.md) for the detailed source-to-definition comparison and the [fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
for the reasoning behind it. The [glossary](GLOSSARY.md) introduces the specialized terms used below.

## Required clauses and interpretive guidance

Registry identifiers are retained so this table can be compared directly with
[requirements.json](requirements.json). A `required` row is part of the target. The `interpretive_guidance` row records the
source footnote's guidance without adding a mandatory classical/quantum bijection.

| Clause identifier | Meaning | Role | Status |
| --- | --- | --- | --- |
| group | Every allowed compact connected simple Lie [gauge group](GLOSSARY.md#gauge-fields-and-observables). | required | formalized |
| spacetime | The physical theory lives on full four-dimensional spacetime. | required | formalized |
| [qft](GLOSSARY.md#quantum-fields-and-distributions)-axioms | The complete chosen quantum-field-theory framework. | required | formalized |
| ym-identification | The quantum theory is linked to Yang–Mills for the chosen group. | required | formalized |
| gauge-observables | Quantum fields correspond to [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) [curvature](GLOSSARY.md#gauge-fields-and-observables) and derivative polynomials. | required | formalized |
| renormalized-[filtration](GLOSSARY.md#gauge-fields-and-observables) | Dimension bounds guide the correspondence while allowing quantum relations and mixing. | interpretive_guidance | formalized |
| [ultraviolet](GLOSSARY.md#scales-and-renormalization) | Short-distance correlations match the prescribed perturbative behavior. | required | formalized |
| [stress-tensor](GLOSSARY.md#scales-and-renormalization) | The same theory has the required [stress tensor](GLOSSARY.md#scales-and-renormalization) and physical translation charges. | required | formalized |
| [ope](GLOSSARY.md#short-distance-products-and-contact-terms) | Local operator products have the specified expansion and singularity behavior. | required | formalized |
| nontrivial | The identified theory has genuine physical excitations. | required | formalized |
| physical-gap | Its actual [Hamiltonian](GLOSSARY.md#operators-and-spectrum) has positive finite [spectral mass](GLOSSARY.md#operators-and-spectrum). | required | formalized |
| universal-existence | All required properties are requested simultaneously for every allowed group. | required | formalized |

## How to interpret the status

The target is [universe-polymorphic](GLOSSARY.md#reading-a-formalization). Proof submission, [kernel verification](GLOSSARY.md#reading-a-formalization) and external acceptance are
separately reported by the verifier. Source roles and provenance classifications remain
unchanged; see [formalization layers](FORMALIZATION_LAYERS.md).

Historical implementation reviews record earlier gaps. For present readiness, use the
final review documents and [verification record](VERIFICATION_RECORD.md), not an earlier snapshot's open-work list.
