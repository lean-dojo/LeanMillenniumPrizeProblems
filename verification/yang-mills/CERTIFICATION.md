# Formal specification and proof-admission contract

This contract explains what the repository's verifier accepts and what that acceptance
means. The specification is an **internally reviewed formal proposal**; its fidelity
to the source problem has not been independently validated. **No existence proof is
supplied, and external acceptance has not been assessed.** These are three independent
states.

For an introduction to the mathematical target, read the [README](README.md). For terms such as
“[closed target](source/GLOSSARY.md#reading-a-formalization),” “universe” and “kernel,” see the [formalization glossary](source/GLOSSARY.md#reading-a-formalization).

## 1. Source and interpretation

The normative source is Jaffe–Witten, *Quantum Yang–Mills Theory*, §4, printed p.6,
together with its action/QFT context and cited mathematical frameworks. The [source registry](source/requirements.json)
records the exact repository PDF and its SHA-256 hash.

The [final fidelity argument](source/FINAL_FIDELITY_ARGUMENT.md), [current clause crosswalk](source/CURRENT_JW4_READINESS_CROSSWALK.md) and [final adversarial review](source/FINAL_ADVERSARIAL_REVIEW.md) explain the interpretive choices,
source-access qualifications and resolved findings. These documents give an internal argument for a proposed
sufficient presentation; they do not claim that the source determines a unique Lean
encoding.

The [witness audit](source/WITNESS_AUDIT.md) maps the constraints and open
validation questions. `SPECIFICATION_READY` denotes internal admission under
the configured checks, not an expert-reviewed equivalence to Jaffe–Witten.

## 2. The fixed mathematical target

`YangMills.YangMillsExistenceAndMassGap.{u}` requires a `FilteredGeneratedCandidate G` for every actual compact connected simple Lie
[gauge group](source/GLOSSARY.md#gauge-fields-and-observables) in universe `u`. A candidate contains mathematical objects and proofs
that those objects satisfy the fixed conditions. There is no freely selected Yang–Mills
[predicate](source/GLOSSARY.md#reading-a-formalization), assumed existence theorem or new axiom in the target definition.

The candidate binds all of the following to the same theory:

- The gauge group, action and auxiliary perturbative prescription.
- The physical [QFT](source/GLOSSARY.md#quantum-fields-and-distributions) and its renormalized observable correspondence.
- The full [Ward](source/GLOSSARY.md#graded-gauge-symmetry) and [Callan–Symanzik](source/GLOSSARY.md#scales-and-renormalization) identities, plus physical short-distance
  and operator product expansion ([OPE](source/GLOSSARY.md#short-distance-products-and-contact-terms)) matching.
- The [stress tensor](source/GLOSSARY.md#scales-and-renormalization) and actual time-translation [Hamiltonian](source/GLOSSARY.md#operators-and-spectrum), with positive
  finite [spectral mass](source/GLOSSARY.md#operators-and-spectrum).

The [glossary](source/GLOSSARY.md) explains these terms, and the [fidelity argument](source/FINAL_FIDELITY_ARGUMENT.md) gives their precise
relationships. The target does not additionally demand confinement, an isolated mass
eigenstate, a particular nonperturbative construction, a classical/quantum bijection,
convergence of the perturbative series, or uniqueness of exact [beta](source/GLOSSARY.md#scales-and-renormalization)-function
completions.

## 3. What each checker mode establishes

| Mode | Requirement and result |
| --- | --- |
| `--claim specification` | Needs no existence proof. After trusted review activation, source validation, a successful build and inspection of the compiled all-group target, it reports `SPECIFICATION_READY`. |
| `--claim yangmills` without a submission | Reports `PROOF_NOT_SUBMITTED`. |
| `--claim yangmills` with a submission | Requires a checked theorem of the exact target and passes it through the independent declaration and axiom checks below. |
| `--claim qft` | Checks the separate QFT-only proposition; it cannot certify the group-specific Yang–Mills specification. |
| `--claim clay` | A legacy spelling for mathematical proof checking; it does not change the meaning of acceptance. |

A submitted theorem must have exactly one [universe parameter](source/GLOSSARY.md#reading-a-formalization) and no extra hypotheses. The
independently run inspector checks its actual compiled theorem type and every axiom used
through its dependencies. It rejects a fixed-universe theorem, a different target, a
non-theorem declaration and unapproved axioms. An equivalent statement may be submitted
through an unconditional wrapper theorem of the exact target.

Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` are allowed. See [Lean's axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/)
for their role in the foundations. The [README](README.md#4-build-and-check-the-repository) gives the commands for checking the
repository and submitting a future proof.

Coverage labels alone cannot enable admission. The trusted implementation requires
explicit review activation and inspects the compiled definition, rather than accepting a
declaration name or editable status label. Reports include source, model and verifier
fingerprints, and distinguish readiness, proof submission, [kernel verification](source/GLOSSARY.md#reading-a-formalization), semantic review
and external acceptance.

## 4. What local acceptance does not establish

A Lean kernel proof proves the chosen formal statement relative to its foundations. It
does not mechanically establish fidelity to the source prose or acceptance by the
mathematical community.

The full axiom chapter cited as Jaffe–Witten reference [45] was not directly accessed;
that qualification remains explicit in the framework comparison. No external expert
endorsement or Clay Mathematics Institute decision is asserted. `clay_certificate` therefore
remains false even for a future accepted exact-target theorem. This checkout contains no
such existence theorem.
