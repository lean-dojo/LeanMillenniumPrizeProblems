# Independent adversarial specification review — 2026-10-20

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This early review tests whether an insufficient theory could satisfy the proposed
conditions. Each attack isolates a requirement: for example, adding a gauge-group label
to an unrelated massive theory does not make that theory Yang–Mills.

The attack table gives the motivating examples. Findings R1–R6 then explain which
definitions or comparison arguments were missing in that snapshot; later integration
notes record partial repairs.

For terminology, start with the [relevant glossary section](GLOSSARY.md#reading-a-formalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

**Decision: incomplete specification; exact full-target admission is not justified.**
This finding concerns missing definitions and equivalence/fidelity arguments. It does
not depend on the absence of a Yang–Mills existence proof. The independent role reviewed
the original Lean library and the proposed invariant-[jet](GLOSSARY.md#graded-gauge-symmetry), [UV](GLOSSARY.md#scales-and-renormalization) and
Hamiltonian/spectrum additions. Source access limitations are recorded in [SOURCE_ANALYSIS.md](SOURCE_ANALYSIS.md);
this review is not a completed equation-by-equation verification of references [27],
[35], [45].

Agent agreement and successful Lean builds do not establish [semantic fidelity](GLOSSARY.md#reading-a-formalization).

## Attack cases

| Attack | Evidence | Finding and disposition |
|---|---|---|
| Vacuum-only theory | `vacuum_only_has_no_finite_mass`; `GappedWightmanTheory.hasNonVacuumState` | Already excluded by finite supremum mass and actual [resolvent](GLOSSARY.md#operators-and-spectrum). This does not establish Yang–Mills identification. |
| Unrelated massive free [QFT](GLOSSARY.md#quantum-fields-and-distributions) | `QFTExistenceAndMassGap` contains no G or Yang–Mills identification | Remains admissible in principle as intended by this necessary QFT-only target. No concrete free model is constructed in Lean here; do not overstate this as a machine-checked free-field countermodel. |
| Unused gauge-group parameter | `qft_exists_implies_groupwise_qft` | Formal conditional counterexample: any single QFT [witness](GLOSSARY.md#reading-a-formalization) can be reused for all G. The groupwise shadow must never be admitted as the full target. |
| Disconnected classical gauge sector | `qft_exists_implies_unlinked_group_checks` | Formal conditional counterexample: even correct G-dependent lattice laws beside QFT do not identify the quantum theory. New classical invariant polynomials alone do not close this gap. |
| Arbitrarily chosen asymptotic coefficients | `WightmanData.selfSelectedExpansion`: term 0 equals the exact scaled correlator and other terms are zero | Any Q and test word then have zero remainder at order 1, for any rate. The relation is useful only when a fixed perturbative construction determines the terms. It is not a YM [predicate](GLOSSARY.md#reading-a-formalization) and must not be existentially promoted to one. |
| Independent positive [Hamiltonian](GLOSSARY.md#operators-and-spectrum) | `generator_domain` and `generator_action`; proposed domain/action uniqueness lemmas | The complete derivative domain and derivative fix H on the same translation dynamics. No disconnected-H loophole found in this component. |
| Continuous spectrum omitted | Two-sided bounded resolvent; proposed positive-spectrum equivalence | The gap is defined with full spectrum, not eigenvalues. No particle-isolation obligation is added. |

## Resolved limitations in proposed fragments

1. The existing trace-pair grammar excludes higher invariant tensors. `InvariantJetPolynomials` replaces this limitation at the **formal jet-polynomial level** by all finite multivariate polynomials fixed by the actual group's differentiated conjugation action. Its invariant ring has no degree-two restriction and no proof-author-selected invariance predicate.
2. The physical mass definition already has the necessary nonempty/bounded hypotheses. The proposed `mass_isMassGap` and `mass_le_positive_spectral_value` make the supremum meaning explicit. No arbitrary spectral set is used by the QFT target.
3. The proposed normalized [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) dilation evaluates the actual same-theory field words and vacuum. It does not supply unrelated [n-point](GLOSSARY.md#quantum-fields-and-distributions) values. The dimension-four normalization is a test-function Jacobian, not an assertion about anomalous field dimensions.

## Unresolved central findings

**R1 — Yang–Mills identification and prescribed perturbative data (blocking).** No fixed
construction maps the actual G action/Lie bracket to perturbative correlation and
composite [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) coefficients, running-coupling and mixing predictions. No relation
then imposes those predictions on the same Q's fields. Arbitrary terms can absorb all
dynamics; a classical action next to Q is insufficient. Needed: a fixed renormalized
perturbative presentation, exact admissible scheme transformations, composite-insertion
coefficient construction, and a fidelity/sufficiency argument before any target can
quantify witnesses satisfying these relations.

**R2 — Local geometry (blocking for the observable correspondence).** `onConnection_eq_of_covariant_jets` is
conditional on the covariance law for every connection jet. It does not define a local
gauge-transformed connection or prove the curvature/covariant-derivative transformation
rule. The final module defines the concrete quotient by equality on all smooth
connections, with well-defined evaluation and an exhaustive [filtration](GLOSSARY.md#gauge-fields-and-observables). This removes
formal identities by definition. Presentation-equivalence and gauge covariance are still
unproved; the renormalized quantum correspondence remains absent.

The new module correctly states its limitation; its name alone must not be taken as a
completed local gauge-invariance proof.

**R3 — [Renormalization](GLOSSARY.md#scales-and-renormalization) and [stress tensor](GLOSSARY.md#scales-and-renormalization) (blocking).** No completed quantum
mixing/correspondence or [stress-tensor](GLOSSARY.md#scales-and-renormalization) normalization links the local operator family to
translations and the physical H. A generic symmetric conserved tensor is insufficient:
its charges and normalization must connect to the same [unitary](GLOSSARY.md#operators-and-spectrum) dynamics, with
domains/limits and contact/improvement ambiguities specified. Do not impose a naive
classical/quantum bijection.

**R4 — UV/OPE topology and universality (blocking).** `TestwiseExpansion` concerns one fixed word
of factorized smearings, all insertions scaled toward a common origin, one finite order
and a supplied rate. It has no prescribed coefficient system, [spectator](GLOSSARY.md#short-distance-products-and-contact-terms)-insertion OPE
condition, collision configuration treatment, RG/mixing law, or established sufficient
distributional topology. A final definition must choose and justify these meanings;
pointwise numerical tests cannot automatically establish all distributions'
singularities.

The present helper is correctly documented as partial.

**R5 — Cited-standard adequacy (unresolved supporting equivalence work).** Strong
continuity, dense invariant domain, adjoints, locality, [cyclicity](GLOSSARY.md#quantum-fields-and-distributions) and [self-adjoint](GLOSSARY.md#operators-and-spectrum)
Hamiltonian data are substantial. Still needed: prove the chosen field formulation
yields the required multi-point [tempered](GLOSSARY.md#quantum-fields-and-distributions) distributions and matches the precise cited
[Wightman](GLOSSARY.md#quantum-fields-and-distributions) standard, and justify countable finite-component [bosonic](GLOSSARY.md#quantum-fields-and-distributions) SO+(1,3)
presentation as sufficient for pure [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) YM observables. An [OS](GLOSSARY.md#notation-and-source-abbreviations) alternative
must use the corrected OS II conditions.

Adding these requirements without checking derivability would risk strengthening the
source; declaring them consequences without proof risks weakening it.

**R6 — Group/nontriviality scope (unresolved fidelity work).** Connected compact Lie
groups with simple real Lie algebra are a plausible documented convention and allow
finite central quotients; the source convention must be justified and required groups
shown covered. Non-vacuum excitation alone is only a necessary nontriviality check until
R1 is closed. No ad hoc non-Gaussianity, confinement, isolated particle, universal
lattice, [regulator](GLOSSARY.md#scales-and-renormalization) or particular renormalization scheme is authorized.

## Admission recommendation

Keep full-target admission closed. Report specification readiness independently of proof
submission, kernel checking and external/CMI review. A future exact-target checker is
appropriate only after a fixed complete proposition and defensible fidelity argument
exist. These fragments and this review do not meet that condition. Missing existence
proofs are not a reason to leave the specification incomplete, and are not counted among
R1–R6.

## Verifier review

The proposed CLI adds a separate `specification` claim and reports fixed specification
readiness, proof submission, [kernel inspection](GLOSSARY.md#reading-a-formalization), semantic review and external acceptance
separately. The full gate remains closed even if every editable coverage label says
formalized. Reporting `existence_proof_required_for_specification: false` correctly respects this task. The declared QFT target
can still be checked without claiming full YM semantics. The initial `admitted_target`
assignment preceded acceptance; reviewer requested that it only be set after successful
independent inspection (or be renamed to `requested_target`).

The explicit new `selfSelectedExpansion` theorem records the freely chosen coefficient attack as a
Lean [negative control](GLOSSARY.md#reading-a-formalization). This resolves the risk of mistaking the generic remainder relation for
prescribed predictions; the missing fixed coefficient construction remains unresolved
R1/R4.

Primary-agent integration follow-up: the final polynomial module adds actual adjoint
identity/composition laws, a quotient by evaluation on all smooth connections,
well-defined quotient evaluation and exhaustive quotient filtration. These address the
missing quotient relation in R2, but do not establish gauge covariance,
invariant-representative adequacy or quantum correspondence. The primary agent also
inspected [27] pp657–659, 671–680; its warning about extra composite [spectators](GLOSSARY.md#short-distance-products-and-contact-terms)
strengthens the need for qualified collision/contact data in R4.

This follow-up records the integrated changes; the independent review itself does not
claim a full source equivalence proof.

The verifier's `admitted_target` issue was resolved in integration: assignment now occurs only
after successful independent inspection. A rejection regression asserts that no target
was admitted. All admission and kernel-inspector regressions passed in the requested
checkout.
