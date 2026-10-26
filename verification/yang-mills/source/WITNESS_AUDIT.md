# Witness constraints and open validation questions

This is a navigation aid for evaluating the proposed specification, prepared
in response to a structural critique on 22 October 2026. It is another internal,
AI-assisted inspection, not independent expert validation or a recursive audit
of every imported definition. It makes no new theorem claim.

The user identified the critique's model as **Claude Sonnet 5.5**, with
**medium** reasoning effort. This is user-reported provenance, not a verified
session record. The critique covered the README and
`FilteredGeneratedCandidate.lean` and explicitly excluded an audit of the
imported definitions. The attribution applies to the critique, not to this
response or to the repository's earlier internal reviews.

The target fixes a proposition. That does not establish that the proposition
is an adequate formulation of Yang–Mills. Both under-constraint (an unintended
model satisfies it) and over-constraint (a source-admissible presentation is
excluded) remain legitimate review questions. Earlier `FINAL_*` and
`*_READINESS_*` file names record internal development stages; their conclusions
are revisable. Terms used below are explained in the [glossary](GLOSSARY.md).

## Witness freedom and where it is constrained

Start at [FilteredGeneratedCandidate](../YangMills/FilteredGeneratedCandidate.lean).
All its fields are supplied by an existence witness, including objects with
embedded proof obligations. A field's being dependent on another object is
useful evidence of a link; it is not proof that every relevant constraint is
sufficient. Follow the named fields below into their definitions.

| Supplied fields | Concrete constraints to inspect | What still needs mathematical assessment |
| --- | --- | --- |
| `theory`, `qft_and_gap` | [GappedWightmanTheory](../YangMills/QFT/Wightman.lean) contains `axioms` and `massGap`; the gap uses the physical Hamiltonian's real spectrum. | Adequacy of the full domain, continuity, locality and spectral formulation; these QFT conditions alone do not identify Yang–Mills. |
| `vacuumKernels` | [WightmanVacuumKernels](../YangMills/WightmanVacuumKernels.lean) binds full continuous kernels to the actual field words on tensor tests. | Comparison with the cited framework, including completeness of the multiplet presentation and test-space conventions. |
| `form` | [InvariantForm](../YangMills/Classical.lean) requires symmetry, strict positivity on nonzero vectors and invariance under the actual Lie bracket. `sector.same_stress` equates `stress.traceForm` to it. | Whether normalization changes are handled coherently everywhere; positivity alone does not prove this. |
| `colorFrame` | [ColorFrame](../YangMills/Renormalization.lean) is a basis orthonormal for that same form. Structure constants are computed from the bracket and basis. | Adequacy and coordinate independence of every downstream contraction, not just the basis type. |
| `engine` | [FixedFlowSystem](../YangMills/PerturbativeCoefficientLimits.lean) supplies a reference scale, local scheme and amplitude families, with `background_equations` and `insertion_equations`. | Follow the flow, regularity and boundary definitions; establish that the permitted schemes neither erase the intended interactions nor exclude justified presentations. |
| `wardFamily` | [LocalWardFlowFamily](../YangMills/LocalWardFlowFamily.lean) requires `full_ward`, `local_extension`, `same_cumulants`, scaling bounds and physical-word conditions for that engine. | Check local contact freedom, null directions and compatibility of the simultaneous requirements. This table does not audit their full imports. |
| `basis`, `generated` | [FilteredBasis](../YangMills/OperatorProductExpansion.lean) supplies the classical basis. `LocalWardCoefficientFamily.compatible` invokes [GeneratedEuclideanData.Compatible](../YangMills/GeneratedEuclideanCoefficients.lean), including `raw_limit`, `physical_recovery` and `same_flow_continuum`. | Whether physical recovery leaves unintended freedom, particularly through quantum null directions; a classical basis is not a quantum injectivity theorem. |
| `normalization` | [GeneratedScaleNormalization](../YangMills/GeneratedScaleNormalization.lean) supplies beta, field, mixing and primitive data with graph bounds and `same_scale_insertion`. Beta and gamma series are computed from those supplied, constrained data. | Whether the full CS residual equations constrain the physical predictions sufficiently. “Generated” does not mean uniquely determined by `G` alone. |
| `composites`, `kernels` | `sector.correspondence` invokes [Compatible](../YangMills/CompositeFields.lean), including identities, descendants, covariance, unit, Hermiticity and composite-only `cyclic`. [MultiKernels](../YangMills/MultiOperatorProductExpansion.lean) ties kernels to those fields. | Cyclicity prevents an invisible extra sector; it does not by itself distinguish an interacting theory from a free one. |
| `coefficients` | `sector.physical_ope` invokes [WeakMultiExpansion](../YangMills/MultiOperatorProductExpansion.lean). `matching.coefficient_matching` in [FilteredQuantumRG](../YangMills/FilteredQuantumRG.lean) imposes all-order matching. | Sufficiency of the distributional topology, collision domain, truncations and quantifier order; whether these conditions leave an unintended model possible. |
| `physicalCoefficients` | `sector.continuation` invokes `GeneratedContinuation` in [FilteredQuantumRG](../YangMills/FilteredQuantumRG.lean): one raw continuation family connects generated Euclidean coefficients to these coefficients using the same Wick rotations. | Adequacy of the analytic-continuation and recovery constraints. This field is an order-indexed perturbative comparison family, distinct from the exact OPE `coefficients`. |
| `stress`, including its coupling | [StressTensorData.Compatible](../YangMills/StressTensor.lean) imposes symmetry, conservation, covariance and graph-core charge limits. `same_stress` fixes its form, reference scale and coupling to the common running system. `generated_stress_reference` and `same_stress_rg` add generated binding and transport. | Whether the chosen charge and stress presentation is justified and whether the complete matching rules exclude unintended models. Coupling equality is a constraint, not a proof of sufficiency. |
| `curvatureSquare` | [HasCenteredTraceAnomaly](../YangMills/CenteredTraceAnomaly.lean), required by `same_stress`, fixes its evaluation on every smooth connection to `classicalCurvatureSquare stress.traceForm` and imposes the centered field equation. | Whether the composite correspondence and trace relation jointly have the intended physical strength; the label is not an arbitrary scalar subtraction. |
| `sector` and its running/frame data | [GeneratedSector / GeneratedMatching](../YangMills/FilteredQuantumRG.lean) combine the requirements. `common_running`, `common_gamma`, `actual_transport`, `coherent_transport` and `actual_words` link finite sectors and actual vacuum words. | Audit the conjunction. No individual row demonstrates that the full candidate is satisfiable, faithful, unique, or excludes every wrong model. |

This distinguishes three kinds of freedom: coordinate/normalization choices,
solutions of fixed auxiliary equations, and genuinely nonperturbative data.
Their intended admissibility must be justified; the labels themselves do not
justify it. Proving uniqueness of every auxiliary choice is not automatically
necessary, but any residual freedom that changes required physics is relevant.

## Countermodel tests and their present status

The following are different levels of evidence. In particular, malformed-proof
rejection tests exercise the verifier, not the mathematical strength of the
Yang–Mills predicates.

| Challenge | Present evidence | Limit or next falsification task |
| --- | --- | --- |
| Vacuum-only spectrum | [vacuum_only_has_no_finite_mass](../YangMills/Spectrum.lean) proves the spectral obstruction. | It excludes this case, not all non-Yang–Mills spectra. |
| Identically zero stress | [FilteredGeneratedCandidate.stress_nonzero](../YangMills/FilteredGeneratedCandidate.lean) is a derived theorem using the actual charge/gap conditions. | A nonzero stress tensor is not an interaction test. |
| Attach a group label or separate classical laws to an arbitrary QFT | [qft_exists_implies_unlinked_group_checks](../YangMills/GroupwiseNecessary.lean) is a conditional negative control for a weaker target. | It is not a constructed free-model counterexample to the full candidate. |
| Choose asymptotic coefficients to fit any correlation | [selfSelectedExpansion](../YangMills/Ultraviolet.lean) demonstrates a loophole in a weaker helper relation. | Trace the full generated/continuation/CS constraints before claiming this attack succeeds or fails in the full target. |
| Add a physically excited sector invisible to the composites | `RenormalizedCompositeMap.Compatible.cyclic` is the relevant density condition. | A visible spectator must be tested against the full word/OPE/stress conditions; no universal exclusion theorem is asserted. |
| Massive free or generalized-free model | No full witness construction or general full-target exclusion theorem is supplied. A generalized-free field has Gaussian correlations determined by a chosen two-point function, potentially with a continuous mass distribution; see [Dütsch–Rehren, §1](https://arxiv.org/pdf/math-ph/0209035#page=2). | Choose a concrete model and observable assignment; compute a group-sensitive correlation channel and its first nonzero prescribed correction; identify the exact matching or Ward clause it violates, or construct all remaining fields if it survives. Do not identify composite correlators with elementary Gaussian correlators. |
| Flat nonperturbative deformation | [HasPerturbativeJet](../YangMills/RenormalizationGroup.lean) and the all-order matching definitions allow beyond-all-orders differences. | A flat change preserves asymptotic coefficients only; separately test positivity, locality, full field products, contact identities, charge limits and the common running system. No such full deformation is constructed here. |
| Convention-induced inconsistency | Existing reviews record and repair particular sign, degree and smoothness mistakes. | Independently check a nontrivial finite-order channel through action, extraction, Wick rotation, scale transport and stress normalization. Prior repairs do not exclude another mismatch. |

For the generalized-free challenge, stress regularity needs particular care.
[Dütsch and Rehren](https://arxiv.org/pdf/math-ph/0209035#page=3) construct a
singular stress density as a quadratic form, rather than a Wightman field
operator. That result is not a witness of this repository’s stronger stress
requirements, nor a theorem that every generalized-free assignment fails them.
A proposed test must compare the actual operator/domain requirements.

“All orders” fixes every finite-order asymptotic coefficient, not a unique exact
function. Allowing flat terms is therefore an explicit interpretive choice,
not an argument that the resulting physical conditions are sufficient. Adding
convergence or uniqueness merely to remove this ambiguity could instead
strengthen the source problem unjustifiably. The correct comparison is a
mathematical review question.

## Source, provenance and external review

Both previously reported access gaps were closed on 22 October 2026 with
user-supplied PDFs. The [Chapter 3 comparison](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026)
of Streater–Wightman, *PCT, Spin and Statistics, and All That* uses the 2000
reissue, not a checked copy of the 1964 printing cited as Jaffe–Witten [45].
It records actual axiom/page locations and open comparisons for domains,
continuity, the spin cover, covariance, spectral support and locality.
The [OS II reading](SOURCE_ANALYSIS.md#direct-os-ii-reading-22-october-2026)
records its corrected reconstruction conditions. These are direct source
readings, not completed equivalence proofs or independent expert validation.
Chapter 3 itself discusses free and generalized-free examples (pp.102–105);
it therefore reinforces, rather than settles, the countermodel question above.

The [AI disclosure](../README.md#6-ai-disclosure) records the models identified
in coordinating-session metadata and their work areas. It does not establish
all delegated models or per-file authorship. No retrospective authorship
percentages should be inferred from commit count, line count or agent roles.
For future contributions, record the changed files, actual model/session
provenance, human review performed and exact tested revision when available.
Low or high reasoning settings, repository age and documentation volume are
neither correctness proofs nor counterexamples.

An external review should return a scoped finding: definitions inspected,
source passages compared, a concrete counterexample or over-constraint if
found, and unresolved obligations. A proposed countermodel must satisfy all
fields to refute the full specification; a partial failure can still identify
a useful test. A source-fidelity review need not solve the existence problem.
No external expert review was obtained as part of this response. The present
artifact is a reviewable proposal, and this audit does not elevate its status.
