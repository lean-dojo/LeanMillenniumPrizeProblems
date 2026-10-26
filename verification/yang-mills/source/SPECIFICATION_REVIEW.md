# Central Yang–Mills specification review — 20 October 2026

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This intermediate review describes the first central links among classical Yang–Mills
data, physical observables, stress and short-distance matching. The main question is
whether their coefficients are prescribed by the action or still supplied as inputs.

Start with the component table, then the OPE/RG conventions and repaired failure cases.
The work list and recorded verifier status describe this snapshot, not the current
admission state.

For terminology, start with the [relevant glossary section](GLOSSARY.md#scales-and-renormalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

**The complete fixed Jaffe–Witten target remains unfinished.** This continuation
implements central definitions and their same-theory links. It does not replace the
missing renormalized prediction prescription with assumed conclusions or
proof-author-selected meanings. No existence proof is required for this task.

## Implemented central objects and exact links

| Component | Definitions and behavior now encoded | Boundary |
|---|---|---|
| Actual G action | `PerturbativeYangMills`: [curvature](GLOSSARY.md#gauge-fields-and-observables), quadratic/cubic/quartic action, ordered [ghost](GLOSSARY.md#graded-gauge-symmetry) [vertex](GLOSSARY.md#perturbative-calculations), actual Lie-bracket contractions; action-expansion and convention-bridge proofs | Auxiliary perturbative presentation; no universal nonperturbative [regulator](GLOSSARY.md#scales-and-renormalization) requirement |
| All-order bare coefficients | `Renormalization`: fixed finite-cutoff covariance, derivative Fourier contractions, graded Wick signs, action insertion sum, coupling extraction and vacuum division | [Counterterm](GLOSSARY.md#scales-and-renormalization) normalization, [UV](GLOSSARY.md#scales-and-renormalization) removal, quantum gauge identities and [switching](GLOSSARY.md#perturbative-calculations) removal unfinished |
| Classical insertions | `classicalInsertionPolynomial`, `bareCompositeCoefficient`: actual [structure constants](GLOSSARY.md#gauge-fields-and-observables), commuting partial-[jet](GLOSSARY.md#graded-gauge-symmetry) derivation, covariant curvature descendants, source/canonical coupling factors, fixed bare insertion kernels | Evaluation/quotient-descent equivalences and renormalized insertion mixing unfinished |
| Physical composites | `RenormalizedCompositeMap`: real-linear actual finite combinations of Q fields on Q's original invariant domain, at each positive scale | Group-specific renormalized prediction link still missing |
| Correspondence behavior | `Compatible`: classical evaluation identities, unit, Hermitian fields, actual derivative descendants, [Poincare](GLOSSARY.md#quantum-fields-and-distributions) intertwining, composite-word [cyclicity](GLOSSARY.md#quantum-fields-and-distributions) | Universal polynomial-transform/descendant construction and complete scheme constraints need supporting work |
| Physical stress | `StressTensorData.Compatible`: same-C tensor, symmetry/covariance/conservation, admissible weak charge [smearing](GLOSSARY.md#quantum-fields-and-distributions) and [graph-core](GLOSSARY.md#operators-and-spectrum) charges to actual Q translations; time component is Q's [Hamiltonian](GLOSSARY.md#operators-and-spectrum) | Leading perturbative symbol and fixed beta/anomaly prescription unfinished; chosen graph-core presentation needs fidelity argument |
| Physical [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) | `PairKernels`, `FilteredBasis`, `WeakBasisExpansion`: product kernels fixed on a dense [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) tensor span by actual C-field products, coherent all-degree truncations, relative-only scaling, separated [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) field-word matrix elements | Full multi-cluster/contact prescription and supporting kernel/basis existence facts unfinished |
| UV/RG | `RunningCoupling`, `Frame`, `ExhaustiveMatching`: fixed-series all-order weak matching, intrinsic dimension powers, matrix logarithmic transport, common running system and compatible sectors exhausting the classical basis | [Formal series](GLOSSARY.md#perturbative-calculations) remain inputs pending the renormalized generator |
| Euclidean/physical bridge | `Wick.AnalyticContinuation`, `LabelRotation`, `RG.FamilyContinuation`: explicit [tube](GLOSSARY.md#analysis-and-asymptotics) holomorphy/boundary limits plus fixed time-index phases and incoming/outgoing tensor-label transport | Must establish these relations for the actual prescribed renormalized coefficients, including contact qualifications |
| Assembled central relations | `RG.CoupledSectorConditions`: the same C, exact coefficients, common running system, stress form/coupling/scale, and [analytic](GLOSSARY.md#analysis-and-asymptotics) coefficient family enter one formula | Parameterized relation, **not** the closed Yang–Mills target |

The classical basis is a basis of the classical [evaluation quotient](GLOSSARY.md#gauge-fields-and-observables) only. There is no
classical/quantum bijection, injectivity or multiplicative quantization requirement. The
physical [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions) is generated by C's own composite words, so unrelated extra Q fields
cannot silently supply its gap.

## Precise OPE and RG meanings

The actual pair kernel acts on a Schwartz test of `(x,y)`. [Cluster](GLOSSARY.md#short-distance-products-and-contact-terms) coordinates are
`(r,z)=(x-y,y)`. Center smearing remains fixed while the normalized relative test is
`scale^(-4) f(r/scale)`. Finite subtractions pair each coefficient with that relative test and
multiply by the actual output composite's matrix element on the center test. For
truncation degree D and every positive slack delta, `scale^(dim(a)+dim(b)-D+delta)` times the remainder tends
to zero through positive scales.

Dimensions are the least bounds in the evaluation-quotient [filtration](GLOSSARY.md#gauge-fields-and-observables), not inflatable
[witness](GLOSSARY.md#reading-a-formalization) labels. Spectator supports stay a positive distance from the center support.

OPE coefficient distributions satisfy explicit finite-order continuity bounds on every
compact support. They are not required to be globally [tempered](GLOSSARY.md#quantum-fields-and-distributions): the finite-[IR](GLOSSARY.md#scales-and-renormalization)
Euclidean exponential cutoff can continue to exponential timelike growth. Values on
noncompact Schwartz tests are auxiliary algebraic extensions; all coefficient conditions
observe compact tests. Physical product kernels remain genuinely tempered continuous
functionals, as required by the chosen [Wightman](GLOSSARY.md#quantum-fields-and-distributions) framework.

The map-on-label convention is `Q_base(v)=Q_run(R_t v)`, with `t=log(1/scale)`, `g'=beta(g)` and `R'=gamma(g)R`.
Canonical dimension transport uses input-degree sum minus output degree. The stripped
coefficient is `R Cbar (R^-1 tensor R^-1)`. Every finite-order remainder is [little-o](GLOSSARY.md#analysis-and-asymptotics) of the last
retained running-coupling power, not merely little-o(1). Smooth [beta](GLOSSARY.md#scales-and-renormalization) and
[gamma](GLOSSARY.md#scales-and-renormalization) completions may contain flat nonperturbative terms, but all perturbative jets
must equal the prescribed series. The exact series are **not yet fixed** by a completed
renormalized construction in this repository.

All finite sectors share one actual [running coupling](GLOSSARY.md#scales-and-renormalization), including its initial value and beta
completion, and coherent gamma/transport restrictions. Exact operator equations connect
their transport to C at both scales. The trace relation uses that same running beta, C,
invariant form, coupling and scale. Finite-mixing operator-component matrices and
[RG](GLOSSARY.md#scales-and-renormalization) label maps have explicitly different conventions; no universal
scheme-equivalence theorem is claimed.

Coordinate continuation alone is insufficient for tensor labels. Each covariant time
index contributes `-i`; curvature contributes its two indices and each derivative
contributes another. `LabelRotation` fixes the resulting complexified polynomial
transformation by actual connection evaluations. The coefficient bridge transforms both
incoming and outgoing labels accordingly.

## Adversarial findings resolved in the definitions

- An exact linear image of the classically traceless [stress tensor](GLOSSARY.md#scales-and-renormalization) would force
  quantum trace zero. That condition was removed. Stress has physical charge
  normalization and an explicit anomaly relation, with its prescribed symbol
  and beta identification still to be supplied.
- Spatial coordinate-translation generators have the metric sign needed for
  contravariant momentum charges. The stress charge equation includes it.
- Composite-only cyclicity closes the unused spectator-sector loophole.
- Intrinsic minimal degrees prevent inflation of bounds from weakening OPE or
  mixing conditions.
- One coherent filtered basis prevents duplicate or independently selected
  truncations from changing coefficient subtraction multiplicities.
- One common running system and actual operator transport prevent sectorwise
  or disconnected numerical RG data from masquerading as one theory.
- Tensor Wick transport prevents identifying Euclidean and physical coefficient
  components merely because their coordinate types agree.
- The old action convention's factor-two mismatch is exposed by proved
  normalization bridges; it is not silently equated with the canonical action.

The review also found that equal cutoffs or zero switching can erase bare interactions.
The finite-cutoff helpers permit these mathematical inputs, but **cannot** be accepted
as final predictions by existentially selecting them. Switching/cutoff removal and the
fixed local normalization are essential next work. The previous arbitrary-coefficient
[negative control](GLOSSARY.md#reading-a-formalization) remains relevant: parameterized asymptotic relations alone cannot define
prescribed predictions.

## Exact central work still required

1. Add local counterterm insertions and composite mixing to the fixed all-order
   construction, with the chosen flow/forest normalization and boundary data.
2. Define the complete graded quantum gauge/BRST/Slavnov–Taylor system. The
   renormalized interaction insertion is not merely the bare action derivative;
   its coefficients, quantum differential and contact antibracket must be
   constrained together. No free interaction-insertion family is permitted.
3. Fix the UV and switching/IR-removal operations and coefficient extraction,
   including multi-insertion oversubtractions, to produce the actual formal
   OPE/beta/gamma inputs. Prove the necessary perturbative existence and
   equivalence facts; these are not the future massive-YM existence theorem.
4. Establish gauge, basis, regulator and finite-scheme equivalence, the
   source/canonical insertion evaluation and quotient descent, tensor analytic
   boundary relations, and leading stress-symbol/anomaly normalization.
5. Complete multi-cluster/contact OPE and source-fidelity arguments for the
   selected weak topology, graph-core stress presentation and homogeneous RG
   sectors. Finish the outstanding cited-Wightman kernel/spectral equivalences.

The implemented source/canonical map keeps `F_source=g F_canonical` and all [covariant derivative](GLOSSARY.md#gauge-fields-and-observables) factors. Two
beta coefficients are computed from the actual structure constants as normalization
checks; those two terms do not supply all-order renormalized predictions. The full
formal input family must be an output of items 1–3, rather than a theorem/proof
parameter.

## Sources and admission boundary

Jaffe–Witten §4 p6 remains normative. The cited textbook's relevant RG, mixing and
weak-OPE equations were inspected. Additional primary mathematical presentations
[Fröb–Holland](https://arxiv.org/abs/1603.08012) and [Fröb–Holland–Hollands](https://arxiv.org/abs/1511.09425) give precise flow, normalization, coefficient extraction and
quantum gauge identities. They guide an explicit presentation; their choice does not add
a universal construction method to the source theorem. Exact equations and
qualifications are recorded in [PERTURBATIVE_PRESCRIPTION.md](PERTURBATIVE_PRESCRIPTION.md).

For implementation details see [PERTURBATIVE_IMPLEMENTATION.md](PERTURBATIVE_IMPLEMENTATION.md) and [COMPOSITE_STRESS_REVIEW.md](COMPOSITE_STRESS_REVIEW.md). The independent findings and
integration dispositions are in [CENTRAL_ADVERSARIAL_REVIEW.md](CENTRAL_ADVERSARIAL_REVIEW.md).

Full exact-target admission stays closed. `--claim specification` reports `SPECIFICATION_INCOMPLETE` independently of
proof submission; kernel checking, semantic review and external/CMI acceptance remain
separate. Neither the new central relations, the build nor agent agreement completes the
missing fixed prescription or establishes [source fidelity](GLOSSARY.md#reading-a-formalization).

## Integration validation

`python3 scripts/check_proofs.py` completed with exit 0 in the requested repository under pinned Lean 4.25.0.
The 2750-job default build and transitive axiom audits passed, including the actual bare
composite generator and coupled central relation. All 21 verifier unit tests, 15
proof-audit regressions and both separate kernel-inspector adversarial rejections
passed. No new axioms, `sorry`, opaque placeholders or existence assumptions were
introduced.

These checks validate the implemented definitions, supporting proofs and admission
boundaries. They do not resolve the missing fixed renormalized prediction prescription
or prove semantic sufficiency. Full admission stays closed; missing existence proofs are
not the reason for that status.
