# Central implementation adversarial review (2026-10-20)

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review follows concrete failure cases through several implementation revisions. A
useful example is the [stress tensor](GLOSSARY.md#scales-and-renormalization): mapping an exactly traceless classical polynomial
linearly into quantum fields would force its quantum trace to vanish too.

Read C1–C5 for the initial mechanisms, then the integration findings and final repair
audit. A finding marked repaired is a local repair, not a claim that the whole theory
has been constructed.

For terminology, start with the [relevant glossary section](GLOSSARY.md#reading-a-formalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This review concerns the new central definitions, not proof existence or peripheral
audit infrastructure. It reads `source-design.md`, the fixed interaction/cutoff/Taylor modules,
composite correspondence and stress modules, and the evolving root [OPE](GLOSSARY.md#short-distance-products-and-contact-terms)
implementation. It does not identify a green build with fidelity. At this stage exact
full-target admission remains unjustified.

## Findings sent to implementers

### C1 — Exact classical stress identification forces a quantum trace identity (blocking)

Initial `StressTensorData.Compatible.classical_label` identifies every stress component exactly with the four-dimensional
classical Yang–Mills stress polynomial on every smooth connection. `RenormalizedCompositeMap.Compatible.relations` preserves
every such classical identity, and the map is real linear. But the classical tensor is
identically traceless in dimension four. Therefore the sum of metric-weighted diagonal
labels is equal on connections to zero, so the same sum of quantum fields is zero by
`relations` and linearity.

The docstring's omission of a `trace_zero` field does not prevent this derived condition.
It would exclude the quantum [trace anomaly](GLOSSARY.md#scales-and-renormalization).

Required repair: distinguish classical leading symbols/perturbative zeroth order from
exact quantum stress, allowing fixed quantum mixing with the metric [curvature](GLOSSARY.md#gauge-fields-and-observables)-square
operator (and admissible improvements) determined by the same perturbative beta/anomaly
data. Charge normalization must still connect that tensor to Q's translations. Merely
adding an arbitrary correction tensor would reintroduce arbitrary Yang–Mills meaning;
the perturbative constraints on it must be fixed.

### C2 — Spatial translation versus contravariant stress sign (blocking component error)

`TranslationGenerators.action` uses `+i operator_mu` as the derivative for the coordinate translation `a=t e_mu`.
Existing [Wightman](GLOSSARY.md#quantum-fields-and-distributions) conventions are `U(a)=exp(i P·a)` with (+---) Minkowski pairing. Thus
spatial `operator_i` is covariant momentum `P_i=-P^i`. The stress is defined
contravariantly, so its integrated `T^{0i}` yields `P^i`. The initial `charge_limit`
sets these equal without the required metric sign. Time normalization is unaffected.

Required repair: insert `metricSign mu` in the stress charge or use explicitly contravariant
translation generators with derivative `i metricSign mu operator_mu`. Derive the convention consistently
from the same [unitary](GLOSSARY.md#operators-and-spectrum) translation representation.

### C3 — Mixing matrix conventions must be transported consistently (integration risk)

The composite module initially states `new_i=sum_j M_ij old_j`, taking the row-i/column-j entry of the
linear equivalence. The source design instead uses a map on labels, `Q_new(v)=Q_old(M v)`, whose
image of basis label i has coefficients `M_ji`. Both are valid conventions
separately, but using the same Lean object in the root map-on-label OPE formula without
a transpose reverses the intended action. The [filtration](GLOSSARY.md#gauge-fields-and-observables) inequality must track the
chosen convention as well.

Required repair: unify conventions or prove an explicit transpose bridge before applying
incoming/outgoing OPE transport and [RG](GLOSSARY.md#scales-and-renormalization) matrix formulas.

### C4 — Composite map need not exhaust Q's local observable algebra (central gap)

C maps classical labels into finite combinations of Q.field, but Q's [cyclicity](GLOSSARY.md#quantum-fields-and-distributions) concerns
all Q.field labels. It does not imply cyclicity of C's image. Thus one could try to
attach unused extra fields/sectors outside the matched composite family. Stress charges
reproducing the full Q dynamics constrain this attack but are not an identification of
the local observable algebra.

Required repair: impose/prove density of words in the renormalized gauge-observable
fields in the physical vacuum [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions), or an equally explicit generation condition.
Justify it as the physical vacuum representation of the complete [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) observable
family, rather than as an ad hoc interaction test. A common [carrier](GLOSSARY.md#operators-and-spectrum) for different G
remains permissible.

### C5 — Fixed kernels and one primitive subtraction are not fixed all-order predictions (known blocking gap)

The new bare [vertices](GLOSSARY.md#perturbative-calculations) use the actual G bracket and invariant form, with concrete
density expansions; the cutoff covariance includes its p=0 continuation; Taylor
subtraction is an actual derivative operation; the integrated primitive bubble requires
integrability. These are substantial central definitions, and their current caveats are
appropriate.

They still do not define all graded contractions, full [renormalization](GLOSSARY.md#scales-and-renormalization) flow with boundary
conditions, multi-insertion oversubtractions, coefficient extraction, quantum Ward/BRST
identities or the [UV](GLOSSARY.md#scales-and-renormalization) limit. A two-loop [beta](GLOSSARY.md#scales-and-renormalization) polynomial is a fixed
necessary check, not all-order prediction semantics. Equal infrared/ultraviolet cutoffs
give zero kernels; a final definition cannot replace cutoff removal by existential
selection of one admissible cutoff pair. Individual [BPHZ](GLOSSARY.md#short-distance-products-and-contact-terms) graph subtraction cannot
be called a sufficient gauge-preserving scheme without
counterterm/Ward/scheme-equivalence work.

## Source-design fidelity boundary

The design now uses concrete primary formulas and explicitly acknowledges that the
perturbative reference proves orderwise perturbative statements, not the proposed
nonperturbative all-order matching and weak OPE claims. A complete target needs the
promised sufficiency argument for its exact topology, finite truncation convention, RG
transport and admissible schemes. A universal preferred construction must not be
silently imposed. This is definition/equivalence work, not a request to prove Yang–Mills
existence.

Root weak OPE/RG code was not yet present at the first review snapshot. It must be
reviewed when available for arbitrary coefficient witnesses, correct
relative-configuration scaling and [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) domains, engineering and RG matrix
orientation, all-order fixed-series matching, and possible trivial renormalization maps.
No full gate unlock is justified by the fragments alone.

## Update after first repair pass

The [QFT](GLOSSARY.md#quantum-fields-and-distributions) owner removed exact `classical_label` from stress compatibility, eliminating the
forced quantum-tracelessness mechanism C1. This leaves, explicitly, the required
leading-classical-symbol and fixed beta/anomaly identification unfinished. Spatial
charges now include `metricSign mu`, resolving C2 at the convention level. Composite
compatibility now includes cyclicity of words in C's own fields, resolving C4's
missing-generation condition.

Additional C6 (sent to owner): `FiniteMixing` supplied degrees initially only bound actual
polynomial weights from above. Inflating all bounds to the same value makes its
filtration condition vacuous even for labels with different actual engineering
dimensions. Derive the exact weighted degree/minimal bound, or explicitly treat this as
a coarse chosen filtration and do not equate it with the prescribed engineering
filtration. Dimensionful mu powers and any label/component transpose must be consistent
with that degree convention.

Additional normalization integration issue: old `Connection.euclideanAction` uses a sum over mu<nu with
factor 1/(4g^2), while new canonical `yangMillsDensity` uses all ordered tensor components with
factor 1/4. After canonical field rescaling, the same B/g gives a factor-two
discrepancy. A B/coupling convention can absorb it, but the promised same-action bridge
must make that rescaling explicit rather than silently identify them.

## Actual pair-OPE implementation review

Reviewed root [OperatorProductExpansion.lean](../YangMills/OperatorProductExpansion.lean). The pair-product kernel is a continuous [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) functional
constrained on the dense span of pointwise elementary [tensor tests](GLOSSARY.md#quantum-fields-and-distributions) to equal actual
products of C's fields. This prevents hidden arbitrary kernel components. The
relative-only scaling in `(r,z)=(x-y,y)` and normalized `lambda^-4 f(r/lambda)` are coherent: the
[cluster](GLOSSARY.md#short-distance-products-and-contact-terms) center remains [smeared](GLOSSARY.md#quantum-fields-and-distributions) and the subtraction is the coefficient distribution
evaluated on the normalized relative test times the actual output-field matrix element
on the center test.

Positive spectator separation and compact [off-diagonal](GLOSSARY.md#short-distance-products-and-contact-terms) relative support avoid additional
spectator coincidences at sufficiently small scale. Intrinsic quotient degree closes
upper-bound inflation for the OPE exponents. The file correctly calls itself a pair-OPE
fragment and does not assert a complete coefficient generator.

Additional findings:

**C7 — Derivative descendants lack an actual derivative link.** C currently need not
identify the fixed total-derivative [jet](GLOSSARY.md#graded-gauge-symmetry) polynomial with the distributional
derivative of the corresponding quantum composite. Define the appropriate jet derivation
and require `C(derivative_mu p)(f)=-C(p)(partial_mu f)`, or provide the justified contact/scheme-qualified relation.
Without it, derivative labels in the OPE truncation can represent unrelated fields. This
is renormalized correspondence semantics, not a demand to construct the theory.

**C8 — Euclidean-to-Minkowski coefficient bridge is missing.** The flow covariance and
fixed kernels are Euclidean; the actual root OPE uses Minkowski Wightman fields on the
same coordinate type. Matching to fixed perturbative distributions requires a fixed
[analytic](GLOSSARY.md#analysis-and-asymptotics)-continuation/boundary-value prescription, or actual same-Q Schwinger
functions and their reconstruction/continuation bridge. Coordinate type equality is not
this mathematical bridge.

**C9 — Truncation/basis consistency.** `Truncation` permits duplicate or dependent labels,
which is harmless for a single relation but changes the numerical coefficient sum. An
assembled all-degree expansion needs a consistent basis/dual coefficient extraction or
explicit reparametrization law. It must not quantify over every arbitrary spanning
truncation with one unchanged coefficient family, nor independently choose truncations
to absorb normalization errors. The fixed generator's coefficient-extraction scheme must
supply this consistency.

## RG implementation review

Reviewed root [RenormalizationGroup.lean](../YangMills/RenormalizationGroup.lean). For the stated map-on-label convention, `strippedPairing` correctly
implements outgoing R and two incoming inverse-R factors. Its engineering power is input
degree sum minus output degree, and normalized distributional dilation has the correct
relative-coordinate normalization. The all-order comparison uses the last retained
running-coupling power rather than merely o(1). The t=log(1/lambda), g'=beta(g),
R'=[gamma](GLOSSARY.md#scales-and-renormalization)(g)R convention is consistent with `Q_base(v)=Q_run(R v)` and `Q_run'=-Q_run gamma`. The file
explicitly treats the series as a parameter to be supplied by an unfinished fixed
generator; it does not claim this parameter is already prescribed YM data.

**C10 — Actual scale-family transport still needs a bridge.** Frame contains no C and no
operator identity `C_base(v)=C_run(R_t v)`. Hence the current ODE/matching structure defines a
numerical normalization relation for coefficients, not yet the asserted RG transport of
the same composite operator family. A final assembled specification must provide this
actual-field identity or justify why an equivalent fixed-base presentation suffices.

**C11 — Finite sectors must exhaust the observable family.** A single arbitrary finite
Frame may be empty or identity-only. Full agreement cannot be reduced to existence of
such a frame. The assembly needs a compatible exhaustive family of prescribed finite
sectors, covering every required input/output observable and truncation, with the fixed
engine supplying consistent coefficient restrictions.

Regularity wording: beta/gamma are described as smooth completions, while their
structures impose perturbative jets and derivative ODEs along the running trajectory,
not global smoothness as functions of g. Either encode intended smoothness or describe
exactly the weaker regularity actually required. No error in the stated finite jet/ODE
formula itself was identified.

C6 was repaired in the latest CompositeFields version by deriving
intrinsicEngineeringDimension from the minimum quotient-filtration bound. The row-array
finite-mixing convention remains distinct from RG's label-map convention; an explicit
interface/transpose is still needed if they are composed.

## Final integrated snapshot findings

The revised pair OPE now has one classically independent filtered basis with finite
active sets and coherent all-D subtraction. This repairs C9's arbitrary spanning-list
multiplicities. Local finite-order bounds on each compact support replace global
[tempered](GLOSSARY.md#quantum-fields-and-distributions)-growth conditions on coefficient distributions; the latter would have been an
unjustified restriction for finite-[IR](GLOSSARY.md#scales-and-renormalization) Euclidean continuation. Only compact tests
are observed, so auxiliary algebraic extension to the Schwartz vector space does not
impose a global distribution growth condition.

Actual-field scale transport (`Realizes`) and exhaustive active-basis frames repair the
respective missing structures of C10/C11, subject to the common-running finding below.
`StressMatched` now binds the same tensor/form/coupling/scale to a running beta completion.

**C12 — Exhaustive sectors initially have different running couplings (integration
error).** `ExhaustiveMatching.frame D` initially contains its own RunningCoupling for each D. Common beta
jets and coherent R entries do not make beta completions, initial g, or g(t) equal. In
particular gamma-zero sectors have R=id for any g trajectory. Thus one physical theory
can be compared using a different RG integration constant in each finite sector, while
stress is tied to only one frame.

Require one common RunningCoupling (or explicit beta/coupling equalities) for all frames
and bind the tensor to this common object. Coherence of exact gamma entries should
likewise follow from or be supplied with the common running/transport convention.

**C13 — [Wick rotation](GLOSSARY.md#analysis-and-asymptotics) of tensor labels is absent from initial componentwise bridge
(integration error).** The new LowerTube [holomorphy](GLOSSARY.md#analysis-and-asymptotics), Euclidean restriction, explicit
integrability and compact weak Minkowski boundary limits are a substantive coordinate
continuation relation. But the observable basis includes tensor curvature and derivative
components. Rotating time also rotates those operator labels (time components carry
fixed i factors; contracted tensor labels can mix), with incoming and outgoing OPE-label
transformations.

`CoupledContinuumOPE` initially applies AnalyticContinuation separately to identically named
Euclidean/physical basis components, with no such label map. This is insufficient for
the full tensor observable algebra. Supply the fixed complexified Wick map for the same
classical jets/labels and transport coefficient slots, or define the Euclidean
comparison family to include that explicit transformation before invoking the scalar
boundary relation. No arbitrary freely selected label map is acceptable.

The Euclidean covariance still must not be naively identified with a physical Wightman
covariance; local [holomorphic](GLOSSARY.md#analysis-and-asymptotics) continuation allows exponential timelike growth without
pretending it is globally tempered. Contact extensions and many-cluster compatibility
remain expressly unfinished.

## Expanded bare perturbative engine review

Reviewed all-order fixed finite-cutoff Wick coefficients and classical insertion
substitution. By inspection: nonzero elementary covariance pairs have equal parity, so
the first-leg [Koszul](GLOSSARY.md#graded-gauge-symmetry) crossing sign is coherent; oriented [ghost](GLOSSARY.md#graded-gauge-symmetry) covariance
agrees with exp(-cbar K c) convention; cubic/quartic color monomial factors match the
written density; interaction expansion uses (-1)^n/n!; normalized coefficients perform
triangular vacuum-series division; the fixed insertion map retains F_source=g
F_canonical and D_source=partial+g[A_canonical,.]. This is not yet a checked proof of
monomial/action or insertion/connection equivalence, which the implementation accurately
lists as supporting work.

**C14 — [Switching](GLOSSARY.md#perturbative-calculations) removal must be fixed.** The arbitrary real Schwartz switching
function may be identically zero, killing every interacting [vertex](GLOSSARY.md#perturbative-calculations) while preserving
the nonzero classical action definitions. This is a legitimate finite-switching bare
helper, not a complete prescription for physical predictions. A final prescription needs
a fixed local switching/adiabatic removal and translation-invariance bridge, rather than
existentially choosing a switching function. The reviewer sent this explicitly to the YM
owner for the remaining-work document.

## Final repair audit and disposition

Reviewed the latest exact [OperatorProductExpansion.lean](../YangMills/OperatorProductExpansion.lean), [RenormalizationGroup.lean](../YangMills/RenormalizationGroup.lean), and [WickRotation.lean](../YangMills/WickRotation.lean) repairs.

- **C12 repaired structurally:** `ExhaustiveMatching.running` is one shared object; `common_running` equates every sector's complete beta/initial-coupling/trajectory data with it. `common_gamma` likewise equates exact gamma entries on overlaps. `FamilyStressMatched` uses this shared running system. Coherent transport now belongs to the same physical running family.
- **C13 repaired structurally:** `jetFactor` supplies (-i) for every covariant time index of F and each [covariant derivative](GLOSSARY.md#gauge-fields-and-observables). `observableValue` is the actual complexified polynomial substitution. `LabelRotation.meaning` fixes W from that substitution on actual connection evaluations, rather than leaving a free label convention. The outgoing W/two incoming inverse-W slots in `rotatePairing` are consistent with `Q_E(v)=Q_M(Wv)`. `FamilyContinuation` uses a single global coordinate-boundary family and these fixed sector label rotations. No new sign/slot error was found. Uniqueness/coherence of W can be proved from classical basis independence; it is supporting equivalence work, not permission for arbitrary matrices.
- **C7 repaired structurally:** the latest composite module defines descendants by actual connection derivatives and imposes the quantum distributional derivative relation. Its [Poincare](GLOSSARY.md#quantum-fields-and-distributions) pullback/covariance condition also ties the same labels to the actual affine one-form transformation.

Latest dispositions: C1, C2, C4, C6, C7, C9, C10, C11, C12 and C13 have concrete
repairs. C3's row-array versus label-map conventions are explicitly distinct; an
interface is still required if the finite-mixing structure is later composed with
label-map RG transformations. C8 now has explicit coordinate and tensor-label
continuation relations, rather than a coordinate-type identification; applicability to
the eventual fixed renormalized coefficients still needs the declared analytic/fidelity
work.

C5 (fixed full renormalized generator/Ward/extraction) and C14 (switching/adiabatic
prescription) remain unfinished. The normalization bridge is now exposed by exact
action-density comparison rather than silently ignored.

This audit found no further mathematical sign, scaling, or same-data defect in the
latest C12/C13 repairs. It does not prove the outstanding equivalence lemmas, the
all-cluster/contact prescription, or semantic sufficiency of the assembled presentation.
It does not authorize exact full-target admission.
