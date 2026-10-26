# Independent prediction-link review

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review checks how scale derivatives and [operator mixing](GLOSSARY.md#scales-and-renormalization) feed into short-distance vacuum
correlations. A numerical mixing table is insufficient unless it transports the actual
composite fields used in those correlations.

Read the findings before the all-scale assembly update. The later review distinguishes
requiring simultaneous equations from constructing a restoration procedure that supplies
their witnesses.

For terminology, start with the [relevant glossary section](GLOSSARY.md#scales-and-renormalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

Reviewed current primary AmputatedLegendre, CohomologicalScaleInsertion,
FiniteWardRestoration, CACSchemeTransport, GeneratedScaleNormalization and
InvariantBasisCoordinates, plus physicalbridge VacuumWordContinuation and
GeneratedVacuumWordMatching. Owner files were not edited. This is inspection of
definitions and consistency, not an existence result or full-target admission.

## Findings

No new blocking contradiction was found in this stage by inspection. The following
statements distinguish checked structure from remaining fidelity obligations.

1. The [Legendre](GLOSSARY.md#perturbative-calculations) construction uses the actual fixed covariance and flow jets. Nonempty labelled blocks, internal block order, the [Koszul](GLOSSARY.md#graded-gauge-symmetry) regrouping sign and 1/k! implement the expected graded [Faà di Bruno](GLOSSARY.md#perturbative-calculations) combinatorics. The independent coupling and loop allocations have exact [Cauchy](GLOSSARY.md#perturbative-calculations) totals. With the explicitly required vanishing of the interaction at g=0, the unknown equal-coupling-order outer term is the identity contribution and all recursively subtracted terms have lower coupling order. Constant mean-field components are explicitly excluded. The full functional-equivalence proof, especially the general graded chain rule, remains to be supplied; a scalar cubic check alone does not supply it.

2. Background gradient contractions preserve momentum conservation on balanced tuples; the inserted directional transform retains independent insertion momenta. The quadratic subtraction uses the right/left conversion for the even action before external differentiation. Basic [ghost](GLOSSARY.md#graded-gauge-symmetry) covariance has opposite entries in the two orientations. I found no sign/factorial error in these formulas by inspection; the general algebraic identities remain proof obligations.

3. The scale insertion differentiates the full computed free-plus-interaction [Gamma](GLOSSARY.md#scales-and-renormalization), with smoothness on positive subtraction scales. The composite [dictionary](GLOSSARY.md#notation-and-source-abbreviations) is differentiated too. Residual equations retain field/source inverse-dual weights and actual generated-Q primitives through the same insertion engine. They require coefficientwise compact weak [UV](GLOSSARY.md#scales-and-renormalization) removal followed by [IR](GLOSSARY.md#scales-and-renormalization) removal, not exact finite-cutoff [Ward](GLOSSARY.md#graded-gauge-symmetry) closure and not only finitely many projector equations. The source classification, uniqueness and [gauge-fixing](GLOSSARY.md#graded-gauge-symmetry) authorization of these equations remain substantial supporting mathematical work.

4. The finite Ward correction now permits relevant as well as [marginal](GLOSSARY.md#scales-and-renormalization) local terms, with explicit engineering compensation and actual group/O(4) invariance. After a relevant shift, the filtered normalization is imposed at the positive subtraction scale rather than retaining the incompatible relevant-IR-zero normalization. A restoration step specifies the fixed bare defect and actual UV shift; its claimed cancellation is not silently built into an unrelated after-anomaly. The tower fixes lower-loop prefixes. Proving restoration from the primitive identity and flow estimates remains required.

5. The [CAC](GLOSSARY.md#perturbative-calculations) scheme expressions restore/subtract the free quadratic before field pullback, distinguish local and [regulator](GLOSSARY.md#scales-and-renormalization)-weighted free actions, retain the computed [antifield](GLOSSARY.md#graded-gauge-symmetry)-only normalization I, and use source-dual factors in connected W. Endpoint transport is required after ordered limits; a field redefinition is not incorrectly asserted to commute with a fixed finite IR covariance. The coupling change has an explicit factor g, so a finite g-truncation through the desired order does not miss higher powers pulled down by a nonzero constant coupling shift.

6. Classical mixing coordinates are fixed by equality on every smooth connection and uniqueness in the actual independent filtered basis. No quantum injectivity or physical-[cohomology](GLOSSARY.md#graded-gauge-symmetry) isomorphism is inferred. [Beta](GLOSSARY.md#scales-and-renormalization) and gamma loop assembly is finite at fixed coupling order by the explicit graph bounds. Wick conjugation has the checked column convention W gamma_E W^-1.

## Assembly issue that must stay explicit

CompositeMixing permits dimensionful, subtraction-scale-dependent lower-dimensional
mixing. The physical [RG](GLOSSARY.md#scales-and-renormalization).Frame currently uses equal-degree blocks and gamma
depending only on running g. Comparing the generated gamma table at the reference scale
does not alone establish the correct scale evolution of a general raw mu-dependent
scheme. One needs a homogeneous engineering-rescaled/vacuum-subtracted representative and
a source-equivalence/normalization-freedom argument, or a more general scale-dependent
transport definition. The frame and word-bridge documentation acknowledge this
limitation; it must remain a required link in any proposed closed sector.

This review does not classify the homogeneous presentation as already equivalent to
every admissible scheme.

The owner has agreed to require equality to the same Wick-conjugated generated gamma at
every positive normalization scale in the new full-sector assembly. If implemented as
stated, that removes the single-reference-scale gap as an explicit homogeneous-family
condition; it does not prove availability or source equivalence of that choice. This
proposed assembly field was not part of the file snapshot inspected above.

The [CS](GLOSSARY.md#scales-and-renormalization) decomposition also does not by itself prove uniqueness of beta or mixing
modulo exact/EOM directions. Classical basis-coordinate uniqueness resolves redundant
classical polynomial presentations, not physical [BRST](GLOSSARY.md#graded-gauge-symmetry)-null directions. The
appropriate [cohomological](GLOSSARY.md#graded-gauge-symmetry) classification/normalization result remains necessary before
claiming a uniquely prescribed physical prediction.

## Physical vacuum-word bridge

The continuation's distributional boundary is the same actual C operator word on the
same invariant domain and vacuum, proved on [tensor tests](GLOSSARY.md#quantum-fields-and-distributions). There is no independent physical
correlator in this bridge. Absolute complex translations preserve the [tube](GLOSSARY.md#analysis-and-asymptotics);
Euclidean and boundary time ordering agree with the lower-tube convention. The
shrinking-coordinate observation carries no extra inverse volume factor, since its
definition already integrates in the rescaled variable.

Incoming labels are Wick transformed and inverse transported, and each transformed
component has its own intrinsic canonical dimension factor. No outgoing factor belongs
in a vacuum word. The generated right-hand series comes from the same corrected
invariant-word data, with no elementary gauge/ghost external legs. Each finite-order
asymptotic remainder is tested on separated, strictly Euclidean-ordered compact
supports. Matching is asymptotic to every running-coupling order and permits flat
corrections; it does not equate a perturbative series with a nonperturbative vector or
require [analytic](GLOSSARY.md#analysis-and-asymptotics) resummation.

The quotient statement proved here concerns equality of UV germs, which is the
appropriate limited consequence of these hypotheses.

The bridge currently omits independent [one-point](GLOSSARY.md#scales-and-renormalization)-condensate matching and explicitly
uses a homogeneous/vacuum-subtracted reference presentation. Its claimed equivalence to
the source's short-distance-correlation requirement still needs the stated normalization
and analytic-continuation supporting theorems. No exact nonperturbative BRST
Hilbert-space quotient follows from the formal quotient statement alone.

## Disposition

The new definitions substantially connect previously separate data, and no fresh
blocking defect was found in the inspected equations. A provisional sector may record
these exact obligations, but successful compilation cannot replace the outstanding
source-equivalence, cohomological-classification, homogeneous-scheme and
analytic-continuation fidelity proofs. No existence theorem or full-target admission is
certified.

## Implemented assembly update

`GeneratedRenormalizedSector.generated_gamma_all_scales` now requires the computed mixing equality at every positive subtraction
scale, using exactly its coefficient/word Wick rotations and common exhaustive matching
frames. The full [predicate](GLOSSARY.md#reading-a-formalization) remains provisional. The filtered Ward-restoration/scheme
transport adequacy, cohomological classification/uniqueness, and analytic continuation
implications remain supporting obligations. No full target or nonperturbative existence
proof is admitted by this assembly.

## Independent generated-sector assembly review

Inspected the primary staged GeneratedRenormalizedSector.lean,
GeneratedScaleNormalization.lean, InvariantBasisCoordinates.lean,
LocalWardFlowFamily.lean, LocalWardOPEStressBinding.lean and their concrete
matching/continuation dependencies. This is a review of mathematical meaning and object
identity. No owner modules were edited, and no existence theorem or exact-target
admission is certified.

## All-positive-scale gamma link: implemented

GeneratedRenormalizedSector.generated_gamma_all_scales quantifies over every positive
RenormalizationScale, every finite sector and every coefficient order. It identifies the
physical gammaSeries with the same normalization.euclideanGammaSeries, resolved in the
same classical basis and conjugated by sector.rotation D. It is not restricted to the
reference scale. That implements the previously requested missing all-scale
compatibility condition.

The same rotation is passed to coefficient_continuation and actual_word_matching. There
is one matching [witness](GLOSSARY.md#reading-a-formalization), whose frames use normalization.betaSeries and
sector.gammaSeries; both coefficient matching and actual vacuum-word matching use those
frames. The same matching witness determines the stress sector, its basis dictionary,
same [running coupling](GLOSSARY.md#scales-and-renormalization) and stress RG equation. The physical [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) kernels and vacuum
continuation use the same C. The coefficient continuation takes generated.data at the
same S.referenceScale, and this generated family is already bound to the same
LocalWardFlowFamily and fixed S.

I found no replacement matching/frame/rotation/engine hidden in this assembly.

This all-scale equality is a concrete restriction selecting a compatible homogeneous
reference presentation. It is not a proof that arbitrary dimensionful raw subtraction
prescriptions satisfy it. The source-adequacy theorem for choosing this presentation,
including treatment of identity/lower-degree mixing and vacuum subtraction, remains
required.

## Fixed massless prescription versus finite Ward restoration

The final S still satisfies the original CoefficientFlowConditions, with marginal-only
finite scheme data and relevant IR-zero normalization. FilteredCoefficientFlowConditions
and RestorationTower now define a broader prescription permitting finite relevant terms
normalized at mu. The latter are not required by GeneratedRenormalizedSector, nor is the
final S identified with their restored diagonal. Likewise importing CACSchemeTransport
does not instantiate its concrete endpoint comparison for this final family.

There are two different logically legitimate routes, with different unfinished work:

* Direct simultaneous prescription: require a massless homogeneous S and all full Ward/CS/continuation conditions simultaneously, as the current sector does. This has a concrete meaning, and no contradiction from these conditions has been established. The unfinished issue is a supporting normalization/source-equivalence theorem: show this particular prescription does not exclude source-admissible Yang--Mills realizations. Its absence cannot be dismissed as merely the missing Yang--Mills existence proof.
* Restoration construction: use the filtered finite Ward tower to justify the final selected prescription. This route currently lacks an actual final-family binding/transport condition. One must identify final S with the restored diagonal, or explicitly compare the restored family and final S through the same endpoint scheme change, carrying insertions, generated Ward map, observable lift and CS data as well as the background. A separate unused tower and unused transport definition do not supply this relation. Broadening S to the filtered normalization and binding that same S everywhere is another concrete option.

It would be incorrect to call the current massless-scheme conjunction proved
inconsistent merely because the available finite-restoration construction uses relevant
intermediate terms. It would also be incorrect to cite those intermediate constructions
as establishing the current final prescription without the missing relation or
equivalence theorem.

## Definition gaps versus supporting obligations

For the narrow simultaneous generated sector, the reviewed core quantities have concrete
definitions: regulated flow and UV data; full Ward/anomaly transport; local partition
extension through the same lower hierarchy; generated cohomological dictionaries and
output recovery; actual coefficient limits; all-[arity](GLOSSARY.md#perturbative-calculations) weak OPE; fixed Wick
substitution; actual C-word UV germs; full Gamma scale insertion; finite beta/gamma loop
assembly; generated stress and same physical translations. The sector does not contain a
freely chosen predicate standing for one of these meanings.

No further omitted central quantity was identified in this exact assembly review.

Actual missing final-assembly predicates are: (a) the optional restoration-to-final-S
bridge if that is the selected fidelity route, as detailed above; (b) a closed
proposition quantifying the required groups and witnesses and conjoining this sector
with the chosen complete [QFT](GLOSSARY.md#quantum-fields-and-distributions) axioms, positive finite gap for its actual
[Hamiltonian](GLOSSARY.md#operators-and-spectrum), and the intended nontriviality condition. GeneratedRenormalizedSector is
explicitly only a fragment and supplies none of that outer quantification by itself.

Those outer properties already have separate concrete definitions; their absence here is
an assembly gap, not a need to redefine them.

Substantial unfinished supporting work remains: equivalence to the cited
QFT/analytic-continuation standards; local density/functional [BV](GLOSSARY.md#graded-gauge-symmetry) and graded
Legendre identities; extraction duality and flow normalization uniqueness; source/forest
equivalence and finite normalization freedom of local contact extensions;
Ward/cohomological classification authorizing beta/gamma and their physical quotient
ambiguities; sufficiency/availability of the chosen homogeneous vacuum-subtracted
reference scheme; and equivalence of the chosen testwise UV/OPE formulation to the
source's delegated statements. These are task obligations even when their component
predicates are fully concrete.

They are distinct from proving that any Yang--Mills model exists.

Auxiliary Euclidean OPE distributions are recovered off the insertion diagonals and have
[power-counting](GLOSSARY.md#scales-and-renormalization) bounds. Their contact representatives need not be uniquely fixed merely by
this recovery. This is not automatically a physical loophole: the required OPE and
all-order matching are themselves tested away from insertion diagonals, and the physical
continuation is tied by its analytic boundary. A stronger universal prescription for
these auxiliary coefficient contact values should not be added without showing the
source requires it.

The full continuum insertion/contact W hierarchy already has the separate same-engine
partition-local extension condition.

## Disposition

The all-scale gamma/Wick repair is present and uses the same objects. No new blocking
contradiction was found in the current simultaneous sector. This does not close the
source-fidelity argument, prove universality of its fixed prescription, or justify
full-target admission. The precise massless-normalization fork above must be resolved
explicitly before claiming a faithful complete specification.

## Closed proposed outer assembly

`GeneratedCandidate` now collects one actual-group engine, complete gapped QFT, composite map,
generated normalization, physical OPE/word matching and stress sector. `ProposedGeneratedSpecification`
universally quantifies the required compact simple Lie gauge groups in the group
[carrier](GLOSSARY.md#operators-and-spectrum) universe. It is a closed proposed statement, not admitted as the completed
source-faithful target. The same stress is proved nonzero from its actual charges and
physical gap. The remaining fixed-presentation/source-adequacy and framework fidelity
work continues to block exact full admission, independently of existence proofs.
