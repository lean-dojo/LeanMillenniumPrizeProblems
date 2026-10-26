# Same-action identities and physical mixing: proof boundaries

> **Source-access update, 22 October 2026.** The book-access limitation recorded
> below describes this historical review. Chapter 3 of the supplied 2000 reissue
> has since been [read and compared](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026).
> That comparison records remaining obligations; it does not validate all earlier conclusions.

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This report collects proof boundaries for the action-derived symmetry formulas,
[Legendre](GLOSSARY.md#perturbative-calculations) inversion and the assembled candidate. Its later sections update earlier
partial results, so the document should be read as a sequence of checkpoints.

Start with the free action and coordinate identities, then the insertion inverse. The
assembly review explains how those algebraic results must connect to the physical theory
and cited framework.

For terminology, start with the [relevant glossary section](GLOSSARY.md#graded-gauge-symmetry); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

These are supporting proofs for the central fixed prescription, not a proof of
Yang--Mills existence. No exact full-target admission is enabled.

## Same-action master identity stage

All three new modules strictly compile with `-DwarningAsError=true`; no axioms, `sorry`,
master-equation assumptions, or separately supplied [BRST](GLOSSARY.md#graded-gauge-symmetry) images.

Dependency order:
1. FullBVMasterQuadratic imports frozen FullBVLocalST.
2. FullBVFreeCoordinates imports FullBVMasterQuadratic.
3. FullBVMasterEquations imports FullBVFreeCoordinates.

MasterQuadratic proves actual total derivatives of [jet](GLOSSARY.md#graded-gauge-symmetry) generators; the exact left
Euler formula for quadratic words; the actual right/left parity relation; and equality
of the fixed `freeActionDensity` to its expanded quadratic sum.

FreeCoordinates proves all eight `stCharacteristic (freeActionDensity G)` images, including every [antifield](GLOSSARY.md#graded-gauge-symmetry). In
source conventions these are:

- s A_mu = partial_mu c; s c = 0;
- s barc = div A + i B; s B = i Delta c;
- s A_mu^dagger = -Delta A_mu + partial_mu barc^dagger;
- s c^dagger = -Delta barc - div A^dagger + i Delta B^dagger;
- s barc^dagger = Delta c;
- s B^dagger = B - i barc^dagger.

These follow from the same frozen `freeActionVertices` used by the actual flow's Hessian. They
match [FHH](GLOSSARY.md#notation-and-source-abbreviations) 1511.09425 equations (45)--(49), (56)--(57), with the shifted B and
real [ghost](GLOSSARY.md#graded-gauge-symmetry) phase convention recorded in FullBV.

MasterEquations proves `freeLocalST_square_jet` for every basic and antifield jet, with arbitrary
multiindex. This includes the shifted [antighost](GLOSSARY.md#graded-gauge-symmetry) cancellation i*i Delta c + Delta c = 0,
the antifield cancellations, and commuting double finite derivative sums. `localSTLinear`,
`localST_sum`, `totalDerivativesLinear` and `totalDerivatives_sum` are actual linear maps of the existing operations.

Remaining substantive gaps (NOT asserted as hypotheses or theorems):

- Full interacting [master action](GLOSSARY.md#graded-gauge-symmetry)'s characteristic equals all nonlinear gauge
  BRST/antifield equations, using actual [structure constants](GLOSSARY.md#gauge-fields-and-observables) and Jacobi.
- Full graded derivation / derivative commutation theorem promoting the proven
  free generator [nilpotency](GLOSSARY.md#graded-gauge-symmetry) to the whole [superjet](GLOSSARY.md#graded-gauge-symmetry) polynomial algebra.
- Interacting nilpotency on all jets, and consequently all polynomials.
- Equivalence to vanishing integrated [BV](GLOSSARY.md#graded-gauge-symmetry) master bracket modulo divergences;
  the bracket's descent to the local-functional quotient is not proved here.

Thus this stage verifies the full free coordinate sector of the same action; it does not
certify the full classical master equation or authorize that claim.

## Deterministic local-insertion Legendre bridge

[LegendreInsertionBridge.lean](../YangMills/LegendreInsertionBridge.lean) SHA256: `53e9f97cbad9e5757a602f40361058221d3ba1a3e30ce4856394f40d4542b4b1`.

Pinned Lean, warnings-as-errors build passed; the temporary build produced `YangMills/LegendreInsertionBridge.olean`.

The file proves for the actual finite partition operator:

1. Exact split into strictly lower outer coupling order and a diagonal sum.
2. The fixed `insertionGammaCoeff` recursion subtracts exactly the strictly lower contribution of its own coefficients.
3. At a diagonal term, coupling conservation forces every root's coupling order zero. If the actual background coupling-zero jet vanishes, the entire diagonal equals the diagonal for F=0. No positive-coupling interaction coefficient enters that problem.
4. Every strictly lower term for F=0 vanishes: at least one positive-coupling root is forced, and that exact root is zero.
5. Consequently the all-order inverse follows from the FREE identity-root normalization, and any other inverse with that diagonal normalization MUST equal the computed recursion. The uniqueness proof uses strong induction in coupling order; [loop order](GLOSSARY.md#perturbative-calculations) remains independent throughout.
6. `directionalLegendre_of_free_identity` applies this result to the same actual `flowJet A` used by the [CS](GLOSSARY.md#scales-and-renormalization) module, under its actual g=0 vanishing.
7. Exact leading-coupling/tree zero- and one-leg normalization checks.

The remaining free normalization is a precise finite graded combinatorics theorem:
nonzero identity-root blocks must all be singletons; assignments then identify with
permutations; the partition [Koszul](GLOSSARY.md#graded-gauge-symmetry) sign cancels the outer coefficient's graded
permutation sign; k! labelled blocks cancel the actual factorial denominator. The
arbitrary-[arity](GLOSSARY.md#perturbative-calculations) theorem and preservation of graded symmetry by the recursion are
NOT yet proved. The main theorem deliberately exposes this remaining hypothesis and does
not claim that `DirectionalLegendreCompatible` has been discharged universally.

[LegendreInsertionPair.lean](../YangMills/LegendreInsertionPair.lean) SHA256 `175ec0e2c734897bff009fcdb485318e8d79e8967ef23ee7a76402a6a04817a8` (strict compilation passed) separately evaluates the actual
first odd-sensitive case before applying symmetry:

    Compose(A,F)[g0,h0; K,H] = (A[K,H] + (−1)^(pK pH) A[H,K](swapped q))/2.

Under the actual graded swap law for the insertion coefficients, the computed recursion
is thus proved an inverse at that two-leg coefficient. This retains all actual
basic/antifield species and independent external momenta. It confirms the sign and
factorial convention but is not a substitute for the arbitrary-arity theorem.

No frozen CS module was edited; no original or parent staging source was edited. No
sorry, new axiom, or independently chosen [1PI](GLOSSARY.md#perturbative-calculations) insertion was introduced.

## Independent review of GeneratedCandidate

Reviewed the current primary GeneratedCandidate.lean and its QFT/Operator,
QFT/Spacetime, QFT/Wightman, Spectrum, GeneratedRenormalizedSector and composite
consumers. Consulted the existing source/requirements.json crosswalk,
work/source-analysis.md, work/qft-analysis.md and work/central/qft/FIDELITY.md. No owner
files were edited.

## Outer assembly and universes

ProposedGeneratedSpecification explicitly quantifies every CompactSimpleGaugeGroup at
[carrier](GLOSSARY.md#operators-and-spectrum) universe u. The group definition specifies actual connected compact
second-countable real Lie groups with simple tangent Lie algebra; finite centers are
allowed. The connected-group convention and redundant smoothness instance still need
their documented source-fidelity explanation.

Each GeneratedCandidate has precisely one QuantumTheory. Its GappedWightmanTheory
concerns that theory's fields and [Hamiltonian](GLOSSARY.md#operators-and-spectrum). The composite map, [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) kernels,
physical vacuum continuation and [stress tensor](GLOSSARY.md#scales-and-renormalization) all take those same fields as parameters.
The generated sector uses one actual fixed flow system for G, one compatible [Ward](GLOSSARY.md#graded-gauge-symmetry)
family, one basis, one generated coefficient family and one computed CS normalization.
Its existing same-stress relation includes the physical charge/Hamiltonian
compatibility.

The checked stress_nonzero theorem uses that relation and the very same gap hypothesis.

QuantumTheory.State is Type 0 even when G.Carrier is Type u. This is a fixed small
separable-Hilbert presentation, not a separate [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions) chosen at every intermediate
link. It is mathematically reasonable: a separable metric Hilbert space has small
cardinality and may be transported to a small model. A formal
small-model/unitary-transport equivalence is still supporting work if the specification
is advertised as independent of all universe presentations.

The declaration at universe u is a Lean [universe-polymorphic](GLOSSARY.md#reading-a-formalization) proposition schema, not an internal
quantifier over every universe simultaneously. Neither fact supplies a new physical
restriction once the appropriate transport equivalence is established.

## Nontriviality and negative controls

The positive finite mass uses the full [resolvent](GLOSSARY.md#operators-and-spectrum)-defined real spectrum of the actual
time-translation generator. It excludes vacuum-only spectrum without demanding an
isolated eigenvalue or particle state. The outer assembly adds no Gaussianity,
scattering, confinement, string tension or one-particle [predicate](GLOSSARY.md#reading-a-formalization). Nontriviality is not
being identified with the mere existence of a non-vacuum vector: the separate
same-action UV/OPE/observable/stress clauses perform Yang--Mills identification.

The previous unused-group mechanism is structurally blocked: G determines the actual Lie
algebra, [vertices](GLOSSARY.md#perturbative-calculations), fixed covariance/action calculation and generated Ward/extraction
data; their predictions enter the same C's OPE and actual vacuum-word asymptotic
conditions. A disconnected classical action sidecar alone cannot satisfy those required
equality/limit links. Composite-only [cyclicity](GLOSSARY.md#quantum-fields-and-distributions) prevents adjoining an independently
excited Hilbert sector invisible to all C words, and the generated stress charges use
the physical Hamiltonian whose spectrum defines the mass.

These are meaningful structural controls, not a proof that every conceivable
unrelated/free model fails the full proposition. No fully formal negative model theorem
has been supplied. A free massive model satisfies the [QFT](GLOSSARY.md#quantum-fields-and-distributions)-and-gap fragment; to
make it a candidate one would additionally have to satisfy the fixed actual-G all-order
word/OPE, Ward/CS and generated-stress conditions. It cannot pass merely by selecting
arbitrary asymptotic terms. Proving those conditions exclude every unrelated [Gaussian](GLOSSARY.md#perturbative-calculations)
assignment would require nonzero group-dependent coefficient and physical-class
arguments, rather than just reading the type dependencies.

No such theorem is claimed here.

## Exact cited-standard adequacy tasks

The QFT clauses are concrete. The outstanding issue is supporting equivalence/adequacy,
not choosing what an axiom means or proving existence of Yang--Mills.

1. Obtain and audit the actual primary [Wightman](GLOSSARY.md#quantum-fields-and-distributions) axiom text in Jaffe--Witten reference [45], Streater--Wightman, rather than relying on publisher contents or secondary summaries. The existing source-analysis and QFT analysis explicitly say they did not obtain its full axiom text. Record exact axiom/page locations and reconcile domain invariance, adjoint closure, temperedness, covariance, cyclicity and spectrum conventions clause by clause. A Wightman route does not also need an [OS](GLOSSARY.md#notation-and-source-abbreviations) construction. An OS alternative would require the corrected sufficient system in OS II, not bare original E0--E4.

2. Prove the multi-point [tempered](GLOSSARY.md#quantum-fields-and-distributions)-kernel result from the implemented single-field continuity/common-domain adjoint axioms. For each n and field-index word, construct the continuous linear functional on [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) functions of 4n coordinates whose [tensor-test](GLOSSARY.md#quantum-fields-and-distributions) values are the existing vacuumNPoint. Establish the relevant separate/joint continuity and Schwartz [nuclear](GLOSSARY.md#quantum-fields-and-distributions) kernel theorem, tensor-test density and uniqueness; do not assert this merely because single [smeared](GLOSSARY.md#quantum-fields-and-distributions) fields are continuous. Derive the corresponding translation covariance, positivity, adjoint/reversal and local exchange identities. This is the most concrete remaining QFT-standard equivalence item in the crosswalk.

3. Prove the Fourier annihilation condition equals joint translation spectral support in the closed forward cone. Fix the implemented Minkowski sign and U(a)=exp(i P.a) convention; show the written kernel is an integrable Schwartz Fourier transform so explicit spectral_integrable adds no independent method restriction. Relate annihilation for all Schwartz functions vanishing on FutureCone to the usual support formulation, including normalization-independent constants.

4. Relate graph-adjoint self-adjointness and the bounded two-sided resolvent definition to standard closed densely defined operators. The existing exact generator-domain/action and uniqueness results are good controls, but the supporting Stone/spectral equivalences and reality/nonnegative-spectrum consequences remain to be supplied. Redundant spectrum_real/positive_energy obligations need justification as consequences, not an asserted alternative definition of physical energy.

5. Prove the concrete matrix/topology proper-orthochronous [Poincare](GLOSSARY.md#quantum-fields-and-distributions) presentation is the standard connected symmetry group, and justify its use instead of the universal cover for the integer-spin [bosonic](GLOSSARY.md#quantum-fields-and-distributions) invariant observable algebra. Explain why countably many finite-component multiplets suffice, including all real-coefficient polynomial labels and renormalized descendants; countability of a syntax alone does not establish this quantum presentation. If needed provide the separable-Hilbert small-model/unitary-transport result noted above.

6. Prove equivalence between closed-support smeared locality and the usual distributional spacelike-exchange condition. Establish that the additional vacuum-word [analytic](GLOSSARY.md#analysis-and-asymptotics) continuations and their local polynomial [tube](GLOSSARY.md#analysis-and-asymptotics)-bound/uniqueness presentation follow from the selected spectral/locality/domain standards. The assembly currently requires these concrete continuation witnesses; their source-standard sufficiency is not already a theorem merely because boundary values are tied to actual C fields. Likewise establish adequacy of the chosen common [graph-core](GLOSSARY.md#operators-and-spectrum) weak stress-charge presentation without imposing sharp-time operator restrictions.

The full candidate also retains the central, separate fixed-prescription fidelity tasks:
homogeneous massless Ward-compatible normalization adequacy; BV/Legendre/extraction
identities; contact-extension [forest](GLOSSARY.md#short-distance-products-and-contact-terms) equivalence and normalization freedom;
[cohomological](GLOSSARY.md#graded-gauge-symmetry) CS classification and scheme compatibility; and source adequacy of the exact
UV/OPE remainder topology. These are not solved by the outer quantifier or by the QFT
tasks above.

## Disposition

The proposed outer conjunction closes the previously missing group/QFT/gap assembly with
the same central objects. No new contradictory or unrelated-object predicate was found,
and no forbidden particle/confinement condition was introduced. It is appropriately
named a proposed generated specification. It is not yet justified as the exact
Jaffe--Witten target: the listed cited-standard and fixed-presentation fidelity work
remains part of the specification task, distinct from the absent future existence proof.

## Same physical meaning of the computed mixing table

`QuantumMixingCoordinates` proves actual physical-coefficient linearity from finite-cutoff linearity and
coefficient [UV](GLOSSARY.md#scales-and-renormalization) limits. Classical basis reconstruction is the same quantum class
under the same generated Q. `GeneratedMixingMeaning.gammaLoop_coordinates` identifies each computed [gamma](GLOSSARY.md#scales-and-renormalization) column with
the actual local mixing label's coordinate vector. Reconstruction preserves intrinsic
dimension, so no larger syntactic representative loosens [power counting](GLOSSARY.md#scales-and-renormalization). `coordinates_field` proves
the corresponding finite basis combination equals the same C composite operator. None of
these statements asserts quantum injectivity or uniqueness of the CS cohomological
split.

## Spectral test kernel

`SpectralKernelSchwartz` proves the actual kernel exp(-i p.a) is the pinned Schwartz Fourier transform
evaluated at eta a/(2 pi), with exact volume conversion and no unexplained prefactor.
Its actual Schwartz [witness](GLOSSARY.md#reading-a-formalization) supplies all derivative decay estimates and scalar
integrability. Strong continuity and the exact [unitary](GLOSSARY.md#operators-and-spectrum) norm identity then imply
vector integrability, so the explicit Wightman guard imposes no extra condition.
Spectral-measure support equivalence and full [n-point](GLOSSARY.md#quantum-fields-and-distributions) kernel adequacy remain distinct
obligations.

## Later arbitrary-arity closure

The earlier Legendre handoff above records an intermediate proof boundary. `LegendreIdentityCoefficients`
and `LegendreIdentityNormalization` now prove the full identity-root partition normalization for all arities,
coupling and loop orders under the outer graded permutation law. Nonzero terms have
singleton blocks, their assignments are bijective, the roots are unique, the partition
sign cancels the outer graded sign, and n! cancels the exact denominator. Insertion
inversion and uniqueness now follow under gradedness of the computed coefficients.

Deriving that gradedness from the actual F/I equations is still supporting work; the CS
fidelity guard remains in place.

## Actual interacting basic transformations

`FullBVInteractingCoordinates` derives all four nonlinear basic Hamiltonian characteristics from the same
master action and its actual structure constants: sA = d c + g[A,c], sc = -g[c,c]/2,
sbarc = div A + iB, and sB = i Delta c + ig div[A,c]. The proof extracts actual graded
antifield [Euler derivatives](GLOSSARY.md#graded-gauge-symmetry); no separately assigned BRST table is substituted. Full interacting
nilpotency, nonlinear antifield equations and [CME](GLOSSARY.md#graded-gauge-symmetry) remain in progress.
