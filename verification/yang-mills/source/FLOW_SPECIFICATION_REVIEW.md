# Fixed flow, extraction and physical matching: implementation review

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This progress review traces the route from a group-dependent action to coefficients that
can be compared with physical field products. Its tables describe component definitions;
the later assembly sections explain how they must share the same data.

Read the component table first, then the Ward/contact assembly, scale insertion and
vacuum-word matching. The remaining-work sections record the status of this intermediate
construction.

For terminology, start with the [relevant glossary section](GLOSSARY.md#scales-and-renormalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This continuation addresses the central [renormalization](GLOSSARY.md#scales-and-renormalization) and UV/OPE definitions. It is not a
complete specification and does not require or supply a proof of nonperturbative
Yang–Mills existence. The full-target admission gate remains closed.

## Definitions now present

| Requirement | Concrete implementation | Source |
|---|---|---|
| Same actual [gauge group](GLOSSARY.md#gauge-fields-and-observables) in perturbative predictions | Actual bracket/color frame, physical and [antifield](GLOSSARY.md#graded-gauge-symmetry) action [vertices](GLOSSARY.md#perturbative-calculations), fixed covariance and graded external coefficients | [FHH](GLOSSARY.md#notation-and-source-abbreviations) 1511.09425 §§2–3, Table I, (46)–(70) |
| Fixed flow and local freedom | `CoefficientFlowConditions`: explicit graded loop/partition RHS, finite local [marginal](GLOSSARY.md#scales-and-renormalization) vertices, actual-G/O(4) coefficient invariance, UV/relevant/marginal [jet](GLOSSARY.md#graded-gauge-symmetry) equations, endpoint continuity | [FH](GLOSSARY.md#notation-and-source-abbreviations) 1603.08012 (2.20), (2.25); FHH local [counterterm](GLOSSARY.md#scales-and-renormalization) discussion |
| Fixed composite normalization | Admissible supermonomials, exact finite degree enumeration, ordered momentum projector, single-insertion and [oversubtraction](GLOSSARY.md#short-distance-products-and-contact-terms) equations | FH (4.1)–(4.4) |
| Fixed regulated [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) extraction | Product-minus-hbar-oversubtraction functional and dimension-triangular recursion, polynomial inputs computed from the actual [curvature](GLOSSARY.md#gauge-fields-and-observables) map | FH (4.5), (5.5)–(5.7) |
| Actual quantum gauge operator ingredients | Exterior/tensor [superjet](GLOSSARY.md#graded-gauge-symmetry) algebra and fixed antifield-free classical differential; fixed free [BV](GLOSSARY.md#graded-gauge-symmetry) kernel from the same quadratic action; rectangular [Ward](GLOSSARY.md#graded-gauge-symmetry)-coordinate helpers | FHH (49)–(60), (281)–(283) |
| Generated coefficient [UV](GLOSSARY.md#scales-and-renormalization) limit | `FixedFlowSystem.IsCoefficientLimit`: same actual-G input polynomial and same flow, actual g derivative, guarded compact-test integral, UV [weak limit](GLOSSARY.md#analysis-and-asymptotics) away from all collisions | FH Definition 3 and Theorem 1 |
| Any finite insertion [cluster](GLOSSARY.md#short-distance-products-and-contact-terms) in the physical [QFT](GLOSSARY.md#quantum-fields-and-distributions) | `WeakMultiExpansion`: actual same-C field products, coherent all-degree output basis, relative-coordinate scaling, separated physical [spectators](GLOSSARY.md#short-distance-products-and-contact-terms), separate coefficient singularity bound | FH Theorem 1 (1.1.2)–(1.1.3), interpreted nonperturbative weak relation |
| Same [RG](GLOSSARY.md#scales-and-renormalization), Wick labels, fields and stress | `CoupledMultiSectorConditions`: pair restriction of the same multi family, one running system and actual field transport at every degree, all-input tensor Wick transformation, same stress/Hamiltonian | Section 4; [IZ](GLOSSARY.md#notation-and-source-abbreviations) renormalization/OPE discussion; chosen [analytic](GLOSSARY.md#analysis-and-asymptotics) presentation |
| Explicit coincidence quantities | Continuous diagonal restriction, signed relative delta derivatives and finite bounded-order cluster [counterterms](GLOSSARY.md#scales-and-renormalization) acting through the same C field | Distributional contact-term vocabulary; Ward selection not finished |
| Stress tree normalization | Fixed canonical stress polynomials, source g² cancellation and actual-G/B evaluation agreement | Classical Hilbert tensor, source-normalization convention |
| RG coefficient extraction operations | Constant-one formal square root with proved square identity; g0=gZ1Z3^(-3/2), fixed-bare [beta](GLOSSARY.md#scales-and-renormalization) quotient and label [gamma](GLOSSARY.md#scales-and-renormalization)=-Z^-1 DZ, guarded derivatives/unit denominator and coefficientwise limits | IZ (12-124)–(12-126), printed p.593; label transport derivation |

FH means Fröb–Holland, arXiv:1603.08012. FHH means Fröb–Holland–Hollands,
arXiv:1511.09425. Exact primary equations and conventions are recorded in [PERTURBATIVE_PRESCRIPTION.md](PERTURBATIVE_PRESCRIPTION.md)
and [BRST_BV_INTERFACE.md](BRST_BV_INTERFACE.md).

## Further central definitions now present

* `FullBV` gives the full complex field/antifield superjet algebra, finite
  [Euler derivatives](GLOSSARY.md#graded-gauge-symmetry), integrated [divergence quotient](GLOSSARY.md#graded-gauge-symmetry) and actual master density.
  Its local evolutionary [ST](GLOSSARY.md#graded-gauge-symmetry) differential retains ordinary jet descendants.
  `FullBVBridge.densityAmplitude_vertices` proves exact agreement with the
  actual flow vertices; `FullBVLocalST` proves the normalized positional formula.
* `RegulatedBVFlow` and `RegulatedWardInsertion` fix the actual same-action
  bare defects in FHH (302), (324) and the partitionwise Fourier kernel (338).
* `ClassicalPointContact` fixes (335) from actual right/left jet derivatives.
  `ContactTaylorProjection` includes the finite Taylor shift by each partition's
  right external momentum when the field is centered at the first insertion.
  `ContactAnomalyTransport` fixes the full A2 UV boundary (337)–(346), its
  same-background homogeneous flow, support, smoothness and coefficient limits.
* `QuantumObservableLift` supplies finite local corrected representatives with
  fixed tree symbols, the generated Q [cocycle](GLOSSARY.md#graded-gauge-symmetry) equation and coupling/loop grading.
  `QuantumOutputRecovery` uses this same [dictionary](GLOSSARY.md#notation-and-source-abbreviations) on both sides modulo actual
  generated Q-images; it asserts neither injectivity nor a classical/quantum
  bijection. The earlier raw `PhysicalCohomologicalRecovery` remains only a helper.
* `GeneratedEuclideanCoefficients` fixes raw outputs by [off-diagonal](GLOSSARY.md#short-distance-products-and-contact-terms) weak UV
  limits of the lifted extractor and recovers physical outputs on every finite
  [filtration](GLOSSARY.md#gauge-fields-and-observables). Its physical graph-order guard makes hbar=1 assembly finite at
  every coupling order. `GeneratedMultiMatching` binds that assembled series to
  the same composite map, OPE, Wick transport and [stress tensor](GLOSSARY.md#scales-and-renormalization).
* `PartialDiagonalContact` gives actual continuous first-centered pair-contact
  maps on joint position/momentum tests; `CollisionScaling` specifies local
  scaling bounds at every partial collision. These do not alone restore Ward
  identities or classify all allowed local extensions.
* `ActionProbeNorms` proves all five actual reference denominators nonzero
  from group simplicity and form positivity. Full local-jet decomposition now
  fixes action normalization coordinates without extra nondegeneracy assumptions.

## Full local Ward/contact assembly

`ConnectedInsertionFlow` fixes connected insertions and their finite graded [cumulants](GLOSSARY.md#short-distance-products-and-contact-terms) as the same G0.
`MultiWardRestoration` states all-[arity](GLOSSARY.md#perturbative-calculations) quantum Ward identities on compact nonexceptional joint
tests including partial diagonals. `DistributionalCumulants` fixes the connected/disconnected contact
relation by compact-[mollifier](GLOSSARY.md#analysis-and-asymptotics) tensor limits of actual distributions on disjoint blocks.
`PartialDiagonalSupport` and `SeparatedWardIdentity` prove the [contact terms](GLOSSARY.md#short-distance-products-and-contact-terms) vanish only on separated tests and derive
the empty-elementary-leg Ward sum. No Q-exact null identity is imposed on arbitrary
gauge/ghost external legs.

`PartitionContact` and `LocalContactRenormalization` compute full contact extensions from the actual finite-cutoff
G0. Universal finite block coefficients see no [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) positions or momenta; they
obey engineering/ghost/parity and coupling-loop bounds. All partitions act through
proper diagonal [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) maps into the same lower-insertion family. UV limits are
imposed on the whole counterterm sum, with one prescription for all [IR](GLOSSARY.md#scales-and-renormalization) cutoffs.
This excludes the otherwise possible delta-times-arbitrary-spectator-function loophole.
`JointCollisionScaling` adds bounds across every partial collision.

`LocalWardFlowFamily` collects these exact same data at every normalization scale. `LocalWardOPEStressConditions` binds
the generated coefficients to the same physical OPE, Wick continuation and common
exhaustive RG frames. Its stress dictionary is exactly that frame's degree-four sector.
Quantum stress has its fixed canonical tree, same-Q local corrections and same-W limits;
its regular source numerator allows scalar mixing and obeys the pole-cleared
zero-anomalous-dimension identity g beta a' - 2 beta a = g gamma a.

The actual stress tensor still generates the actual [Hamiltonian](GLOSSARY.md#operators-and-spectrum) and satisfies its trace
anomaly; no all-order trace-zero condition is introduced.

`CompositeRenormalizationExtraction` uses actual lifted bare INSERTION amplitudes, including the full L bare
counterterm matrix, to define composite normalization. Gram coordinates are diagnostic
only. The authoritative full bare relation allows same-Q/EOM remainders without
demanding a classical/ quantum bijection or Gram-orthogonal physical quotient. Its gamma
formula remains conditional on actual action/scale transport authorization.

## Computed scale insertion and physical short-distance words

`AmputatedLegendre` fixes Gamma by coupling-adic inversion of the actual connected mean-field
map. `CohomologicalScaleInsertion` differentiates that computed full action and the same corrected
insertions, including their scale dependence. The [CS](GLOSSARY.md#scales-and-renormalization) residuals use full ordered
amplitudes, inverse-dual source weights and actual generated-Q insertions, with weak
UV-then-IR removal. `GeneratedScaleNormalization` assembles finite beta/mixing loop sums and resolves
mixing outputs in the actual classical invariant basis. This does not infer a
classical/quantum [cohomology](GLOSSARY.md#graded-gauge-symmetry) bijection or authorize raw projected bare Z data.

`FiniteWardRestoration` retains relevant local corrections with explicit engineering powers of the
subtraction scale. `CACSchemeTransport` computes the source normalization I and distinguishes the
local/free regulated compensation and its UV artifact. These are concrete transport
targets, not proofs that a restoration tower or a scheme comparison exists.

`VacuumWordContinuation` has the boundary values of the same composite operator words. `GeneratedVacuumWordMatching`
compares their short-distance UV germs to same-family corrected invariant words to every
running-coupling order. It does not resum perturbation theory or identify exact
nonperturbative vectors with formal words. `GeneratedRenormalizedSector` binds these data and the
OPE/stress fragment to the computed beta and the same Wick-conjugated mixing at every
positive subtraction scale. Its homogeneous/vacuum-subtracted presentation still
requires a source-equivalence argument.

## Remaining central assembly/fidelity work

The current generated sector is provisional. The classical master equation, graded
[Legendre](GLOSSARY.md#perturbative-calculations) inversion, same-engine scale-insertion classification, [cohomological](GLOSSARY.md#graded-gauge-symmetry)
uniqueness/normalization, compatible homogeneous-scheme choice, and
source/cited-standard adequacy must be established or resolved before admitting the full
fixed target. In particular, the filtered restoration tower and finite scheme-transport
definitions have not yet been proved to supply the massless same-flow normalization used
by the provisional sector. These are specification/fidelity issues, not requests for a
nonperturbative existence proof.

See [SCALE_WORD_INTERFACE_REVIEW.md](SCALE_WORD_INTERFACE_REVIEW.md) for the current audit boundaries.

## Supporting equivalence/fidelity work

These are not missing nonperturbative existence proofs: graded functional-flow and bare
Wick equivalence (including opposite Fourier conventions), normalized density
reconstruction and degree bounds, master equation/bracket descent and local ST
[nilpotency](GLOSSARY.md#graded-gauge-symmetry), flow uniqueness/bounds and graph homogeneity, source/canonical/shifted-B BV
equivalence, physical cohomology/null-state identification, action-jet reconstruction
and finite-scheme covariance, Schwartz kernel/basis existence, analytic continuation
applicability and comparison of the weak/charge formulations with the cited standards
remain to be established.

The particular exponential flow scheme is an auxiliary perturbative presentation; its
universal admissibility has not been silently added as a restriction on a
nonperturbative construction. A complete fidelity argument must justify its use.

The stress symbol is strictly a tree normalization. Defining the full tensor as an
all-order linear image of that traceless polynomial would exclude the trace anomaly
again. The existing same-theory charge/trace conditions continue to use the actual
Hamiltonian, the actual B(F,F) label, scale, coupling and common beta.

## Independent adversarial review and fixes

The reviewer checked elementary graded contractions, free BV species signs, source
rescaling, multi-insertion [tube](GLOSSARY.md#analysis-and-asymptotics) order, tensor transport, and the generated weak
coefficient-limit bridge. Found and repaired: totalized derivatives without
differentiability, a missing formal inverse-unit guard, disconnected insertion UV
endpoint values, and square finite Ward sectors incorrectly treated as closed under a
degree-raising differential. The full review is in [FLOW_ADVERSARIAL_REVIEW.md](FLOW_ADVERSARIAL_REVIEW.md). A passing build and these
local checks do not certify [semantic fidelity](GLOSSARY.md#reading-a-formalization).

## Latest independent repair audit

The all-q external permutation condition was restricted to nonempty insertion lists: the
background only has momentum-conserving symmetry under its reduced extension. The pair
anomaly now evolves as an independent FULL amplitude with its fixed source UV seed. Its
finite low-degree insertion representation is required only on normalization jets and
through a weak UV-vanishing remainder, so [regulator](GLOSSARY.md#scales-and-renormalization)-suppressed higher-degree UV terms
are retained. Universal block counterterms close the spectator-dependence loophole.

See [LOCAL_WARD_ADVERSARIAL_REVIEW.md](LOCAL_WARD_ADVERSARIAL_REVIEW.md); these repairs do not prove existence or complete source/forest
equivalence.
