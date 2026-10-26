# Same-action master equation and filtered quantum proposal

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This report separates the master equation for the actual action from the broader quantum
transport conditions. It also explains why allowing lower-dimensional [operator mixing](GLOSSARY.md#scales-and-renormalization)
requires a filtered, scale-dependent formulation.

Read the action and quotient identities first. Then follow the coupling relation,
quantum transport and vacuum subtraction; the last section records the proof boundary at
this stage.

For terminology, start with the [relevant glossary section](GLOSSARY.md#graded-gauge-symmetry); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

These are definitions and supporting fidelity proofs, not a nonperturbative Yang--Mills
existence proof. Exact full admission remains closed.

## Actual full classical action

The same fixed free, physical and source [vertices](GLOSSARY.md#perturbative-calculations) now satisfy `masterAction_classicalMasterEquation`. The proof
derives every coordinate, uses actual G Jacobi/invariant color contractions, proves
sF=g[F,c], and proves [curvature](GLOSSARY.md#gauge-fields-and-observables)-squared invariance. The actual [gauge fermion](GLOSSARY.md#graded-gauge-symmetry) and explicit
kinetic, [ghost](GLOSSARY.md#graded-gauge-symmetry) and shifted-source currents express that same action as F²/4+sΨ plus
the same characteristic-linear [antifield](GLOSSARY.md#graded-gauge-symmetry) density modulo divergences. Basic [nilpotency](GLOSSARY.md#graded-gauge-symmetry),
physical-action invariance and the even self-bracket split prove the full integrated
[CME](GLOSSARY.md#graded-gauge-symmetry).

Neither full antifield nilpotency nor CME is assumed.

`FullBVPartialTotalDerivative` proves the exact [jet](GLOSSARY.md#graded-gauge-symmetry)-partial/total-derivative commutator. The finite
multiindex Euler sums telescope, proving both left and right [Euler derivatives](GLOSSARY.md#graded-gauge-symmetry) kill actual
divergences. Hence both Euler maps descend and `functionalBracket` is a genuine operation on the
fixed quotient. `bracketGraph_iff` and `bracketGraph_exists_unique` identify the previous concrete graph with that
operation. The evolutionary map equals this actual integrated bracket. Its full graded
Leibniz and free full-polynomial nilpotency are proved.

Interacting nilpotency is proved for all basic coordinate descendants and two antifield
species. The general [Hamiltonian](GLOSSARY.md#operators-and-spectrum) square/Jacobi identity, hence the final full interacting
polynomial nilpotency, is still work; it does not follow just by declaring the CME.

## Actual coupling and canonical field rescaling

`EssentialCouplingClass.essentialCoupling_class_relation` proves g[partial_g S]+2[S_antifield-free]=Q_S[canonical rescaling generator]
in the same [divergence quotient](GLOSSARY.md#graded-gauge-symmetry), with the actual coupling derivative. `CanonicalJetEuler` identifies this
pointwise Euler operation with the [CS](GLOSSARY.md#scales-and-renormalization) external-field action on the same actual
finite [vertex](GLOSSARY.md#perturbative-calculations) lists. These are algebraic identities and do not prove uniqueness of
[beta](GLOSSARY.md#scales-and-renormalization) or physical operator mixing. At free g=0 the integrated free action is exact;
its integrated F² class must not be confused with local observable [cohomology](GLOSSARY.md#graded-gauge-symmetry).

The remaining essential-coupling classification concerns the formal NONABELIAN
deformation with its coupling grading, antifields and non-Laurent primitives.

## Broader filtered quantum transport

`FilteredQuantumRG` removes the former requirement of exact degree-preserving quantum transport
and one scale-independent [gamma](GLOSSARY.md#scales-and-renormalization) table. Every gamma formal jet is computed from the
same N at its actual positive subtraction scale, conjugated by the same Wick rotations.
One [running coupling](GLOSSARY.md#scales-and-renormalization) and coherent finite sectors transport the same C operators. The stress
[dictionary](GLOSSARY.md#notation-and-source-abbreviations) is scale-dependent and constrained by the same Q/lift/representatives at
every scale. Its equation includes both explicit scale and coupling derivatives.

Canonical scaling follows transport. Coefficients use D_lambda^-1 R_t C(lambda x)(R_t^-1
D_lambda)^tensor; vacuum words use incoming R_t^-1 W D_lambda and no outgoing factor.
Thus powers use external degrees. `QuantumSchemeObstruction` verifies this with a genuine invertible,
unit-preserving mu^d identity shift. `FilteredQuantumRGReduction` embeds the old homogeneous frame, derives
inverse degree preservation and proves exact coefficient/word formula reduction with the
stated Wick degree condition.

`VacuumCenteredTrace` fixes the anomaly using the actual field minus its actual same-vacuum
[one-point](GLOSSARY.md#scales-and-renormalization) functional times identity. There is no free subtraction constant.
Identity-shift invariance, zero centered one-point and reduction to the former anomaly
at actual zero original one-point are proved. `VacuumCenteredTraceMeaning` proves anomaly modulo a scalar
identity plus actual zero stress one-point implies this centered equation. The upstream
physical/source argument for normalized stress vacuum-zero is still required.

The curvature-square label still equals the same actual G invariant form's F² on every
smooth connection, and charges use the same physical Hamiltonian.

`FilteredGeneratedCandidate` binds these definitions to the same complete [QFT](GLOSSARY.md#quantum-fields-and-distributions), full vacuum kernels
and finite positive physical mass for every G. Its `qft_exists` and `stress_nonzero`
consequences are proved. No independently selected beta, Euclidean [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) or word
predictions enter this assembly. The old homogeneous proposal remains a comparison, not
an additional mandatory target.

## Actual finite-flow dilation and remaining fidelity

`FiniteFlowDilation` derives covariance/derivative-kernel scaling, the actual 4D loop Jacobian,
both nonlinear flow contractions, and the rescaled finite-flow equation. This transports
solutions to the same equation; it DOES NOT prove the chosen solution equals its
rescaling. Fixed-reference perturbative coefficient/word comparisons need simultaneous
same-engine boundary/insertion/dictionary dilation covariance and justified
[UV](GLOSSARY.md#scales-and-renormalization)-then-[IR](GLOSSARY.md#scales-and-renormalization) limit transport. Availability of a dimensionally covariant
FILTERED massless [Ward](GLOSSARY.md#graded-gauge-symmetry)-compatible normalization is the precise supporting source
obligation.

Arbitrary smooth scale-dependent redefinitions such as exp(mu)*identity need not satisfy
it; no universal arbitrary-scheme invariance is claimed.

Other remaining issues are formal nonabelian local/cohomological stability, full
interacting [BV](GLOSSARY.md#graded-gauge-symmetry) nilpotency/Jacobi, exact normalized stress/source anomaly
transport and the cited-QFT framework equivalences. Classical basis availability,
algebraic graded [Legendre](GLOSSARY.md#perturbative-calculations) inversion, classical full CME and actual bracket descent are
now proved and are not listed as missing meanings. The absence of a nonperturbative
existence proof is a separate issue.
