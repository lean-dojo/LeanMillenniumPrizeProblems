# Independent central review: flow, extraction and multi-cluster stage

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review tests the flow equations, coefficient extraction and collision limits for
concrete loopholes. One example is Lean’s [totalized derivative](GLOSSARY.md#reading-a-formalization): without a differentiability
condition, its value need not represent the intended [analytic](GLOSSARY.md#analysis-and-asymptotics) derivative.

Start with the repaired derivative issue, then the sign checks and multi-insertion
conditions. The later sections distinguish absent definitions from supporting theorems
still needed at that stage.

For terminology, start with the [relevant glossary section](GLOSSARY.md#short-distance-products-and-contact-terms); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

Reviewed the evolving strict-compiling definitions in StressSymbols,
FormalRenormalization, MultiOperatorProductExpansion, MultiContact, MultiWickRotation,
MultiRenormalizationGroup, GradedAmplitude, PerturbativeFlow, CompositeExtraction,
OversubtractedFlow, FreeWardExtraction, PerturbativeCoefficientLimits, and the concrete
[BRST](GLOSSARY.md#graded-gauge-symmetry) [jet](GLOSSARY.md#graded-gauge-symmetry) core/interface. This is a mathematical content review, not
build-based fidelity certification. No owner files were edited.

## Concrete defect found and repaired

**F1 — Totalized scale derivatives.** Initial IsBetaLimit/IsGammaLimit invoked
`deriv` on arbitrary coefficient functions without differentiability obligations;
Lean could interpret non-differentiable scale coordinates as zero derivatives. The owner
added coefficientwise differentiability on positive reference scales below the
[UV](GLOSSARY.md#scales-and-renormalization) cutoff. IsGammaLimit also initially lacked the denominator-unit guard on the
same bare coupling used by betaAtCutoff; that guard was added. These changes close the
identified [totalization](GLOSSARY.md#reading-a-formalization) loopholes in these extraction relations.

They do not themselves identify arbitrary coordinate series with the fixed
[Ward](GLOSSARY.md#graded-gauge-symmetry)-restored action.

## Sign and normalization checks

- Explicitly checked the S0-derived freeBVKernel on every species in the exp(-ipx) convention. It yields s0 A=-ip c, s0 cbar=-ip·A+iB, s0 B=-ip²c, and the stated [antifield](GLOSSARY.md#graded-gauge-symmetry) images -Delta A+partial cbar*, B-i cbar*, Delta c, and -Delta cbar-div A*+i Delta B*. The [BV](GLOSSARY.md#graded-gauge-symmetry) Euler signs and conjugate (-p,p) momentum arguments are consistent.
- Background and independent-insertion contractions pass elementary odd-pair tests. For an odd insertion on each side, intrinsicContractionSign supplies the needed covariance sign. InsertionPairSign is the [Koszul](GLOSSARY.md#graded-gauge-symmetry) sign of bringing the ordered selected pair before the remaining insertion blocks. No extra factor 1/2 belongs to the k<l source sum.
- The momentum coefficient projector implements explicit i powers, derivative multiindex factorials and full independent insertion momenta. Its multiplication by [bosonic](GLOSSARY.md#quantum-fields-and-distributions) multiplicity factorials in normalizedPotentialExpansion is an input-basis conversion, not automatically a physical output projector. Tree duality remains to be proved.
- The exact regulated [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) recursion subtracts lower engineering dimensions and performs the complete [loop-order](GLOSSARY.md#perturbative-calculations) [Cauchy](GLOSSARY.md#perturbative-calculations) product with the same single-insertion L. Coefficients are extracted, not independently assigned. The finite monomial enumeration completeness theorem prevents a missing-label weakening.
- StressSymbols retains F_source=g F_canonical and cancels the source g^-2 algebraically. Actual bracket/color-frame evaluation and symmetry identities are meaningful supporting equations; no mismatch was found in their ordered [Lorentz](GLOSSARY.md#quantum-fields-and-distributions) contractions.
- Formal [beta](GLOSSARY.md#scales-and-renormalization) extraction -(mu partial_mu g0)/(partial_g g0), and [gamma](GLOSSARY.md#scales-and-renormalization)=-Z^-1 (mu partial_mu+beta partial_g)Z, have the correct sign/order for Q_mu(v)=Q_bare(Z v). Unit-root and inverse recursions are concrete. Their physical use still needs normalized actual coordinates with the stated tree constants.

## New multi-insertion components

The 4n relative-coordinate dilation is normalized correctly, the center remains
[smeared](GLOSSARY.md#quantum-fields-and-distributions), and the ordered actual product kernel uses all n+1 fields on Q's common
domain. The separate coefficient singularity estimate is not replaced by possible
cancellation in the OPE remainder. MultiOffDiagonal excludes all pairwise relative
collisions.

MultiLowerTube imposes both separation from the final point zero and the ordering
between nonfinal points. Its boundary path has imaginary times -epsilon(n-i), so every
ordered difference lies in the intended past timelike [tube](GLOSSARY.md#analysis-and-asymptotics). The label rotation has
one W on output and inverse W on every incoming slot. No tube-order or generalized
matrix-slot/scaling error was found.

The n=1 restriction pairFromMulti has the correct [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) pullback direction and unit
coordinate Jacobian. Pair/multi matching uses the same exact coefficient family, common
[RG](GLOSSARY.md#scales-and-renormalization) frames and stress normalization. Relative/center delta-derivative contacts
have the standard (-1)^|alpha| sign and act through the same local [composite field](GLOSSARY.md#gauge-fields-and-observables).
[Partial-diagonal](GLOSSARY.md#short-distance-products-and-contact-terms) compositions and Ward restrictions are still explicitly separate; the
implemented total-diagonal vocabulary does not silently claim to supply them.

## Definition gaps versus supporting lemmas

### Supporting equivalence work for already concrete definitions

1. Tree projector/normalized-monomial duality, including odd ordering, and action-monomial equivalence.
2. Unique flow solution relative to its mixed normalization conditions, and graph homogeneity justifying finite loop assembly. A plausible induction is lexicographic in [loop order](GLOSSARY.md#perturbative-calculations) and [external-leg](GLOSSARY.md#perturbative-calculations) count: the linear contraction lowers loop; at [tree level](GLOSSARY.md#perturbative-calculations) every background [vertex](GLOSSARY.md#perturbative-calculations) has at least three legs, so quadratic unknown factors have fewer external legs. This observation is not a completed uniqueness proof.
3. Full graded Leibniz and [nilpotency](GLOSSARY.md#graded-gauge-symmetry) proofs for the concrete antifield-free unshifted BRST coordinate map, commuting total derivatives, and formal matrix inverse/root equivalences.
4. Validated correspondence of polynomial jet substitution to actual smooth connections, and consistency of finite frames/limits once the required quotients are fixed.

### Still missing central definitions

1. **Shifted-B full BV/local-functional system.** The concrete BRST algebra currently uses real unshifted s(cbar)=B,sB=0, while the flow/freeAction use the complex shifted convention s(cbar)=div A+iB,sB=i div Dc. The explicit substitution B_unshifted=div A+iB_shifted must be implemented with antifields, [Euler derivatives](GLOSSARY.md#graded-gauge-symmetry) and the local [divergence quotient](GLOSSARY.md#graded-gauge-symmetry), with the fixed [master action](GLOSSARY.md#graded-gauge-symmetry) and quantum contact/Ward maps. The interface acknowledges this; merely composing the two existing maps would be wrong.
2. **Physical cohomology/output recovery.** The fixed polynomial input expansion is not its dual output projector. Even an elementary input p=x²+y² has two normalized monomial coordinates; reusing those coordinates as a projector does not extract a unit coefficient of p. A fixed BRST/EOM/divergence quotient and physical output basis/recovery map must identify the extracted elementary coefficients with invariant observable outputs. The actual quantum differential/contact data must be connected to the same amplitudes.
3. **Ward-restored normalization decomposition.** Z1,Z3 and insertion normalization matrices must be extracted from the same local action/insertion coordinates after a fixed Ward-restoring decomposition/finite scheme transport. A raw cubic coefficient is not the bare coupling. The relation to g0=g Z1/Z3^(3/2), auxiliary/gauge-fixing/antifield rescalings and all-order local normalization freedom must be explicit. FormalRG helpers alone do not authorize free Z inputs.
4. **Higher contact/Ward and extension prescription.** Total-diagonal delta derivatives and [off-diagonal](GLOSSARY.md#short-distance-products-and-contact-terms) UV limits do not yet specify all partial-diagonal contact extensions, their power-counting/symmetry restrictions and restored quantum Ward equations.

These gaps concern specification meanings, not absence of a continuum Yang–Mills
existence proof.

## Further integration cautions

**F2 — Square finite Ward projections need closure.** finiteWardCoordinates computes a
square finite-monomial projection Z^-1W. Since q raises [engineering degree](GLOSSARY.md#gauge-fields-and-observables) by one, a generic
all-labels-below-D square sector is not closed. A physical differential needs compatible
rectangular/exhaustive V_<=D to V_<=D+1 maps or a proved closed finite subspace. Do not
impose the full amplitude Ward identity or nilpotence on arbitrary square truncations
while discarding outgoing labels.

**F3 — Stress symbol identification must remain tree level.** The canonical
four-dimensional stress polynomial is identically traceless. Binding all-order T
linearly to polynomialInsertionFlow of that same exact symbol would reintroduce a forced
trace-zero identity. The current tree-symbol caveat is appropriate. Full stress
normalization must include the fixed anomalous renormalization/metric-variation
prescription. Also distinguish the physical Lorentzian symbol from its explicitly
[Wick-transported](GLOSSARY.md#analysis-and-asymptotics) Euclidean insertion before applying the Euclidean flow.

## Fixed coefficient-limit bridge reviewed

FixedFlowSystem binds actual G/color frame, reference scale, background flow, single
insertions and oversubtractions. regulatedInvariantCoefficient uses the actual
bracket-dependent input substitution and the fixed triangular extractor.
regulatedCouplingCoefficient takes actual coupling derivatives; CoefficientRegularity
explicitly supplies smoothness and compact-test integrability. IsCoefficientLimit
compares to that fixed output on every compact test away from all partial coincidences,
and the uniqueness lemma is correctly only off-diagonal. This avoids the false demand
that unsubtracted free Wick-power coefficients have a cutoff limit across coincidence.

Physical invariant-output recovery, [contact extension](GLOSSARY.md#short-distance-products-and-contact-terms) and loop/RG assembly remain separate. No
new defect was found in this limited bridge.

## Disposition

F1 was repaired. No additional sign/normalization defect was found in the reviewed fixed
graded flow, free BV generator, multi-[cluster](GLOSSARY.md#short-distance-products-and-contact-terms) scaling/tube, or actual-input
off-diagonal coefficient-limit definitions. F2/F3 are important assembly restrictions.
The physical output/cohomology and Ward-normalization definitions above remain central
blockers to an exact full target. Passing compilation, this review, and agreement
between agents do not discharge those meanings or establish [source fidelity](GLOSSARY.md#reading-a-formalization).
