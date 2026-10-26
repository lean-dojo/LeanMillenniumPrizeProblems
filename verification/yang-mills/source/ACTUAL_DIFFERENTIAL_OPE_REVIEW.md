# Actual interacting differential, source normalization and OPE transport

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review asks whether the action, its symmetry differential, and the extracted
short-distance coefficients really belong to one construction. The key distinction is
between deriving a formula from the specified action and accepting a separately supplied
formula with the right name.

Read the differential proof first, then the integrated response and [OPE](GLOSSARY.md#short-distance-products-and-contact-terms)
transport. The final sections record what had not yet been established at this stage.

For terminology, start with the [relevant glossary section](GLOSSARY.md#graded-gauge-symmetry); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This is central specification/fidelity work, not an existence proof. Exact full
admission remains closed.

## Same-action differential now proved

`FullBVCurvatureEulerEquation` proves that the same actual action has Euler gradient E_mu=-sum_nu(D_nu
F_nu,mu), with its exact actual G/color contractions. `FullBVCovariantColorDerivative` proves the actual
connection commutator on arbitrary full color polynomials. Its [curvature](GLOSSARY.md#gauge-fields-and-observables) antisymmetry
and Jacobi give the exact [Noether identity](GLOSSARY.md#graded-gauge-symmetry) D_mu E_mu=0. The actual [ST](GLOSSARY.md#graded-gauge-symmetry) evolution
makes E covariant. The arbitrary-polynomial two-[ghost](GLOSSARY.md#graded-gauge-symmetry) Jacobi contraction then
closes the shifted gauge-[antifield](GLOSSARY.md#graded-gauge-symmetry) square. Its actual divergence evolution and Noether
identity close the ghost-antifield square.

`FullBVActualNilpotency` assembles all eight actual coordinate species, every total-derivative
[descendant](GLOSSARY.md#gauge-fields-and-observables) and every full polynomial, for every real g and actual ColorFrame. No
[nilpotency](GLOSSARY.md#graded-gauge-symmetry), [CME](GLOSSARY.md#graded-gauge-symmetry), equations of motion as premises, or generic [BV](GLOSSARY.md#graded-gauge-symmetry) Jacobi
theorem is assumed. `FullBVActualDifferentialComplex` proves actual linear comp-self=0, range<=kernel,
exact=>closed, and all those identities on the actual [divergence quotient](GLOSSARY.md#graded-gauge-symmetry). The fixed complex
therefore has a proved meaning, rather than a nilpotency condition supplied by a
candidate.

These results do not assert a general classification of its [cohomology](GLOSSARY.md#graded-gauge-symmetry) or identify
classical and quantum cohomology bijectively.

## Actual integrated response and computed finite change

`IntegratedMarginalConditions.unique` proves uniqueness of the actual source dimension-four integrated response for
the same background and seed, with relevant [IR](GLOSSARY.md#scales-and-renormalization) zero, [marginal](GLOSSARY.md#scales-and-renormalization) normalization at
mu and irrelevant [UV](GLOSSARY.md#scales-and-renormalization) jets. No pointwise identification is assumed. `IntegratedWardFlow`
defines the source dimension-five [BRST](GLOSSARY.md#graded-gauge-symmetry) response with the actual same-[master-action](GLOSSARY.md#graded-gauge-symmetry)
seed, relevant IR dimensions below four, normalization in dimensions four through five,
and irrelevant UV dimensions above five.

`ReducedTaylorDensity` constructs a finite actual superalgebraic density from reduced Taylor jets
with fixed Fourier/factorial coefficients and proves its finite engineering bound.
`IntegratedPointwiseNormalization` computes coefficients recursively from that target and the same pointwise
insertion's actual unit-triangular [jet](GLOSSARY.md#graded-gauge-symmetry) matrix; irrelevant higher rows are
retained. `IntegratedNormalizationProjectors` proves the actual constructed finite amplitude has the claimed
canonical normalization rows. Neither a free mixing matrix nor a false global Kronecker
identity is used.

The remaining Fourier/Taylor recovery is substantive: canonical admissible supermonomial
projectors must determine the required graded momentum jets. Repeated odd jets vanish at
the permutation-fixed origin, not at arbitrary momenta. Consequently the [analytic](GLOSSARY.md#analysis-and-asymptotics)
all-coordinate uniqueness theorem cannot be substituted for this algebraic/PDE adequacy
proof. `MomentumJetSymmetry` proves actual all-order derivative permutation symmetry, a necessary
part of that bridge. The generic independent/reduced linear uniqueness theorems are
supporting theorems only; fixed candidate boundary definitions are not strengthened by
their hypotheses.

Vacuum subtraction of the integrated response must also remain explicit when comparing
pointwise responses.

## Actual OPE and ultraviolet transport

`RegulatedOPEDilation` proves dilation of the actual disconnected product and the full well-founded
triangular OPE recursion with the same output projectors. `UltravioletOPEDilation` transports the
actual coefficient limit along the [cofinal](GLOSSARY.md#analysis-and-asymptotics) positive cutoff map UV->a*UV. It does not
choose a new prediction. The physical generated coefficients further use corrected
lifts, weak distributional limits and same-Q [cohomological](GLOSSARY.md#graded-gauge-symmetry) recovery; their full
Ward/lift/CS/continuum transport remains a separate obligation.

`FixedFlowCanonicalDilation` derives the actual canonical one-parameter scale/momentum derivative from
proved dimensional covariance. This does not silently assume separate mu/UV
differentiability, or identify an unproved raw projection with the physical [beta](GLOSSARY.md#scales-and-renormalization)
function.

## Stress normalization issue remains explicit

The same-C/same-H stress and centered curvature anomaly are concrete, but current
existential charge profiles allow a spatial cutoff with zero integral. Such a cutoff
cannot detect a constant identity density in its spatial charge. Thus current charge
normalization alone does not prove zero vacuum stress. A justified
positive/nonzero-integral cutoff normalization or universal profile formulation, with
the corresponding same-vacuum stress argument, is still needed for that proposed
centering interpretation.

No vacuum-zero premise is silently inferred or added to the exact target.

## Remaining source-fidelity boundary

Full interacting nilpotency and background/integrated-response uniqueness are closed.
The formal nonabelian cohomology/source-normalization audit must identify exactly which
universal equivalence lemmas justify the chosen prescription, while keeping existence of
a response separate. Full graded projector/Fourier adequacy, nonlinear restoration and
generated physical transport, stress normalization and cited-[QFT](GLOSSARY.md#quantum-fields-and-distributions) equivalences
remain explicit.
