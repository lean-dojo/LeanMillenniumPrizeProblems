# Graded flow and fixed coefficient-boundary stage

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This implementation note fixes the conventions needed to calculate perturbative
amplitudes. The action supplies the interaction data; the flow and boundary equations
constrain how amplitudes depend on cutoffs and normalization scale.

Read the field ordering and Fourier convention before the flow formulas. Then compare
the boundary data with the [analytic](GLOSSARY.md#analysis-and-asymptotics) safeguards: endpoint values alone do not control
behavior approaching an endpoint.

For terminology, start with the [relevant glossary section](GLOSSARY.md#perturbative-calculations); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

New modules: [GradedAmplitude.lean](../YangMills/GradedAmplitude.lean) and [PerturbativeFlow.lean](../YangMills/PerturbativeFlow.lean).

## Fixed conventions

External basic fields are `BasicField G`; antifields are the second copy in `ExternalLeg G = BasicField G ⊕ BasicField G`.
Parity, [ghost number](GLOSSARY.md#graded-gauge-symmetry) and degree are the explicit assignments of 1511.09425 Table I (p14),
including [antifield](GLOSSARY.md#graded-gauge-symmetry) degree `3 − basic degree`. Ordered coefficients mean ordered left
variational derivatives, the first listed derivative acting first. Statistical parity
and [ghost-number](GLOSSARY.md#graded-gauge-symmetry) selection are explicit obligations.

The functional Fourier convention is exp(−ipx). Each derivative in a local [vertex](GLOSSARY.md#perturbative-calculations)
therefore contributes −ip, while the primary composite extractor D uses +i, giving
the required label delta. The older bare position contraction uses an inverse-plus
Fourier convention; equivalence under p→−p for its even covariance has to be proved
before linking those formulas directly.

`linearFlowRHS` is the integral of the combined one-loop contraction without 1/2. It uses
actual covariance derivative and loop l−1, and vanishes at l=0. `quadraticFlowRHS L F` is the
ordered loop-Cauchy/external-[unshuffle](GLOSSARY.md#perturbative-calculations) product without 1/2, with conserved background L
fixing the joining momentum. Background flow is `(linear − quadratic(L,L))/2`. The homogeneous insertion
flow is `linear(F)/2 − quadratic(L,F)`.

For odd independent insertion sources, the fixed cross term has the extra factor
`(-1)^(parity(M)*parity(left source))` before the covariance. The helper `independentContractionIntegrand` integrates the actual
unconstrained joining momentum; replacing this by a momentum sum is incorrect for
independent local insertions. Block-permutation signs among multiple insertion labels
remain in the insertion module.

## Fixed tree and local marginal boundary data

`treeActionVertices e` is the actual physical YM cubic/quartic/ghost list plus nonlinear antifield
[vertices](GLOSSARY.md#perturbative-calculations). The coherent component convention is `sA=Dc`, `sc=−g[c,c]/2`, `s(cbar)=div A+iB`,
`sB=i div Dc`. Antifield vertices are −g[A,c]A‡, +g[c,c]c‡/2 and +ig[A,c]∂B‡ (the latter
after integration by parts). All actual color tensors come from e/B/bracket. `freeActionVertices G`
separately fixes the quadratic S0, including the free antifield terms. Those bilinear
terms are removed from [amputated](GLOSSARY.md#perturbative-calculations) Sint and are not free choices of its tree boundary.

The free gauge density is the Feynman 1/2 Σ(∂A)^2 presentation modulo total divergence.

Higher-loop `LocalMarginalData` contains finite local monomial lists only, with dimension four,
ghost number zero, even parity and the standard graph coupling order. It cannot supply
arbitrary momentum-dependent amplitudes. This is finite [renormalization](GLOSSARY.md#scales-and-renormalization)-scheme freedom;
admissibility is not the claim that arbitrary choices restore the gauge [Ward](GLOSSARY.md#graded-gauge-symmetry)
identities.

Local symmetry constraints test all ORDERED GRADED coefficient tensors extracted by
actual left differentiation, rather than commuting numerical [ghost](GLOSSARY.md#graded-gauge-symmetry) evaluation.
Color pullback uses actual Ad_g and inverse-dual antifield matrices. Full O(4) is
defined through preservation of the Euclidean quadratic form, not preservation of the Pi
sup norm. Momentum and gauge covector transformations automatically transform every
derivative index; antifields transform dually. Scalar antifields are dual densities with
|det|=1 on O(4).

## Analytic/domain safeguards and all-order parameter interfaces

The coefficient conditions require momentum smoothness, joint coupling/momentum
smoothness, actual combined-loop integrability, the pointwise scale derivative flow,
positive-scale continuity of every momentum [jet](GLOSSARY.md#graded-gauge-symmetry) up to the [UV](GLOSSARY.md#scales-and-renormalization) endpoint,
relevant [IR](GLOSSARY.md#scales-and-renormalization) regularity and actual one-sided zero IR limits. Endpoint values
alone would allow disconnected fake boundary data. Reduced background momenta are fixed
by eliminating the last component. Inserted amplitudes retain all independent momenta.

Irrelevant UV jets vanish; relevant IR jets vanish; [marginal](GLOSSARY.md#scales-and-renormalization) jets at µ equal the fixed
local action/scheme polynomial, with only independent background momentum derivatives
admitted. The vacuum functional is subtracted separately; its additive
source-independent I is excluded from the nonempty-leg flow.

`ScaleCouplingFamily G` is µ→g→FlowFamily G. `couplingCoefficient` and `uvJetCouplingCoefficient` are actual derivatives at g=0
of that same family, not new coefficient inputs. Root's beta/gamma extraction can use
`marginalJet` and `uvLocalJet` on the actual UV local action.

## Exact remaining work and interpretive limits

- Prove equality of this fixed coefficient convention with the primary graded
  functional flow and the earlier bare Wick coefficient construction. The
  source's unnamed c-sign constants have been replaced by explicit ordered
  conventions, not by assumed equivalence lemmas.
- Prove existence/uniqueness and the needed bounds of the triangular flow with
  these boundary equations. These are perturbative reference-construction
  results, not a proof of the massive nonperturbative theory.
- Prove that the full fixed [BV](GLOSSARY.md#graded-gauge-symmetry) action is pulled back coherently from the
  primary source conventions, including integration by parts/free-field
  redefinition and Fourier conventions. Source-agent BRST/graded algebra
  and [qft](GLOSSARY.md#quantum-fields-and-distributions) extraction modules provide the other interfaces.
- Add restored continuum quantum Ward identities/contact brackets and the
  actual UV limits; finite-cutoff local [counterterms](GLOSSARY.md#scales-and-renormalization) are allowed to break
  [BRST](GLOSSARY.md#graded-gauge-symmetry), as source 1511.09425 eq70 p16 explicitly requires.
- Prove equivalence under admissible finite scheme/gauge/regulator changes,
  including normalization of source [curvature](GLOSSARY.md#gauge-fields-and-observables) and coupling. No universal
  nonperturbative regulator/construction requirement is asserted.
- Define the position-space/Euclidean-to-physical analytic boundary relation
  and all-order [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) extraction from those renormalized flow limits.

This stage defines a central fixed coefficient prescription with explicit local scheme
constraints; it does not claim the whole renormalization or Jaffe–Witten specification
is complete.

## Coupling-order assembly

The finite background assembly `finiteLoopCoefficient` and `finiteLoopUVJetCoefficient` sum loops through
couplingOrder+2. The explicit `GraphHomogeneous` equation records the expected g^(n+2l−2) graph
law, and `backgroundCouplingPower_gt` proves the safe arithmetic bound. No theorem that the PDE forces
this graph homogeneity, nor that the excluded higher-loop coupling derivatives vanish,
is silently asserted. These remain supporting reference-construction proofs. Composite
insertions retain the loop index until their field-count-dependent bound is established.

## Source normalization correction during integration

The final local momentum derivative phase is **−i p**, consistent with the primary +i
extractor. A previous scratch version used +i p; do not copy it. The final `freeActionVertices`
includes all source-agent-confirmed quadratic free BV couplings and has all coupling
orders zero. The nonlinear flow tree boundary remains the separate `treeActionVertices`.
