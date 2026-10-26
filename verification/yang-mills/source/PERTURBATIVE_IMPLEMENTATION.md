# Fixed Yang–Mills perturbative anchor: implementation and remaining work

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This early implementation fixes the classical action and bare perturbative coefficients.
“Bare” means before the full [renormalization](GLOSSARY.md#scales-and-renormalization) and cutoff-removal procedure; fixing these
coefficients is an initial step toward prescribed physical predictions.

Read the action and covariance construction first, then the normalization bridge. The
remaining-work list and zero-[switching](GLOSSARY.md#perturbative-calculations) example explain why the bare construction alone
is insufficient.

For terminology, start with the [relevant glossary section](GLOSSARY.md#perturbative-calculations); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

## Files and ownership

[PerturbativeYangMills.lean](../YangMills/PerturbativeYangMills.lean) and [Renormalization.lean](../YangMills/Renormalization.lean) are proposed new modules owned by the YM formalizer. They use
the pinned repository's actual compact simple group, tangent Lie bracket and invariant
positive form. No original repository files were edited by this agent. Temporary
dependency builds used only `/tmp` overlays of the pinned mathlib sources.

## What is fixed mathematically

The action is the Euclidean component formula `(1/4) Σμν B(dAμν+g[Aμ,Aν], dAμν+g[Aμ,Aν])`. The quadratic/cubic/quartic
decomposition is proved from linearity and symmetry of B. Cubic/quartic [vertices](GLOSSARY.md#perturbative-calculations) are
symmetrized multilinear seeds, with proved 6/24 diagonal factors. The ordered
antighost/gauge/ghost [vertex](GLOSSARY.md#perturbative-calculations) is obtained by expansion of `(∂cbar, ∂c+g[A,c])`. All color
contractions use the actual Lie bracket; a theorem shows the cubic color tensor cannot
vanish identically for a simple Lie algebra and positive B.

This is a classical interaction statement, not quantum Yang–Mills identification.

A B-orthonormal basis is an explicit coordinate [witness](GLOSSARY.md#reading-a-formalization) with its exact compatibility
condition. [Structure constants](GLOSSARY.md#gauge-fields-and-observables), [Casimir](GLOSSARY.md#gauge-fields-and-observables) contraction and the two-loop [beta](GLOSSARY.md#scales-and-renormalization) truncation are
functions of that basis and the actual bracket, not independently supplied numbers. The
first two coefficients use the usual canonical coupling normalization.
Basis-independence and the relevant scheme-invariance proofs are not yet implemented.

The exponential covariance is fixed by finite positive IR/UV scales, with the removable
p=0 value supplied explicitly. The Feynman-gauge matrix has oriented [ghost](GLOSSARY.md#graded-gauge-symmetry)
covariances of opposite sign. Its Fourier derivatives include all i/sign factors. A
recursive super-Wick formula fixes every pairing and [Koszul](GLOSSARY.md#graded-gauge-symmetry) crossing sign. Fixed
local action monomials generate coupling polynomials at all action vertices;
coefficients of the interaction exponential include (-1)^n/n! and are integrated against
a [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) switching function.

Normalization divides by the vacuum series via a triangular recursion. The order-zero
and exact normalization equations are proved, including that normalized vacuum
coefficients are 1,0,0,... .

Public bare coefficient functions require concrete propagator and coefficient
integrability obligations, rather than allowing nonintegrable kernels to be interpreted
through Lean's [totalized integral](GLOSSARY.md#reading-a-formalization). Those [analytic](GLOSSARY.md#analysis-and-asymptotics) obligations have not been proved universally
in this implementation.

The bare classical-observable insertion map is fixed, too. Potential variables include
commuting partial-derivative multiindices and a coupling variable. A genuine polynomial
derivation implements the total spacetime derivative. [Curvature](GLOSSARY.md#gauge-fields-and-observables) and its ordered
covariant descendants are generated using the actual structure constants. In source
normalization A_source=g A_canonical, `F_source=g F_canonical` and `D_source=∂+g[A_canonical,·]`; these factors are
retained. Substitution converts the full classical invariant curvature-[jet](GLOSSARY.md#graded-gauge-symmetry)
polynomial into a potential-jet polynomial, with explicit basis-to-tangent coordinate
conversion.

Its monomials then produce bare composite insertion kernels using the same Wick
covariance and action expansion. Thus these bare composite coefficients are not a freely
selected correspondence.

Local contact [counterterms](GLOSSARY.md#scales-and-renormalization) are actual continuous distributions: finite sums of signed
derivatives of delta, with a fixed derivative-order bound. A primitive
external-momentum Taylor subtraction is defined on the fixed one-loop ghost bubble
kernel. This isolated subtraction is not claimed to satisfy gauge [Ward](GLOSSARY.md#graded-gauge-symmetry) identities
or to be the full vacuum-[polarization](GLOSSARY.md#analysis-and-asymptotics) amplitude.

## Normalization bridge

The pre-existing `Connection.actionDensity` sums only μ<ν. The new canonical component action sums all
ordered μν and includes 1/4. The checked bridge is `yangMillsDensity B 1 (connectionJet A x) = (1/2) * A.actionDensity B x`. Consequently the existing
`euclideanAction` prefactor 1/(4g²) is half the ordered-component normalization for the same B
and g. It can be matched by doubling the old B or replacing its old coupling by
g/sqrt(2). This is a trace/coupling convention issue which must be exposed, not silently
ignored.

The source/canonical A rescaling and corresponding action equality are also proved
explicitly for nonzero g.

## Primary references

- Jaffe–Witten, *Quantum Yang–Mills Theory*, Section 1 (classical action),
  Section 4 printed p.6 and footnote 1 (observables, renormalization, UV/OPE).
- Itzykson–Zuber, *Quantum Field Theory*, source-cited reference [27],
  printed p.653 equation (13-81) for the two-loop pure-gauge beta coefficients;
  p.651 equation (13-75) for composite [operator mixing](GLOSSARY.md#scales-and-renormalization); p.677 equation
  (13-150) for [contact terms](GLOSSARY.md#short-distance-products-and-contact-terms) with extra composite insertions.
- Fröb–Holland, *All-order existence of and recursion relations for the
  operator product expansion in Yang–Mills theory*, arXiv:1603.08012:
  equations (2.13)–(2.17) (regulator/covariance), (2.20)–(2.27)
  (graded flow equations and boundary transport), (4.1)–(4.2)
  (composite extraction/normalization), Definition 3 ([OPE](GLOSSARY.md#short-distance-products-and-contact-terms) extraction),
  Theorems 4–6 (interaction insertion, quantum gauge identities and recursion).
  https://arxiv.org/abs/1603.08012

The exponential cutoff is an optional perturbative presentation. No assertion of
[regulator](GLOSSARY.md#scales-and-renormalization) universality or universal nonperturbative regulator choice is made. An
implementation-independent final admission condition would need a fidelity/equivalence
argument for this coefficient prescription.

## Exact central work still required

1. Prove that polynomial monomial extraction agrees with the fixed action
   seeds, that the algebraic observable substitution agrees with actual
   smooth connection jets, and that it descends through equality-on-connections.
   [Bosonic](GLOSSARY.md#quantum-fields-and-distributions) Wick permutation symmetry is also needed to remove support-list
   enumeration dependence. These are supporting equivalence lemmas, not
   Yang–Mills existence proofs.
2. Add loop-order/local [counterterm](GLOSSARY.md#scales-and-renormalization) insertions, including composite mixing,
   and impose their exact finite normalization conditions. Prove the
   all-order [UV](GLOSSARY.md#scales-and-renormalization) limit/extension exists in a specified distribution topology.
   Current delta-derivative vocabulary alone does not prescribe their allowed
   coefficients or prove an all-order renormalization theorem.
3. Formalize the full graded flow/forest construction and the quantum
   Slavnov–Taylor/BRST conditions. Fröb–Holland's interaction insertion is
   NOT simply the bare derivative of the action beyond lowest order. Its
   finite I^E coefficients and quantum BRST/antibracket must be constrained
   together; choosing them independently would reintroduce arbitrary predictions.
4. Use the resulting renormalized composite functionals to define fixed OPE
   coefficients by the source's recursive subtraction/extraction. Establish
   basis, gauge, regulator and scheme equivalence, including [finite mixing](GLOSSARY.md#scales-and-renormalization).
5. Supply a valid Euclidean/Minkowski analytic-boundary relation before
   comparing these kernels with [Wightman](GLOSSARY.md#quantum-fields-and-distributions) functions. The finite-[IR](GLOSSARY.md#scales-and-renormalization) Euclidean
   exponential cutoff does NOT directly yield a [tempered](GLOSSARY.md#quantum-fields-and-distributions) Minkowski kernel by
   naive substitution; its timelike continuation grows exponentially.
6. Only then relate the coefficients to the same nonperturbative physical
   composite fields, [stress tensor](GLOSSARY.md#scales-and-renormalization), [Hamiltonian](GLOSSARY.md#operators-and-spectrum) and asymptotic remainder bounds.

No existence proof of the massive continuum theory is being requested in these six
items. They are missing definitions, supporting equivalence facts, and fidelity
arguments within the user's specification task. These modules are therefore substantial
central progress, but **not a complete specification**.

## Additional adversarial restriction: switching is not a free final witness

The fixed finite-switching coefficient helpers permit any Schwartz switching function,
including zero. Choosing zero deletes all interaction insertions, even though the action
vertices themselves are nonzero. This is legitimate for a finite-switching perturbative
fragment but cannot be used as a final Yang–Mills prediction prescription. The final
construction must fix local switching equal to one on the relevant region and prove the
required switching-independence/algebraic [adiabatic](GLOSSARY.md#perturbative-calculations) limit or another justified removal
of switching, with translation invariance.

Root's admission must not simply existentially choose a switching function.
