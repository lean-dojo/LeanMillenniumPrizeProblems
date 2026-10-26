# Actual classical basis, local BV descent and same-system Legendre identities

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

The first question is whether classical observables admit a finite, coherent basis at
each dimension bound. The next is whether integration by parts gives well-defined
symmetry operations on equivalence classes of densities.

Read the basis construction before the quotient operations and [Legendre](GLOSSARY.md#perturbative-calculations) identities.
Classical basis availability does not imply a one-to-one correspondence with quantum
operators.

For terminology, start with the [relevant glossary section](GLOSSARY.md#gauge-fields-and-observables); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

These are central supporting results for the generated proposal. None is a
nonperturbative existence proof or an admission of the exact full target.

## Classical basis availability is proved

`ClassicalHomogeneousProjection` preserves the actual adjoint-G invariance of [curvature](GLOSSARY.md#gauge-fields-and-observables) polynomials under
engineering-degree projection. Actual translated connections and dilation show that
equality on all smooth connections is preserved degree by degree, including at arbitrary
points. Thus the degree projections descend to precisely the existing classical
observable quotient, rather than a freely chosen syntactic quotient.

`ClassicalFiniteSlices` proves finiteness of bounded [jet](GLOSSARY.md#graded-gauge-symmetry) coordinates and weighted monomials,
hence finite dimensionality of bounded invariant polynomial slices. `ClassicalGradedQuotient` gives the
actual evaluation quotient a vector-space structure and decomposes it as an internal
direct sum of finite homogeneous grades. `ClassicalFilteredBasis` constructs `availableFilteredBasis : OPE.FilteredBasis G` for every
actual G, with independent connection evaluations, finite coherent degree truncations,
[filtration](GLOSSARY.md#gauge-fields-and-observables)-preserving spanning and homogeneous representatives of their exact intrinsic
degree. This closes the classical basis-availability issue.

It imposes no classical/quantum isomorphism and does not establish availability of a
homogeneous quantum subtraction scheme.

`IntrinsicFiltration` realizes every intrinsic degree by a same-connection representative and
proves finite linear combinations preserve bounds. The actual local mixing support
therefore implies `mixingLabel_dimension`. `GeneratedMixingFiltration` derives the same bound for actual [gamma](GLOSSARY.md#scales-and-renormalization)
entries and finite loop assembly; no additional bound is required from the proof author
to obtain a mixing class in the input's Q-complex slice.

## Local and integrated BV operations

All eight field/antifield characteristics are now extracted from the actual [master action](GLOSSARY.md#graded-gauge-symmetry).
The final gauge-[antifield](GLOSSARY.md#graded-gauge-symmetry) formula uses finite ordered [vertex](GLOSSARY.md#perturbative-calculations) deletion and
integration by parts, rather than an assumed compact Euler equation. `FullBVActionParity` proves
this same full action is even; `FullBVPartialParity` proves the actual partial derivative sign
rules.

The arbitrary-polynomial induction and total-derivative modules work in the full
polynomial/exterior algebra. They prove ordinary derivative product rules, commutation,
parity preservation, and commutation with the actual evolutionary [ST](GLOSSARY.md#graded-gauge-symmetry) operator on
every local insertion. Thus ST preserves the span of divergences and defines `localSTFunctional`
on the fixed quotient. Exact multiindex integration by parts has the prescribed
(-1)^degree sign without interchanging possibly odd factors.

This proves evolutionary quotient descent. Identifying that induced map with the
integrated Euler antibracket, and proving the actual full master equation and
arbitrary-polynomial [nilpotency](GLOSSARY.md#graded-gauge-symmetry), remain separate work. Six of the eight species squares
have been established at the generator level; no missing two-species or full-[CME](GLOSSARY.md#graded-gauge-symmetry)
theorem is silently assumed.

## Background and local Legendre identities

`LegendreQuadraticGraded` expresses the actual gradient-quadratic term as the actual kernel-weighted
split convolution and proves its balanced statistics. The deterministic background
recursion therefore satisfies the all-order inverse equation using only source balanced
statistics and the free g=0 normalization. Empty mean roots follow from zero basic
[one-point](GLOSSARY.md#scales-and-renormalization) values at zero momentum. `LegendreFlowAdapters` derives the actual S lift and
generated-Q-exact local directional equations from S's single-insertion statistics and
its same background free law.

Thus the directional guards add no new restriction once that background condition is
supplied.

These proofs do not assert bulk free normalization or one-point vanishing from boundary
values alone. Such propagation needs a suitable growth-space uniqueness/equivariance
theorem for the actual flow hierarchy. The fixed source boundary [vertices](GLOSSARY.md#perturbative-calculations) have graph
[power counting](GLOSSARY.md#scales-and-renormalization); the missing step is its propagation to the whole bulk amplitude family.

## Remaining central scope

The classical basis choice is no longer an unproved extra restriction. The homogeneous
massless [Ward](GLOSSARY.md#graded-gauge-symmetry)-compatible QUANTUM scheme still needs a source adequacy argument.
Essential-coupling and local quantum [cohomology](GLOSSARY.md#graded-gauge-symmetry) classification, remaining full BV/CME
identities and cited-[QFT](GLOSSARY.md#quantum-fields-and-distributions) framework equivalences are still under review. Those are
specification fidelity issues, separate from the future nonperturbative Yang--Mills
proof.
