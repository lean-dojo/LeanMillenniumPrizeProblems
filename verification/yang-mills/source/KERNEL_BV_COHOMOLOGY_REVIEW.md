# Full kernels, actual BV identities and the quantum observable quotient

> **Source-access update, 22 October 2026.** The book-access limitation recorded
> below describes this historical review. Chapter 3 of the supplied 2000 reissue
> has since been [read and compared](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026).
> That comparison records remaining obligations; it does not validate all earlier conclusions.

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review covers three supporting constructions: full correlation distributions, the
action-derived gauge differential, and the quotient defining quantum observable classes.
It distinguishes specifying full kernels directly from deriving them from fewer
continuity assumptions.

Read the kernel and source-audit sections before the [analytic](GLOSSARY.md#analysis-and-asymptotics) proof obligations. The
[BV](GLOSSARY.md#graded-gauge-symmetry) and [cohomology](GLOSSARY.md#graded-gauge-symmetry) sections then explain what is proved algebraically without
claiming a physical [ghost](GLOSSARY.md#graded-gauge-symmetry)-state construction.

For terminology, start with the [relevant glossary section](GLOSSARY.md#quantum-fields-and-distributions); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

These are fixed definitions and supporting proofs, not a Yang--Mills existence proof.
The full target remains unadmitted pending the specific remaining fidelity obligations.

## Full Wightman kernels of the same theory

`GeneratedCandidate.vacuumKernels` supplies continuous full-[Schwartz](GLOSSARY.md#quantum-fields-and-distributions) kernels for all actual Q component words.
Their tensor values are the existing same-H operator vacuum expectations. Pointwise
tensor-product equations and density make the kernels unique, as proved in `WightmanVacuumKernels`.
An unrelated correlator cannot satisfy that dense-span identification. The existing
C-word kernels separately identify with finite combinations of those same operators.

`WightmanNPointContinuity` proves actual complex multilinearity and separate continuity at every slot,
using reverse adjoints on the same invariant domain. `WightmanVacuumPositivity` identifies
adjoint-concatenated word correlations with actual Hilbert inner products and proves
their finite [Borchers positivity](GLOSSARY.md#quantum-fields-and-distributions). No boundedness or essential self-adjointness of [smeared](GLOSSARY.md#quantum-fields-and-distributions)
fields is required.

## Primary author/source audit

Streater's [author exposition](https://www.scholarpedia.org/article/Wightman_quantum_field_theory), sections “The [Wightman](GLOSSARY.md#quantum-fields-and-distributions) Axioms for a Scalar Field” and “The
Wightman Distributions”, identifies the common-domain, weak-continuity and [tempered](GLOSSARY.md#quantum-fields-and-distributions)
full-kernel formulations, including the [nuclear](GLOSSARY.md#quantum-fields-and-distributions)-kernel step. Its scalar exposition is
not a proof of the full multiplet/framework equivalence here. The cited book's
[publisher record](https://www.jstor.org/stable/j.ctt1cx3vcq) locates chapter 3 at pp.96–133; full chapter access was unavailable in this
session. No complete direct audit of that chapter is claimed.

| Source quantity | Concrete proposed condition | Supporting boundary |
|---|---|---|
| Positive separable [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions) | WightmanAxioms.complete/separable and actual inner product | Small-model/universe transport |
| Covariant common-domain fields | WightmanData.field/domainAction and actual adjoint/covariance equations | Countable [bosonic](GLOSSARY.md#quantum-fields-and-distributions) multiplet presentation |
| Tempered distributions | Full actual-word continuous Schwartz kernels | Standard tensor realization/density and economical-axiom redundancy |
| Spectrum in the forward cone | Actual integrated [unitary](GLOSSARY.md#operators-and-spectrum) translation test equation | Joint spectral-measure support equivalence |
| Locality and [cyclic vacuum](GLOSSARY.md#quantum-fields-and-distributions) | Same-domain spacelike commutation and actual word span density | Test/kernel and analytic [tube](GLOSSARY.md#analysis-and-asymptotics) equivalences |

The direct kernel presentation fixes the multipoint meaning. Deriving it as a redundant
consequence of the economical original single-field axioms still requires additional
library analysis, summarized below.

## Actual n-point continuity support

[YangMills/WightmanNPointContinuity.lean](../YangMills/WightmanNPointContinuity.lean) proves the reverse-order adjoint identity on the existing common invariant
domain, linear and continuous dependence of the actual vacuum expectation on an
arbitrary interior slot, and an actual complex multilinear map at every [arity](GLOSSARY.md#perturbative-calculations). Its
values are proved equal to the existing vacuumNPoint; no candidate may supply different
[n-point](GLOSSARY.md#quantum-fields-and-distributions) values. The final theorem gives separate continuity explicitly for every
Fin-indexed test-function slot.

The file strict-compiles with autoImplicit=false and warningAsError=true in the pinned
project. Audited central theorems use only propext, Classical.choice and Quot.sound. The
spectral module is frozen and was not edited during this work.

The precise remaining supporting bridge is:

1. Establish that the actual Schwartz seminorm topology is Frechet/complete (and hence Baire/barrelled). The pinned SchwartzSpace implementation supplies WithSeminorms and FirstCountableTopology, but `#synth CompleteSpace YangMills.TestFunction` fails. No completeness theorem was found in its source. This is a missing library proof, not evidence that Schwartz space is mathematically incomplete.
2. Prove the standard promotion from separately continuous finite multilinear scalar maps on these [Frechet](GLOSSARY.md#analysis-and-asymptotics) spaces to joint continuity. Pinned mathlib has the [barrelled](GLOSSARY.md#analysis-and-asymptotics) Banach-Steinhaus theorem, but no ready general separately-continuous multilinear promotion was located. No additional physical assumption is justified by this library gap.
3. Prove the Schwartz nuclear kernel correspondence: the jointly continuous multilinear functional on n copies of S(R^4) extends uniquely to a continuous linear functional on S(R^(4n)), with [tensor-test](GLOSSARY.md#quantum-fields-and-distributions) values fixed by the actual vacuum words. Neither a Schwartz nuclearity/completed-projective-tensor isomorphism nor this kernel theorem was found in the pinned distribution modules. Density/uniqueness and the continuity estimate are part of the theorem, not freely chosen multipoint data.

These steps would complete the specific multipoint tempered-distribution adequacy
argument. They do not involve constructing a Yang--Mills model or proving the
[mass gap](GLOSSARY.md#operators-and-spectrum).

## Direct cited-standard presentation

The additional frozen module [YangMills/WightmanVacuumKernels.lean](../YangMills/WightmanVacuumKernels.lean) supplies a direct alternative to waiting for the
preceding library derivation. It requires actual full-Schwartz continuous kernels for
all Q component words, fixed pointwise product [tensor tests](GLOSSARY.md#quantum-fields-and-distributions), tensor-span density, and
exact equality to Q's existing vacuum expectations on every tensor. The module proves
uniqueness of tensor tests and full kernels, an extensional uniqueness theorem against
any proposed continuous kernel, and coverage of every existing finite field word.

It strict-compiles without new axioms.

Adding this concrete [witness](GLOSSARY.md#reading-a-formalization) to the proposed candidate makes multipoint temperedness
an explicit standard condition. It does not let the candidate choose correlation values,
and it introduces no Gaussianity/particle/scheme assumption. Its fidelity justification
is that standard Wightman n-point distributions already have precisely these continuous
Schwartz kernels and tensor values. Standard tensor existence/density and the kernel
correspondence remain supporting source-equivalence mathematics. They no longer leave
the *meaning* of candidate multipoint temperedness unstated.

This direct presentation does not by itself prove its redundancy from the economical
original single-field continuity axioms.

## Actual interacting BV scope

The four nonlinear basic transformations are derived from the fixed actual [master-action](GLOSSARY.md#graded-gauge-symmetry)
[vertices](GLOSSARY.md#perturbative-calculations). The shifted-[antighost](GLOSSARY.md#graded-gauge-symmetry) and nonlinear ghost [nilpotency](GLOSSARY.md#graded-gauge-symmetry) identities now follow
from that same action, the actual pointwise product rule, odd-[jet](GLOSSARY.md#graded-gauge-symmetry) anticommutation
and actual Lie color Jacobi. The auxiliary [antifield](GLOSSARY.md#graded-gauge-symmetry) image B-i barc-dagger is also
extracted from those vertices. Interacting A/B nilpotency, other antifield equations,
promotion to arbitrary [superjet](GLOSSARY.md#graded-gauge-symmetry) polynomials and the full CME/divergence descent are
still in progress.

## Actual quantum cohomology

`FilteredQuantumCohomology` uses full formal hbar power series of the same physical generated Q
coefficients. Its differential raises degree and ghost number by one and flips parity;
the two rectangular maps retain all allowed intermediate monomials. Their composition is
proved zero from the actual Filtered/Nilpotent coefficient equations. Thus the exact
image lies in the [cocycle](GLOSSARY.md#graded-gauge-symmetry) kernel, giving a real quotient module H0. Existing
corrected lifts are proved closed and define actual quotient classes.

No injectivity, surjectivity or classical/quantum isomorphism is asserted. Identifying
formal classes with physical operators still uses the separate same-C UV/Wick/word
bridges; no nonperturbative ghost Hilbert quotient is inferred.

## Remaining general Legendre chain rule

Actual flow jets preserve graded statistics and mean-field roots use the background law
only on [balanced momenta](GLOSSARY.md#notation-and-source-abbreviations). Sorted block permutations and their actual selected indices/momenta
are computed. The weighted [Koszul](GLOSSARY.md#graded-gauge-symmetry) sign is proved equal to the ordinary sign on the
odd-position subsequence. The universal external-permutation factorization and its full
finite-sum reindexing are still being completed before removing any computed-inversion
guard.
