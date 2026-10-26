# Yang–Mills formalizer findings

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This early report constructs a language for classical [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) observables. Its main
distinction is between formal polynomials in [curvature](GLOSSARY.md#gauge-fields-and-observables) derivatives and their values on
actual smooth connections.

Read the [evaluation quotient](GLOSSARY.md#gauge-fields-and-observables) before the unresolved quantum requirements. A precise classical
observable algebra does not by itself identify any quantum field theory as Yang–Mills.

For terminology, start with the [relevant glossary section](GLOSSARY.md#gauge-fields-and-observables); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

## Substantive implementation

`work/ym/InvariantJetPolynomials.lean` proposes a new module importing existing `LocalObservables`. Its invariant ring is
the full multivariate polynomial ring in coordinates of all ordered curvature jets,
restricted by invariance under `Ad_g = d(h ↦ ghg⁻¹)_1` of the actual chosen compact simple group. No
independent adjoint representation is supplied by the proof author. The actual identity
and composition laws of these derivative maps are proved from manifold chain rules. This
replaces the pair-contraction-only restriction as a vocabulary for the classical sector.

All coefficient tensors and all finite polynomial degrees are allowed, including higher
invariant tensors unavailable in the old grammar.

[Engineering dimension](GLOSSARY.md#gauge-fields-and-observables) is a weighted degree of nonzero monomials, using weight `2 + number of covariant derivatives` for each
[jet](GLOSSARY.md#graded-gauge-symmetry) component. The module proves [filtration](GLOSSARY.md#gauge-fields-and-observables) closure under addition and
multiplication. Polynomial algebra performs coefficient cancellation before dimension is
measured. Evaluation uses the actual connection curvature/covariant-derivative
definitions. Equality on all smooth connections defines a [setoid](GLOSSARY.md#gauge-fields-and-observables), and an observable
quotient removes differential identities from the independent formal jet presentation.

The local-invariance theorem concerns the pointwise [adjoint action](GLOSSARY.md#gauge-fields-and-observables) on *jet assignments*. The
theorem on actual connections has an explicit equality premise for transformation of
every curvature jet. A proof that a smooth gauge transform of a connection satisfies
that equality has **not** been supplied. Do not describe this module as a completed
geometric gauge-invariance proof. Nor is a theorem that every invariant local
differential polynomial admits an invariant formal-jet representative supplied.

Compact-group averaging/polarization is the likely route to that
presentation-equivalence theorem.

## Central unresolved meanings, not missing existence proofs

1. **Renormalized correspondence.** The mathematical object should be a filtered
space of local composite quantum distributions acting on the same [Wightman](GLOSSARY.md#quantum-fields-and-distributions)
domain, tied to the invariant classical jet-polynomial space modulo its identities.
A basis change/finite mixing must be allowed. An arbitrary linear map from
classical polynomials to field indices can be zero or can label a free massive
[QFT](GLOSSARY.md#quantum-fields-and-distributions); it does not establish Yang–Mills identification. Required next work is a
fixed [renormalization](GLOSSARY.md#scales-and-renormalization)-equivalence relation on composite fields and its link to
Yang–Mills perturbation theory, without insisting on a naive bijection or on a
single scheme. This is a missing definition/fidelity argument.

2. **Group-specific perturbative predictions.** A family of arbitrary coefficient
distributions indexed by G does not fix their physical meaning. The nontrivial
anchor must be an explicitly defined perturbative pure Yang–Mills coefficient
system derived from the actual Lie bracket/invariant quadratic form and the
Yang–Mills action, with gauge fixing/ghost or equivalent gauge-invariant machinery,
renormalization ambiguities and relevant [Ward](GLOSSARY.md#graded-gauge-symmetry) identities controlled. The current
repository contains no such coefficient system or equivalence theorem. Merely
postulating [formal series](GLOSSARY.md#perturbative-calculations), [beta](GLOSSARY.md#scales-and-renormalization)-function signs, or an input called
`correctPredictions` leaves the free-QFT loophole open.

3. **[UV](GLOSSARY.md#scales-and-renormalization) asymptotics.** A precise condition needs dilation of same-theory [n-point](GLOSSARY.md#quantum-fields-and-distributions)
distributions, a specified topology (testwise versus bounded-set estimates),
logarithmic/running-coupling behavior and quantified orders/remainders. These
must be constrained by the fixed coefficient system above. Weak finite scalar
expansions alone do not fix the source-required UV behavior; the exact relation
between perturbative asymptotic series and short-distance distributions needs a
fidelity argument. Defining finite remainders is useful but not a solution.

4. **[OPE](GLOSSARY.md#short-distance-products-and-contact-terms).** A concrete formulation needs a specified collision domain, [smeared](GLOSSARY.md#quantum-fields-and-distributions)
composite operator products on a common invariant domain, coefficient
distributions for the classical-observable-indexed quantum fields, a dimension
filtration controlling truncation, [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) insertions/domain matrix elements,
and uniformity/order bounds. Coefficients must match the same fixed perturbative
Yang–Mills system modulo allowed [finite mixing](GLOSSARY.md#scales-and-renormalization). Choosing the actual product as
one coefficient, or permitting arbitrary singular coefficients, is vacuous.

5. **[Stress tensor](GLOSSARY.md#scales-and-renormalization).** A rank-two local field being symmetric/conserved alone is
insufficient: zero satisfies both. It must belong to the same renormalized
observable correspondence and produce the actual spacetime generators through
well-defined charges or Ward identities. Surface/time-cutoff limits, common
operator domains, and normalization belong in that definition. [Trace anomaly](GLOSSARY.md#scales-and-renormalization) and
its perturbative normalization require the fixed YM renormalization anchor.

6. **Nontriviality.** The existing non-vacuum/field-excitation equivalence is useful
QFT mathematics. It identifies Yang–Mills nontriviality only after the preceding
same-theory links exist. One must not enforce an unreferenced non-[Gaussian](GLOSSARY.md#perturbative-calculations)
criterion as a shortcut.

## Adversarial cases

A trivial quantum correspondence sends all nonconstant classical observables to zero. A
free massive QFT can be attached to every group and to any disconnected classical
invariant algebra. Either passes the existing QFT target and classical checks. The
proposed invariant ring makes the classical objects precise but **does not eliminate
either quantum counterexample**. No full target/admission unlock is justified by this
implementation.

## Interpretation and strengthening risks

- Coordinates use the given Lie algebra model, with equality on actual
connections eliminating coordinate-polynomial identities. Coordinate independence
and presentation equivalence remain supporting lemmas.
- Arbitrary polynomial invariants allow higher invariant tensors and tensor
components. Restricting to products of invariant quadratic pairings would weaken
the source's observable clause.
- Ordered derivative jets are redundant, not additional physical degrees of
freedom. Taking their polynomial algebra without quotient is not yet the actual
observable algebra; equality on all connections is the concrete quotient relation.
- Engineering filtration is classical source-informed vocabulary, not a new
mandatory exact quantum filtered isomorphism.
- No lattice, [regulator](GLOSSARY.md#scales-and-renormalization), particular representation, renormalization prescription,
confinement criterion or isolated-particle condition is imposed.

The checked module also proves that the derivative-defined adjoint maps satisfy the
identity/composition laws, and that the induced jet maps obey the same laws. The
evaluation quotient uses the kernel setoid of the concrete connection evaluation
function; its evaluation therefore descends without an extra well-definedness
assumption. The quotient dimension filtration is existence of a dimension-bounded
representative, with monotonicity and exhaustiveness proved. This avoids assigning a
syntactic degree to a quotient class arbitrarily.
