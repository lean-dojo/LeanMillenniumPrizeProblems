# Internal fidelity argument for the proposed specification

> **Review status:** This is an internal AI-assisted assessment, not independent
> human expert validation. Its historical conclusions remain revisable;
> `FINAL` and `READINESS` in file names are workflow labels. See the
> [witness audit and open validation questions](WITNESS_AUDIT.md).

This document explains why the proposed Lean statement is intended to satisfy the source
problem. The argument follows one candidate from its [gauge group](GLOSSARY.md#gauge-fields-and-observables) and physical fields
through the prescribed perturbative coefficients to the same [stress tensor](GLOSSARY.md#scales-and-renormalization) and [Hamiltonian](GLOSSARY.md#operators-and-spectrum).

Read the physical framework first, then the action prescription and observable matching.
The final section distinguishes the meaning of the specification from proving that a
candidate exists.

For terminology, start with the [relevant glossary section](GLOSSARY.md#reading-a-formalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

Normative source: Jaffe–Witten, *Quantum Yang–Mills Theory*, §4, printed p.6, with §§1
and 3 and the mathematical frameworks it cites. The exact repository PDF and its hash
are recorded in [requirements.json](requirements.json). The detailed primary locations and clause crosswalk are
in [CURRENT_JW4_READINESS_CROSSWALK.md](CURRENT_JW4_READINESS_CROSSWALK.md). The independent resolved findings are in [FINAL_ADVERSARIAL_REVIEW.md](FINAL_ADVERSARIAL_REVIEW.md).

This is a reviewed sufficient presentation of the source problem. It is not a claim that
the source uniquely determines a Lean encoding. It supplies no Yang–Mills existence
proof, external expert endorsement or [CMI](GLOSSARY.md#notation-and-source-abbreviations) acceptance.

## One closed collection of mathematical objects

`YangMillsExistenceAndMassGap.{u}` requires, for every actual `CompactSimpleGaugeGroup.{u}`, a `FilteredGeneratedCandidate G`. There is no external
theory [predicate](GLOSSARY.md#reading-a-formalization) or presumed theorem parameter. The group has an actual compact
connected smooth Lie-group structure and simple nonabelian tangent Lie algebra; the same
bracket and invariant form determine the [color frame](GLOSSARY.md#gauge-fields-and-observables), [master action](GLOSSARY.md#graded-gauge-symmetry) and all group
coefficients. Finite central quotients are allowed. The source concerns local
observables on R4, so it does not separately prescribe line-operator sectors on
arbitrary bundles.

No assertion of equivalence of all global-form theories follows.

The physical [QFT](GLOSSARY.md#quantum-fields-and-distributions), composite map C, vacuum kernels, generated auxiliary families,
corrected representatives, coefficient limits, Ward/CS normalization, physical
asymptotics, local stress and physical Hamiltonian all occur in that single candidate.
Their relations are fixed formulas, limits and estimates. Required behavior cannot be
replaced by freely chosen Prop data. Constructing these objects and proving the
conditions is the future existence task, rather than missing specification meaning.

## Complete physical framework

The selected endpoint is a positive complete separable Hilbert [Wightman](GLOSSARY.md#quantum-fields-and-distributions) model on full
four-dimensional spacetime, with a common dense invariant domain, [tempered](GLOSSARY.md#quantum-fields-and-distributions) fields/full
[n-point](GLOSSARY.md#quantum-fields-and-distributions) kernels, adjoints, local commutativity, strongly continuous [Poincare](GLOSSARY.md#quantum-fields-and-distributions)
covariance, unique invariant vacuum and the joint positive-energy translation condition.
Every full [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) vacuum functional is tied to the actual field word, with
dense-tensor uniqueness. The translation spectral condition is stated by exact Fourier
annihilation outside the future cone; its matrix/operator forms are proved equivalent.

A separate [PVM](GLOSSARY.md#operators-and-spectrum) datum would not add missing spectral meaning.

The time Hamiltonian is [self-adjoint](GLOSSARY.md#operators-and-spectrum) with the full infinitesimal-generator domain and
action of those same translations. Its real spectrum is defined through actual
unbounded-operator resolvents. The mass is the supremum of positive gap intervals; the
interval set must be nonempty and bounded, so the mass is strictly positive and finite.
Continuous excitation spectrum is allowed. Neither an isolated particle nor confinement
is required.

The small Hilbert presentation preserves fields, domains, every QFT axiom, full vacuum
kernels, resolvents and mass through an actual [unitary](GLOSSARY.md#operators-and-spectrum). The remaining candidate
objects transport by the same conjugation, leaving all scalar generated coefficients and
limits unchanged. Countability and [bosonic](GLOSSARY.md#quantum-fields-and-distributions) observable covariance are justified by the
finite classical filtrations and observable [cyclicity](GLOSSARY.md#quantum-fields-and-distributions), not by Hilbert separability
alone. The [Lorentz](GLOSSARY.md#quantum-fields-and-distributions) cover's central kernel fixes every observable-word vector and
hence the physical space.

Strong fixed-vector field continuity follows from the usual weak matrix version by the
Schwartz-to-Hilbert closed graph theorem.

The standards comparison uses the primary coauthor Wightman exposition and
Osterwalder–Schrader I/II, as detailed in the crosswalk. A subsequent
[direct reading of Chapter 3 in the 2000 reissue](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026)
supersedes the earlier contents-only access. It records remaining convention
and equivalence questions and does not establish complete fidelity. The internal endpoint comparison
supports the chosen complete Minkowski formulation; requiring an additional [OS](GLOSSARY.md#notation-and-source-abbreviations)
construction would prescribe a method rather than fill an identified endpoint axiom.

## Actual Yang–Mills action and prescription

The auxiliary master density is the same actual nonabelian [curvature](GLOSSARY.md#gauge-fields-and-observables)-square action plus
the actual [ST](GLOSSARY.md#graded-gauge-symmetry) [gauge-fermion](GLOSSARY.md#graded-gauge-symmetry) variation and all characteristic [antifield](GLOSSARY.md#graded-gauge-symmetry) couplings,
modulo explicit total divergences. `masterDensity_gaugeFermion_curvature` and `fullAntifieldDensity_characteristic` establish that identity.
The actual full classical master equation and interacting [nilpotency](GLOSSARY.md#graded-gauge-symmetry) are proved on
coordinates, every [descendant](GLOSSARY.md#gauge-fields-and-observables), every polynomial and the [divergence quotient](GLOSSARY.md#graded-gauge-symmetry). No master equation
or nilpotency premise substitutes for their meaning.

The fixed [Gaussian](GLOSSARY.md#perturbative-calculations) coefficient prescription is compared with [FHH](GLOSSARY.md#notation-and-source-abbreviations) 1511.09425,
especially §III.C Eq.(91), Eq.(95) and Table II, and [FH](GLOSSARY.md#notation-and-source-abbreviations) 1603.08012 §2
Eqs.(2.25)–(2.27). The displayed FHH Eq.(67) [ghost](GLOSSARY.md#graded-gauge-symmetry) covariance is transposed
relative to the chronological derivative convention. The exact simultaneous covariance
transpose and reversal of written left partials give identical complete Gaussian and
flow contractions. The Fourier momentum-reflection identity uses the same master
polynomial, including antifields.

These are proved in `SourceCovarianceOrder`. The standard component [gauge-fixing](GLOSSARY.md#graded-gauge-symmetry) identity suffices; an
unclaimed literal pullback of every total form in Eq.(47) is not an additional
requirement.

The prescription fixes formal predictions; it is not a demand that the nonperturbative
theory be constructed by this [regulator](GLOSSARY.md#scales-and-renormalization) or perturbation method. Finite [marginal](GLOSSARY.md#scales-and-renormalization) data
represent normalization choices subject to full same-engine [Ward](GLOSSARY.md#graded-gauge-symmetry) and [CS](GLOSSARY.md#scales-and-renormalization)
identities. The candidate does not replace those identities by a finite diagnostic
projection. A theorem restoring every arbitrary choice, classifying all [cohomology](GLOSSARY.md#graded-gauge-symmetry) or
proving uniqueness of exact [beta](GLOSSARY.md#scales-and-renormalization) representatives is therefore not a missing
definition.

Original admissible canonical low/high insertion rows determine genuine C∞ amplitudes.
The proof transports actual projectors to coordinate jets, uses odd cancellation only at
the appropriate coincidence points, and combines the finite admissible-subindex
dichotomy with anchored smooth finite-[jet](GLOSSARY.md#graded-gauge-symmetry) [determinacy](GLOSSARY.md#analysis-and-asymptotics). It does not assume all
nonadmissible jets vanish at arbitrary momenta, [analyticity](GLOSSARY.md#analysis-and-asymptotics), or additional coordinate
[UV](GLOSSARY.md#scales-and-renormalization) clauses. The same high rows alone imply all higher coordinate jets vanish.

Actual single-insertion and inhomogeneous [oversubtraction](GLOSSARY.md#short-distance-products-and-contact-terms) uniqueness then fix the literal
triangular [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) extractor and its [cofinal](GLOSSARY.md#analysis-and-asymptotics) scalar limits for the same
action/normalization, including comparison of auxiliary families. Contact extensions are
not falsely declared universally unique.

Literal local vertex/Fourier/Taylor enumeration, all [arity](GLOSSARY.md#perturbative-calculations) and color sums,
[Koszul](GLOSSARY.md#graded-gauge-symmetry) signs and factorials recover the same finite Taylor polynomial. Computed
triangular normalization coefficients use the actual pointwise response matrix, rather
than a free mixing matrix. The integrated versus pointwise normalization comparison
retains their different source boundary conditions, conserving momenta and explicit
vacuum subtraction. It does not identify an integrated response with an uncorrected
pointwise insertion.

## Same observables, predictions and stress

The observable algebra contains arbitrary actual Ad-invariant curvature and
covariant-derivative polynomials, quotiented by identities on actual connections. The
real-linear map C gives finite combinations of the same QFT fields. It respects
identities, descendants, covariance, reality and the identity field, and its word states
alone are cyclic. Quantum relations and finite lower-degree mixing are allowed. Footnote
1 is respected as [filtration](GLOSSARY.md#gauge-fields-and-observables) guidance without imposing a classical/quantum bijection.

The physical all-arity OPE uses actual same-field kernels with separated [spectators](GLOSSARY.md#short-distance-products-and-contact-terms),
simultaneous engineering truncation remainders and separate coefficient singularity
bounds. Its prescribed perturbative coefficients come from the same extraction,
corrected lifts and weak continuum limits, with fixed local contact/partial-diagonal and
Wick relations. Coefficients cannot be chosen independently merely to fit a product.

All-order short-distance matching concerns those same analytically continued vacuum
words and OPE coefficients, after actual filtered [RG](GLOSSARY.md#scales-and-renormalization) transport and canonical
normalization. At each retained order the expansion is finite; the explicit remainder is
small relative to the prescribed running-coupling power as that coupling tends to zero.
No convergence of an infinite formal series at a fixed coupling or unique resummation is
asserted. Exact beta, [gamma](GLOSSARY.md#scales-and-renormalization) and stress completions are C∞ with the fixed jets;
nonperturbative flat contributions remain possible.

The former accidental [analytic](GLOSSARY.md#analysis-and-asymptotics) top orders were removed, including the stress numerator
condition that otherwise forced a convergent [germ](GLOSSARY.md#analysis-and-asymptotics). Genuine complex Wightman
[holomorphy](GLOSSARY.md#analysis-and-asymptotics) is retained.

The local stress field belongs to the same C and has degree four. Its conservation,
symmetry/covariance and charge limits on actual generator cores bind it to the same
physical translations and Hamiltonian. Its quantum [dictionary](GLOSSARY.md#notation-and-source-abbreviations), Ward [cocycle](GLOSSARY.md#graded-gauge-symmetry) and RG
equations use the same generated representatives and normalization. The tensor
dictionary uses active degree four; the [BRST](GLOSSARY.md#graded-gauge-symmetry) response has the separate degree-five
cutoff. Transport of the actual reference dictionary numerator forces the same physical
tensor at every running scale, as proved by `GeneratedStressFamily.field_transport`.

The trace coefficient uses beta and coupling from that same normalization. Both the
stress trace and curvature-square operator are centered by their actual same-vacuum
[one-point](GLOSSARY.md#scales-and-renormalization) functions. The equation is equivalent to the anomaly plus its computed scalar
identity term, with no independently chosen subtraction. This permits legitimate
identity mixing and does not impose zero absolute local vacuum stress. Charge-cutoff
transport preserves the same physical generators, so a positive-profile or vacuum-zero
hypothesis is not added.

Positive finite physical mass excludes a vacuum-only model but is not alone the
Yang–Mills identification. Composite-only cyclicity excludes an invisible [spectator](GLOSSARY.md#short-distance-products-and-contact-terms)
sector; the actual-G generated word/OPE matching and stress/charge relations supply the
group-specific content. A massive free field or a group index appended to an unrelated
QFT cannot pass by those elementary choices. The adversarial review found no complete
countermodel to the assembled conditions; that review is an argument about meaning, not
an existence proof.

## Admission and limits of the result

The exact target is a definition, not a proved theorem. Trusted activation, source-role
validation and a compiled raw all-group target-shape check control specification
admission. Future proofs undergo an independent checked-environment inspection of exact
theorem type/universe and transitive axioms. Coverage labels and submitted audit syntax
do not decide acceptance. The verification record distinguishes the completed definition
and supporting lemmas from the absent existence proof, [kernel verification](GLOSSARY.md#reading-a-formalization) of a future
submission, semantic interpretation and external acceptance.

No further missing mathematical meaning is identified by these resolved reviews.
Producing the full Ward/CS, continuum and physical witnesses remains the intended
existence problem. This is a complete reviewable formal proposal with a documented
sufficiency argument, not a certificate of community or Clay Mathematics Institute
acceptance.
