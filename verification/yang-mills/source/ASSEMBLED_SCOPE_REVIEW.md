# Assembled generated candidate: scoped source-fidelity review

> **Source-access update, 22 October 2026.** The book-access limitation recorded
> below describes this historical review. Chapter 3 of the supplied 2000 reissue
> has since been [read and compared](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026).
> That comparison records remaining obligations; it does not validate all earlier conclusions.

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review asks what must be checked before a collection of equations can serve as a
specification. Requiring witnesses to satisfy the full equations is different from
proving that those witnesses exist, and different again from claiming that every
normalization scheme is equivalent.

Start with the conditional verdict and its smoothness correction. Then follow the
action, normalization, observable and stress links before reading the [carrier](GLOSSARY.md#operators-and-spectrum) and
group conventions.

For terminology, start with the [relevant glossary section](GLOSSARY.md#scales-and-renormalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This review concerns the current [PRIMARY](GLOSSARY.md#notation-and-source-abbreviations) `FilteredGeneratedCandidate`, `GeneratedScaleNormalization`, `FilteredQuantumRG`,
`LocalWardFlowFamily`, `CompositeFields`, `StressTensor`, and the current [source/CANONICAL_TRACE_QFT_REVIEW.md](CANONICAL_TRACE_QFT_REVIEW.md). It supersedes neither
the proof audit nor the admission policy. The two hypotheses of this review are that the
actual canonical high-[UV](GLOSSARY.md#scales-and-renormalization) [determinacy](GLOSSARY.md#analysis-and-asymptotics) application and literal reduced
Fourier/Taylor recovery are completed, rather than replaced by stronger
independent-coordinate boundary conditions.

## Concrete correction discovered after the first pass

The audit subsequently found 45 occurrences of `ContDiff ℝ ⊤` or `ContDiffOn ℝ ⊤` in the pinned
WithTop-ℕ∞ calculus API. These impose [analyticity](GLOSSARY.md#analysis-and-asymptotics), not C-infinity. They must be replaced
by `∞`; the exact stress numerator plus all-order [jet](GLOSSARY.md#graded-gauge-symmetry) condition otherwise
imposes an unjustified convergent [germ](GLOSSARY.md#analysis-and-asymptotics). See the [smoothness review](SMOOTH_ORDER_REVIEW.md) and [pre-patch inventory](smooth_order_audit.json). The
positive scoped verdict below is conditional on that correction and its dependent
rebuild; it is not an acceptance of the unpatched candidate.

Genuine [Wightman](GLOSSARY.md#quantum-fields-and-distributions) [holomorphic](GLOSSARY.md#analysis-and-asymptotics) continuation and inner ℕ∞-top finite-order inequalities
are unaffected.

## Verdict

The assembled simultaneous conditions can serve as a concrete fixed prescription for the
required perturbative predictions. I found no further counterexample or precise missing
same-object binding which requires a new universal [cohomology](GLOSSARY.md#graded-gauge-symmetry) classification,
[beta](GLOSSARY.md#scales-and-renormalization)-uniqueness, quantum injectivity, or perturbative response-existence theorem.
Those must not remain generic readiness gates after the concrete [dictionary](GLOSSARY.md#notation-and-source-abbreviations) is checked.

A source comparison is still necessary, but its scope is narrow: explain why the
explicitly fixed finite-order covariance/contraction, [vertices](GLOSSARY.md#perturbative-calculations), [canonical projectors](GLOSSARY.md#analysis-and-asymptotics), mixed
boundary normalization, insertion recursion, and Wick continuation are a presentation of
pure Yang--Mills perturbation theory. This is a comparison of specified formulae, not a
demand to construct a solution satisfying all [Ward](GLOSSARY.md#graded-gauge-symmetry) identities. If the existing
exact bridge proofs and the primary formula comparison cover that dictionary, no further
unspecified “fixed-scheme equivalence” obstruction has been identified here.

The record should then say that, rather than perpetually requiring an unnamed additional
equivalence theorem.

## What the source asks and what its interpretation does not determine

Jaffe--Witten, printed p.6, §4, requires the local observable correspondence,
short-distance agreement with [asymptotic freedom](GLOSSARY.md#scales-and-renormalization) and perturbative [renormalization](GLOSSARY.md#scales-and-renormalization), [stress tensor](GLOSSARY.md#scales-and-renormalization),
[OPE](GLOSSARY.md#short-distance-products-and-contact-terms), and its prescribed singularities. Its footnote rejects a naive
classical/quantum bijection. It does not select one [regulator](GLOSSARY.md#scales-and-renormalization), finite renormalization
scheme, [ghost](GLOSSARY.md#graded-gauge-symmetry) presentation, or exact resummation of a divergent formal expansion.
The surrounding §3 specifies the physical [QFT](GLOSSARY.md#quantum-fields-and-distributions) and the actual translation
dynamics. These claims are read directly in the repository's pinned PDF, also available
at https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf .

Consequently the relevant statement is that there exists one simultaneous presentation
satisfying the prescribed predictions. It is not that every presentation of every valid
theory already has the selected auxiliary coordinates. Conversely, choosing a regulator
does not justify arbitrary new physical predictions: its action/normalization dictionary
must identify the usual perturbative coefficients. A fixed sufficient presentation needs
a defensible sufficiency argument; it does not need a bijection between all
formalizations or uniqueness of all normalization witnesses.

## Why the current conditions bind actual predictions

The engine contains the actual G bracket, fixed free covariance and fixed classical
interaction/antifield vertices. Its [marginal](GLOSSARY.md#scales-and-renormalization) data are finite local [counterterms](GLOSSARY.md#scales-and-renormalization) with
explicit degree, ghost, parity, symmetry and graph guards; they are not a [predicate](GLOSSARY.md#reading-a-formalization)
defining a substitute theory. Canonical projectors and literal Fourier recovery identify
their local coefficients with the same ordered amplitudes. Triangular flow uniqueness
then determines the amplitudes for the supplied finite normalization data, including
canonical pointwise insertion boundaries.

`LocalWardFlowFamily` binds the continuum, corrected lift, Q, contact maps, connected/moment data
and physical invariant words to this same engine. The full Ward and extension equations
are actual coefficient identities and limits. No cohomology theorem is being silently
used to infer these equations from a smaller set of projected rows. Their satisfaction
is part of the [witness](GLOSSARY.md#reading-a-formalization) one must eventually construct; proving it for a candidate is
the existence problem, not missing meaning in their definition.

`GeneratedScaleNormalization.same_scale_insertion` is the full same-[Gamma](GLOSSARY.md#scales-and-renormalization) [CS](GLOSSARY.md#scales-and-renormalization) identity, with the same corrected
insertions and generated differential. Beta, field coefficients, primitive and mixing
are simultaneous solutions of that equation, with explicit graph order. Physical
beta/gamma jets are computed from these coefficients, including the fixed actual
classical basis coordinates and Wick conjugation. They are therefore constrained
coordinate witnesses, rather than independently supplied prediction tables. A proof that
these witnesses are unique would be useful only if uniqueness were claimed.

A classical or quantum null direction does not itself show that unrelated physical
asymptotics satisfy the full assembled conditions.

The same physical running/frame data occur in actual operator transport, all-order OPE
matching and actual vacuum-word matching. The latter prevents an unrelated massive
Wightman model from being attached merely through formal OPE names. The nonperturbative
coefficients remain witnesses with all-order asymptotics, as they should: perturbative
jets do not determine beyond-all-orders contributions. No unique resummation is
prescribed.

Stress uses the same C fields, actual Hamiltonian/momentum charge limits, generated
local stress lift, same [running coupling](GLOSSARY.md#scales-and-renormalization) and mixing. Both sides of its trace identity are
centered by the same actual vacuum. The remaining identity coefficient is computed, not
chosen. This is the appropriate vacuum-energy-insensitive trace relation. It is not
legitimate to restore the former extra requirement of zero absolute local vacuum stress.
In the source connection convention its coefficient is beta/(2 g^3); replacing F_source
by g F_canonical gives beta/(2g) times the canonical [curvature](GLOSSARY.md#gauge-fields-and-observables) square, the familiar
normalization.

This convention must remain consistent with the actual insertion dictionary, rather than
inferred from a name.

## Exact finite-order comparison which is relevant

The primary flow prescription supplies a direct comparison, without a universal local
cohomology theorem. [FHH](GLOSSARY.md#notation-and-source-abbreviations) 1511.09425, §III.C, printed pp.20--22, Eq.(91), Eq.(95)
and Table II, and [FH](GLOSSARY.md#notation-and-source-abbreviations) 1603.08012, §2, printed pp.12--14, Eqs.(2.25)--(2.27),
identify the finite-cutoff connected-[amputated](GLOSSARY.md#perturbative-calculations) flow and mixed normalization. In
particular FH printed p.14 fixes [irrelevant jets](GLOSSARY.md#scales-and-renormalization) at the UV endpoint, marginal jets at
positive mu and zero momenta, and relevant point-insertion jets at mu; integrated
background/response relevant jets use the distinct massless [IR](GLOSSARY.md#scales-and-renormalization) conditions.

The source explicitly relates these to UV bare local counterterms by integrating the
already-triangular flow, then momentum Taylor reconstruction. Our canonical
admissible-jet reconstruction is precisely the nontrivial graded adequacy step in that
argument; it must not be replaced by all-coordinate vanishing premises.

The remaining dictionary review should record: (1) the same ordered-left [Grassmann](GLOSSARY.md#graded-gauge-symmetry)
convention yields the actual contraction signs and factorials; (2) the master vertices
are the source shifted-B gauge-fixed action, not only its physical cubic/quartic subset;
(3) the mixed boundaries and actual canonical extractor are exactly the selected finite
normalization; (4) the local insertion and OPE triangular extraction uses those same
amplitudes; (5) the raw Gamma/source-normalization compensation and Wick phases match
the conventions used by the CS and physical-word equations.

Existing same-action proofs may discharge these items; listing them does not assert that
an additional formal textbook definition has to be invented and proved isomorphic.

FHH's finite Ward-restoration arguments and [IZ](GLOSSARY.md#notation-and-source-abbreviations)'s stability/CS discussion explain
why such equations are appropriate. Their existence/classification proofs need not be
reconstructed merely to state these full equations. If one instead removed the full
equations and inferred them from a few finite coordinates, the necessary restricted
classification/restoration lemma would then become a real obligation. That is not the
current design.

## Type0 transport extends to the whole candidate without new analysis

Let e:K ~=_unitary H be the already constructed small Hilbert carrier and let J:D_K ->
D_H be its induced linear equivalence of common domains. Use the already transported
QFT, same group/engine/ward/lift/normalization, same field-index labels and same C
coefficient vectors. Then, exactly,

    C_K(p,f) = J^-1 C_H(p,f) J,
    K_K(v,w,F) = K_H(Jv,Jw,F).

The latter defines every multi-kernel. Keep scalar OPE coefficients, Euclidean
distributions, continuations, running/frame matrices and stress labels unchanged.
Transport stress generators by the already proved full unbounded-operator conjugation,
and its charge core by J^-1. Domain actions, word vectors, adjoints and all weak
charge/continuum/OPE limits are conjugate or have identical scalar values, because e
preserves inner products and limits. Trace centering has identical vacuum [one-point](GLOSSARY.md#scales-and-renormalization)
functions.

The physical vacuum word equality uses the same conjugated vacuum. Graph cores and
spectra are already preserved by the operator carrier transport.

Thus no new [analytic](GLOSSARY.md#analysis-and-asymptotics) or physical equivalence is missing for the outer candidate. A
complete Lean candidate-transport function would package these routine substitutions and
is needed to advertise a kernel-checked theorem with that name; it is not a new fidelity
condition or a new existence input. One can choose K and these conjugated observables
from the outset.

## Gauge-group universe and conventions

The group binder is [universe-polymorphic](GLOSSARY.md#reading-a-formalization), so it does not restrict group carriers to Type0.
Finite-dimensional real charts, Hausdorff and second countability are the ordinary
finite-dimensional Lie-group presentation; compactness gives a finite chart subcover, so
second countability does not exclude the usual compact finite-dimensional groups. The
explicit C^3 instance is a redundant smoothness consequence. Lie-algebra simplicity
allows finite central quotients and is appropriate, unlike abstract-group simplicity.

Connectedness uses the conventional compact simple Lie-group meaning; disconnected
compact extensions of a simple identity component are not silently being asserted
equivalent. No simply-connectedness or particular matrix realization is imposed.

## What must not be claimed

This is not an existence proof, nor external expert/CMI certification. Full [45] axiom
chapter access remains explicitly qualified in the separate QFT review; the primary
coauthor/OS comparison is not a false full-book quotation. The Fourier-support
definition already has exact standard meaning and does not need an extra [PVM](GLOSSARY.md#operators-and-spectrum)
datum. Missing formal consequence proofs are not automatically missing definitions. Once
the canonical and literal recovery bridges and the concrete dictionary above are
reviewed, I have no additional necessary equivalence gap to name from the assembled
conditions examined here.
