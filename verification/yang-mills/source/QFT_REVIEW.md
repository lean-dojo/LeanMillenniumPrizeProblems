# QFT and physical-Hamiltonian review, 2026-10-20

> **Source-access update, 22 October 2026.** The book-access limitation recorded
> below describes this historical review. Chapter 3 of the supplied 2000 reissue
> has since been [read and compared](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026).
> That comparison records remaining obligations; it does not validate all earlier conclusions.

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review asks whether the physical framework gives the intended meaning to fields,
time evolution and the [mass gap](GLOSSARY.md#operators-and-spectrum). The critical operator issue is that the [Hamiltonian](GLOSSARY.md#operators-and-spectrum)
must be the full generator of the same time translations.

Read the concrete conditions and supporting lemmas before the adequacy table. The
[QFT](GLOSSARY.md#quantum-fields-and-distributions) conditions are necessary; identifying this theory as Yang–Mills requires
additional group-dependent conditions.

For terminology, start with the [relevant glossary section](GLOSSARY.md#operators-and-spectrum); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

Scope: [QFT/Spacetime.lean](../YangMills/QFT/Spacetime.lean), [QFT/Operator.lean](../YangMills/QFT/Operator.lean), [QFT/Wightman.lean](../YangMills/QFT/Wightman.lean), [Spectrum.lean](../YangMills/Spectrum.lean), and the consumers [Nontriviality.lean](../YangMills/Nontriviality.lean),
[QuantumCorrelations.lean](../YangMills/QuantumCorrelations.lean). This is a mathematical review of the actual definitions, not a certification
of the unimplemented Yang–Mills [predicate](GLOSSARY.md#reading-a-formalization).

## Existing concrete content

* The test space is [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) functions on actual R^4. Its topology is fixed by mathlib. Causality uses (+---). [Lorentz](GLOSSARY.md#quantum-fields-and-distributions) transformations preserve the metric, orientation and future cone; the topology of [Poincaré](GLOSSARY.md#quantum-fields-and-distributions) transformations is induced by the actual matrix entries and translation coordinates.
* A single positive-definite complex [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions) carries all fields and the vacuum. Completeness and separability are fixed obligations. Every field has the same dense invariant complex-linear domain, with vacuum contained in it. Field products and correlation functions therefore concern the same domain and vacuum.
* Adjoint conjugation is a specified index involution; the common-domain inner-product identity has the correct conjugate-test convention. It does not incorrectly require each field to be bounded or [self-adjoint](GLOSSARY.md#operators-and-spectrum).
* The [unitary](GLOSSARY.md#operators-and-spectrum) action is strongly continuous and satisfies actual identity and composition laws. Domain actions agree pointwise with the same unitary action. Field multiplets transform covariantly under finite-dimensional continuous representations, trivial on translations. Pullback and conjugation functions are characterized pointwise, not freely chosen meanings.
* The spectrum condition uses the actual unitary translation action and an explicitly written Fourier kernel. Explicit integrability avoids the zero value of mathlib's [totalized integral](GLOSSARY.md#reading-a-formalization) making a nonintegrable expression vacuously vanish.
* The physical Hamiltonian is densely defined and self-adjoint in the full graph-of-adjoint sense. Its [resolvent](GLOSSARY.md#operators-and-spectrum) consists of bounded everywhere-defined two-sided inverses with image in the actual operator domain. Continuous spectrum is included. Its domain is exactly the set of vectors differentiable under time evolution at zero, and its action is the corresponding derivative divided by i. This is a materially stronger connection than an unrelated positive operator supplied alongside a QFT.
* The mass definition demands a nonempty set of positive admissible gaps and boundedness above before using a real supremum. It excludes vacuum-only spectrum and does not require a one-particle eigenvalue.

No immediate counterexample was found to the *same-Hamiltonian* linkage. These clauses
still permit ordinary massive free [Wightman](GLOSSARY.md#quantum-fields-and-distributions) theories, as they must: Yang–Mills
identification belongs to the missing separate same-theory identification and [UV](GLOSSARY.md#scales-and-renormalization)
clauses.

## New supporting lemmas

Proposed full replacement files are `work/qft/Spectrum.lean` and `work/qft/Wightman.lean`; the only modifications
are additional supporting theorems:

1. `hasPositiveFiniteMass_iff`: the finite-mass condition is equivalent to existence of a positive gap and at least one positive **spectral value**; no eigenstate assumption is introduced.
2. `mass_le_positive_spectral_value`: each positive spectral energy is an upper bound on the mass (`mass σ ≤ E`).
   See the [implemented inequality](../YangMills/Spectrum.lean).
3. `mass_isMassGap`: the source's supremum mass is itself an admissible positive gap.
4. `WightmanAxioms.field_graph_limit_zero`: [smeared](GLOSSARY.md#quantum-fields-and-distributions) fields are closable in the sequential graph sense. If vectors in the common domain converge to zero and their field images converge to w, then w=0. The proof uses the specified adjoint relation and density; no completeness or spectral theorem is assumed for this lemma.
5. `WightmanAxioms.hamiltonian_domain_unique`: two admissible QFT data sets with identical time translations have the same Hamiltonian domain.
6. `WightmanAxioms.hamiltonian_action_unique`: their actions coincide on that domain, by uniqueness of the derivative. This excludes substituting a convenient restriction of the actual generator.

Both proposed files were individually compiled with the pinned `lake env lean -DautoImplicit=false -DwarningAsError=true`. No new
axioms, `sorry`, placeholders, [witness](GLOSSARY.md#reading-a-formalization)-chosen predicates or changes to the
necessary target were introduced. Integration must rebuild the repository and run its
[transitive axiom](GLOSSARY.md#reading-a-formalization) inspector; an individual-file compile does not replace that audit.

## Adequacy gaps: definitions versus supporting mathematics

| Clause | Classification | Exact remaining work |
|---|---|---|
| Physical Hamiltonian domain and action | Supporting equivalence lemmas partly supplied | Prove generator uniqueness (supplied); no existence proof of any theory is demanded by specification readiness. |
| Full self-adjoint spectrum | Supporting equivalence | Relate the explicit graph-adjoint and resolvent definitions to standard closed unbounded-operator definitions; derive real spectrum rather than leave it as a redundant fixed proof obligation. The current obligation itself is concrete and not a placeholder. |
| Spectrum condition | Supporting equivalence | Derive equivalence between the written Fourier-test annihilation condition and support of the translation spectral measure in the closed forward cone. Fix Fourier normalization/sign and prove the Bochner kernels are integrable. These are [analytic](GLOSSARY.md#analysis-and-asymptotics) equivalence theorems, not Yang–Mills existence. |
| [Tempered](GLOSSARY.md#quantum-fields-and-distributions) field distributions | Supporting equivalence | Derive continuous multilinear [n-point](GLOSSARY.md#quantum-fields-and-distributions) functionals, then their unique tempered-distribution kernels on R^(4n), from the common-domain weak/strong continuity and adjoints. The current actual n-point values on factorized test functions are not yet such a kernel theorem. |
| [Bosonic](GLOSSARY.md#quantum-fields-and-distributions) finite-component multiplets | Interpretive fidelity argument | Explain why [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) [curvature](GLOSSARY.md#gauge-fields-and-observables) polynomials and covariant derivatives lie in integer-spin finite-component Lorentz multiplets; justify the proper-orthochronous group rather than its universal cover. A purely bosonic observable presentation is plausible, but must not be advertised as an established equivalence for every allowed presentation. |
| Countable family | Interpretive fidelity argument | Explain why a countable generating field family suffices for the required polynomial observables, including renormalized composites. Countability of a formal polynomial grammar does not itself construct its quantum correspondence. |
| Locality | Supporting equivalence | Relate closed-support smeared commutation to the usual distributional spacelike exchange condition using tensor products and partitions of unity; no sharp-time field product may be assumed. |
| Wightman/OS alternatives | Source choice and supporting equivalence | The source permits a framework at least as strong as either cited system. Choosing Wightman is valid if its full cited-standard adequacy is established; there is no need to require both, nor impose a Euclidean construction. |
| [Analyticity](GLOSSARY.md#analysis-and-asymptotics), [cluster](GLOSSARY.md#short-distance-products-and-contact-terms) theorems | Supporting consequences | Identify the exact cited consequences required and derive them from spectrum/locality/unique vacuum, rather than silently adding stronger [holomorphic](GLOSSARY.md#analysis-and-asymptotics) assumptions or assuming sharp-time restrictions. |
| Yang–Mills identification, [stress tensor](GLOSSARY.md#scales-and-renormalization), [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) | Missing definitions outside this role | None is supplied by the Wightman axioms or the new lemmas. The assembled exact target remains absent. |

This review has not accessed the full text of the exact cited Wightman primary
reference. A search located the publisher's `PCT, Spin and Statistics, and All That` record, but bibliographic access
is not consultation of its axioms. Exact bibliography and source locations must be
supplied by the source analyst; secondary summaries cannot justify closing the
cited-standard audit.

## Adversarial checks

* A different operator with the same unitary time translations cannot change the generator domain or action (new checked uniqueness lemmas).
* A spectrum consisting only of zero cannot have finite mass (existing checked theorem); continuous positive spectrum is allowed (resolvent definition and new equivalence impose no eigenvector requirement).
* Common-domain adjoint identities cannot be satisfied by an unclosable smeared field (new graph-limit lemma).
* A massive free theory, an unused gauge-group index, or an unrelated classical sector still passes the QFT-only fragment. No QFT lemma resolves this central loophole.
* No proof of the existence of a Yang–Mills theory was attempted or required in this work.
