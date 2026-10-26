# Source analysis and clause crosswalk (2026-10-20)

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

> **Source-access update, 22 October 2026.** The user supplied OS II and the
> 2000 reissue of Streater–Wightman. The direct readings below supersede the
> historical access limitations for [OS II](#direct-os-ii-reading-22-october-2026)
> and [Chapter 3](#direct-streaterwightman-reading-22-october-2026).
> Source-equivalence obligations remain; access and reading are not validation.

This early source analysis separates three tasks: defining the intended conditions,
justifying their relation to the prose source, and eventually constructing a theory
satisfying them. Its crosswalk records what the repository lacked at that stage.

Read the source table alongside the access qualifications. The interpretive choices
explain why a formalization must make conventions explicit without silently imposing an
extra construction method.

For terminology, start with the [relevant glossary section](GLOSSARY.md#reading-a-formalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This is a semantic gap analysis, not a claim of specification completion. It uses the
repository's pinned `source/yangmills.pdf`, extracted locally with pypdf, and the
primary-reference evidence recorded below. Page numbers are printed page numbers (PDF
index is one less). No existence proof is required to close a specification gap.

## Clause-by-clause analysis

| Source location | Fixed mathematical requirement | Existing declarations | Missing definition or equivalence work | Existence-proof work, outside this task |
|---|---|---|---|---|
| §4 theorem, p6; classical setting §1 pp1–2 | Every compact simple [gauge group](GLOSSARY.md#gauge-fields-and-observables), with its actual Lie bracket entering the identified quantum theory | `CompactSimpleGaugeGroup` encodes connected compact Lie group with simple real tangent Lie algebra | Justify connected convention and universe coverage; connect actual G-invariant tensors, observable labels, and perturbative coefficients to Q | Construct a [witness](GLOSSARY.md#reading-a-formalization) for each G |
| §4 theorem, p6; §3 p5 | Theory on full R4 with relativistic local fields | `Spacetime`, `WightmanData` | Check [Wightman](GLOSSARY.md#quantum-fields-and-distributions) framework sufficiency against [45], including the topology of multi-point distributions, domains and spacetime covariance | Establish axioms for constructed fields |
| §4 first paragraph, p6 | Local fields corresponding to all [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) curvature/covariant-derivative polynomials | `CurvatureJet`, `CurvatureTracePair`, `CurvatureScalarPolynomial` | Pair contractions are a strict fragment of general invariant tensors; local gauge action/covariance and quantum renormalized correspondence are absent | Construct matching fields and prove obligations |
| §4 footnote1, p6 | [Renormalization](GLOSSARY.md#scales-and-renormalization) qualifies correspondence; no natural polynomial/operator bijection | Classical engineering-dimension [filtration](GLOSSARY.md#gauge-fields-and-observables) | A finite-renormalization/mixing presentation with EOM/contact/derivative relations; clarify precisely which quotients and filtration are used | Exhibit allowed mixing data |
| §4 first paragraph, p6 | Short-distance correlations match [asymptotic freedom](GLOSSARY.md#scales-and-renormalization) and perturbative renormalization | `vacuumNPoint` computes the same [QFT](GLOSSARY.md#quantum-fields-and-distributions)'s vacuum field words | Fixed G-dependent formal perturbative coefficient construction, [running coupling](GLOSSARY.md#scales-and-renormalization) and anomalous mixing; distributional scaling; all-order remainder meaning | Prove those asymptotics of actual correlations |
| §4 first paragraph, p6; §3 p6 opening paragraph | [Stress tensor](GLOSSARY.md#scales-and-renormalization) belongs to those fields and predictions | None | Tensor field labels, symmetry and conservation as [smeared](GLOSSARY.md#quantum-fields-and-distributions) distribution identities, normalization of translation charges on stated domains, allowed improvement/contact terms | Construct tensor and prove identities |
| §4 first paragraph, p6 | [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) has prescribed local singularities from asymptotic freedom | None | Fixed coefficient predictions, collision configuration domain, finite truncations by [engineering degree](GLOSSARY.md#gauge-fields-and-observables), exact distributional remainder topology, [RG](GLOSSARY.md#scales-and-renormalization) logarithms, allowed scheme equivalence | Establish OPE for actual fields |
| §4 theorem, p6 | Nontrivial identified Yang–Mills theory | `HasNonVacuumState`, `HasFieldExcitation` and consequences of finite mass | Explain nontriviality only after YM identification; these necessary conditions alone admit unrelated free massive fields | Supply nontrivial witness |
| §4 second paragraph, p6 | H is actual time-translation generator; HΩ=0, spectrum in [0,∞), a gap (0,Δ), mass sup gaps is finite | Generator domain/action in `WightmanAxioms`; `HasPositiveFiniteMass`; `PDFLiteral` bridge | Review operator-spectrum equivalence and prove any desired equivalence to positive-spectrum infimum; do not substitute independently supplied spectral set | Prove positive finite mass for identified witness |
| §4 theorem, p6 | Existential proposition combines all clauses for the same theory for each G | QFT-only and groupwise necessary shadows | No assembled exact YM target exists because identification/UV/OPE meaning is absent | Future proof of assembled fixed target |

Some manifest gaps currently conflate absence of a QFT existence proof with
specification incompleteness. In particular, the lack of a constructed model on R4 does
not by itself make `Spacetime` an incomplete definition. Conversely, a concrete classical
grammar and a same-vacuum correlation formula do not make quantum identification or
[UV](GLOSSARY.md#scales-and-renormalization) behavior partially defined in the sense required for exact admission.

## Primary-reference findings and limits

Jaffe–Witten reference [45] is Streater–Wightman, *PCT, Spin and Statistics and All
That* (1964); [35] consists of Osterwalder–Schrader I, CMP 31 (1973) 83–112, **and II**,
CMP 42 (1975) 281–305. The latter is mathematically material: its introduction on p282
says the original [OS](GLOSSARY.md#notation-and-source-abbreviations) I Lemma 8.8 is wrong, and bare original E0–E4 were not
known sufficient for reconstruction. It supplies a stronger distribution condition and a
separately usable linear-growth sufficient condition.

An OS route must implement a corrected sufficient system, not merely symmetry/reflection
positivity/temperedness.

Primary OS II PDF, introduction pp281–283, sufficiency constructions Chapters III–VI:
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II-with-an-Appendix-by/cmp/1103899050.pdf . The search index exposed its introduction; a direct open returned a
one-line response. This supports the warning above, not a complete line-by-line
formalization audit of the paper.

The preceding paragraph records the original retrieval attempt. Full local
access and a scoped direct reading are now recorded below.

Reference [27] is Itzykson–Zuber, *Quantum Field Theory* (1980). The primary agent
subsequently downloaded the full [hosted textbook](https://www.maths.tcd.ie/~ngarron/doc/books/Quantum%20Field%20Theory%20%5BItzykson-Zuber%5D.pdf) and inspected printed pp657–659 and 671–680
(PDF indices 677–679, 691–700). Relevant statements: §13-3-2, equations (13-89)–(13-92),
gives running-coupling and anomalous logarithmic factors; §13-5-1, (13-131)–(13-133),
specifies dimension-ordered short-distance expansions and their weak matrix-element
interpretation. Equations (13-145), (13-149) concern coefficient RG equations. Printed
p677 explicitly cautions against naive insertion of additional composites without extra
subtraction contributions, illustrated by (13-150).

Section 13-5-2, (13-154)–(13-155), treats [operator mixing](GLOSSARY.md#scales-and-renormalization); pp679–680 relate current
normalization, [Ward](GLOSSARY.md#graded-gauge-symmetry) identities and anomalous dimensions. This is stronger evidence
than contents-only access, but is not a formalized all-group Yang–Mills perturbative
algorithm or a completed fidelity proof.

Reference [45] publisher contents are available at https://www.jstor.org/stable/j.ctt1cx3vcq . Full axiom text was not
obtained in this role. The QFT formalizer must independently audit domain/temperedness
details against the actual text. A source crosswalk is not that audit.

This is the historical access record; the supplied book and direct comparison
below supersede the lack of access.

## Direct OS II reading (22 October 2026)

The user supplied `osterwalder1975.pdf`, a 25-page copy of Konrad Osterwalder
and Robert Schrader, *Axioms for Euclidean Green's Functions II*, with an
appendix by Stephen Summers, *Communications in Mathematical Physics* **42**,
281–305 (1975). The supplied source filename is
`osterwalder1975.pdf`; its SHA-256 is
`36413586b83b491c8e0ef318e98d6e882619019826e62dc24daf898dc7f486ec`.
The [publisher-hosted paper](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II-with-an-Appendix-by/cmp/1103899050.pdf)
provides a portable bibliographic link; this reading used the supplied local copy.

**Coverage:** direct reading of printed pp.281–289, 297 and 303–305, with
rendered-page checks of the key conditions on pp.282, 285 and 287–288 and the
appendix on pp.303–304. This is an AI-assisted source comparison, not a complete
proof audit of Chapters V–VI or of the paper's dependencies. Printed p.281 is
PDF page 1. The full document is accessible; the narrower review scope is no
longer an access failure.

| Location | What the paper establishes or states | Consequence for this repository |
| --- | --- | --- |
| p.282, introduction and Remark 1 | OS I Lemma 8.8 is incorrect. The authors state that sufficiency of the original E0–E4 was open at publication. Their example distinguishes separate from joint Laplace-transform behavior. | Do not present bare original E0–E4 as a reconstruction theorem established by these papers. This is a statement about the 1975 source, not a claim about all later literature. |
| pp.284–286, Eq. (2.7), Chapter III | The corrected equivalence uses the strengthened condition labelled E-tilde-0, together with E1–E4. It requires continuity of the difference-variable functions in a topology defined through the Fourier–Laplace transform. | This is a precise additional continuity requirement, not ordinary temperedness with a new name. The theorem relates it to the Wightman distribution axioms R0–R5. |
| p.287, Eq. (4.1) | The alternative E0-prime condition bounds the n-point functional by a Schwartz norm of order n times one fixed integer s. Its constants have factorial growth: sigma_n is bounded by alpha times (n!)^beta, for fixed constants. | This controls growth across the entire sequence of correlations; a separate continuity assertion for each n does not supply this bound. |
| pp.287–288, Eq. (4.3) and Remark 3 | E0-prime plus E1–E4 reconstructs a unique Wightman theory. The resulting R0-prime bound has norm order n times a fixed w, with constants bounded by alpha times beta^(n²). The authors do not obtain factorial growth for those constants or a matching equivalence theorem for these growth classes. | Distinguish the sufficient reconstruction route from the corrected equivalence theorem. Do not claim identical quantitative growth on the Euclidean and Minkowski sides. |
| pp.287 and 303–305, Eq. (4.2) and Summers appendix | The stronger E0-double-prime bounds tensor tests using a product of fixed-order single-variable norms. The appendix proves it implies E0-prime. | Tensor-test estimates require a justified extension to full test functions; that implication is supplied here under specific quantitative assumptions. |
| pp.289 and 297, openings of Chapters V–VI | Analytic continuation uses original E0, E1 and E2. The linear growth assumption is used for the estimates establishing tempered boundary values. | Analytic continuation alone must not be treated as a proof of tempered Wightman distributions. |
| p.283, Remark 5 | The exposition treats one real scalar field; the authors refer to OS I Chapter 6 for extension to countably many arbitrary-spin fields. | This is not a worked comparison with this repository's particular countable bosonic multiplets. That presentation still needs its own justification. |

For orientation, **Schwinger functions** are Euclidean correlation functions;
**reconstruction** recovers a relativistic quantum field theory from them.
The [glossary](GLOSSARY.md#quantum-fields-and-distributions) explains tempered
distributions and the Wightman framework. The paper defines its test spaces and
norms on pp.283–285; the bounds above refer to those conventions.

The current candidate supplies a Minkowski theory directly through
[WightmanAxioms](../YangMills/QFT/Wightman.lean), and supplies full continuous
Schwartz kernels tied to its actual vacuum words through
[WightmanVacuumKernels](../YangMills/WightmanVacuumKernels.lean).
It does not obtain those kernels by applying OS II. Consequently this reading
does not justify adding E0-prime as a new compulsory field of the candidate.
An eventual Euclidean construction using OS II would need to prove its chosen
reconstruction hypotheses and connect the reconstructed objects to all the
candidate's fields. Auxiliary perturbative analytic continuation alone does
not perform that task.

**Status:** the OS II access gap is closed and the earlier reconstruction
warning is directly supported. No Lean definition or proof was changed. The
Streater–Wightman comparison is now recorded below; full source-equivalence
arguments and independent human expert validation remain outstanding.

## Direct Streater–Wightman reading (22 October 2026)

The user supplied `spin-and-statistics-and-all-that.pdf`,
a 221-page scan of R. F. Streater and A. S. Wightman, *PCT, Spin and Statistics,
and All That*. The copyright page identifies the **2000 Princeton paperback
reissue, with revised preface and corrections**, of the book originally
published in 1964. This is a later edition of Jaffe–Witten reference [45], not
a verified scan of its cited 1964 printing. No comparison between editions was
performed. SHA-256:
`44fadba731cafe7f009d4e561372febb3597e1f2a4819346ce2efd16befcb889`.

**Coverage:** Chapter 3, “Fields and Vacuum Expectation Values,” printed
pp.96–133, corresponding to PDF pages 108–145. The chapter was read using OCR
and rendered pages; the central axiom and kernel statements on pp.97–101, 106
and 118 were checked visually. The chapter includes the reconstruction proof,
symmetry discussion and bibliography. Reading them is not a verification of
every proof step. Dependencies in Chapters 1–2 and 4, and the bibliography's
papers, were not recursively audited. This is an AI-assisted comparison with
the current definitions, not independent expert review.

The main comparison is with [WightmanData / WightmanAxioms](../YangMills/QFT/Wightman.lean),
[spacetime and test functions](../YangMills/QFT/Spacetime.lean) and
[WightmanVacuumKernels](../YangMills/WightmanVacuumKernels.lean).
The book labels its basic assumptions O, I, II and III; the repository uses a
different numbering. The table follows the book, not the code's comment labels.

| Book location and condition | Repository counterpart | Assessment and remaining comparison |
| --- | --- | --- |
| p.97, O: separable Hilbert space, continuous unitary representation of the inhomogeneous SL(2,C), forward energy-momentum spectrum and unique invariant vacuum | `complete`, `separable`, unitary representation fields, `vacuum_invariant`, `vacuum_unique`, `spectral_integrable`, `spectral_support` | These are identifiable counterparts, not identical formulas. The code uses the proper orthochronous Poincaré group rather than its spin cover, translation-invariant vacuum uniqueness, and an integrated Fourier-test condition. Cover descent for bosonic observables and equivalence of the spectral and vacuum formulations still need explicit justification. |
| p.98, I, Eqs. (3-2)–(3-3): common dense linear domain containing the vacuum, preserved by transformations, fields and adjoints; matrix elements are tempered distributions | `domain`, `dense_domain`, `domainAction`, field codomain, `adjoint_relation`, `adjoint_involution`, `conjugateTest_eq`, `field_continuous` | The common domain and adjoint requirements are explicit. The code requires Hilbert-norm continuity for a fixed domain vector, whereas the book states continuity of matrix elements. The closed-graph argument relating them is a supporting mathematical obligation, not literal textual equality. The book does not require essential self-adjointness of each smeared field. |
| p.99, II, Eqs. (3-4)–(3-5): field covariance and inverse spacetime pullback | `componentAction`, its representation laws, `covariance`, `pullback_eq` | The inverse spacetime pullback agrees in form. Compare the book's inverse matrix with the code's matrix-column action through an explicit dual/index convention; do not identify them by notation alone. |
| p.100, III, Eq. (3-6): spacelike commutation or anticommutation, including adjoints | `locality` for all field indices, plus adjoint closure | The code selects the commuting observable case. Its hypothesis uses strictly spacelike-separated closed supports. The book's parenthetical criterion uses the nonzero test-function values. Boundary-touching supports and passage to the distributional locality statement require a continuity/approximation argument. |
| p.101: field theory requires vacuum cyclicity for polynomials in smeared fields | `cyclic`, using the span of all `Q.word` vectors | Direct structural match. Composite-only cyclicity elsewhere in the candidate is an additional identification condition; this page alone does not justify that stronger selection of generators. |
| pp.106–110, Eqs. (3-19)–(3-36), Theorems 3-1–3-3: full tempered vacuum distributions, covariance, spectral support, adjoint reversal, locality and positivity | `WightmanVacuumKernels.kernel`, `tensor_eq`, `tensor_dense`, `actual_words`, together with the actual Hilbert-space field products | The book explicitly invokes its nuclear theorem to extend product-test matrix elements to full Schwartz distributions. This directly supports the intended kernel presentation; it does not supply a Lean proof of the kernel theorem or of all full-test consequences from the code's predicates. |
| pp.111–116, Theorems 3-4–3-6: clustering and analytic continuation | Intended consequences of the operator axioms, spectrum, locality and vacuum uniqueness | These are substantive theorems, not automatic results of compiling a structure. The displayed clustering proof assumes a mass threshold; the book refers elsewhere for the case without a gap. Relating that threshold to the repository's Hamiltonian-gap presentation requires spectral reasoning. |
| pp.117–126, Theorem 3-7: reconstruction from tempered correlations with the listed properties, including clustering; unitary uniqueness | The candidate supplies the operator theory and matching kernels directly | No separate reconstruction field is needed just to state that endpoint. The written proof is for a Hermitian scalar field; p.126 states extension to countably many fields of any spin. That supports countable presentations but does not show that every source-admissible Yang–Mills observable family is captured by this particular one. |

Two boundaries are now supported directly by the chapter. On pp.101–102 the
authors distinguish equal-time canonical commutation relations and asymptotic
completeness from the axioms used for their field-theory results; p.126 again
says reconstruction does not establish asymptotic completeness. They should
not be silently added as general Wightman obligations. On pp.102–105 the
authors construct free-field examples, discuss Wick polynomials and introduce
generalized-free fields; p.116 gives free-field correlation functions. Thus
the cited framework itself allows these examples. Reading it does not resolve
the full candidate's free/generalized-free countermodel challenge.

Section 3-5, pp.126–132, treats additional symmetries and the reconstruction
of a PCT operator under specified correlation identities; it points forward
to Chapter 4 for the general local-field PCT result. This reading does not
audit that later theorem or establish separate P, C and T invariance.

**Status:** Chapter 3 is now accessible and directly compared in the supplied
edition. The former access blocker is closed. The explicit convention and
equivalence questions above remain open; neither an edition-to-edition audit
nor a completed fidelity proof is claimed. No Lean definitions or proofs were
changed as a result of this reading. Terms such as cyclicity, temperedness and
the spin cover are explained in the [glossary](GLOSSARY.md).

## Interpretive choices and scope

1. A Wightman presentation is a reasonable selected framework if shown at least as strong as the cited standard; requiring a second independent OS construction would add a method requirement. An OS presentation instead needs its corrected analytic/growth conditions.
2. Pure [bosonic](GLOSSARY.md#quantum-fields-and-distributions) gauge-invariant observables justify bosonic locality. No gauge potential acting on a positive physical [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions) is demanded; forcing that could introduce a spurious obstruction.
3. General invariant tensors of the actual [adjoint action](GLOSSARY.md#gauge-fields-and-observables), applied to [curvature](GLOSSARY.md#gauge-fields-and-observables) jets, are a natural group-sensitive classical observable language. Restriction to quadratic pairings can miss higher primitive invariants. Proving its algebraic presentation adequate is supporting equivalence work, not a YM existence proof.
4. Finite renormalization/mixing data may be witnesses, but equations linking them to a **fixed** perturbative construction are definitions. A proof author may choose an admissible presentation, not the prescribed singularities themselves.
5. Weak/distributional OPE remainders with [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) insertions with specified collision/contact restrictions are plausible; a norm-convergent operator OPE is an additional [analytic](GLOSSARY.md#analysis-and-asymptotics) demand unless supported by a fidelity argument. Purely pointwise expansions ignore coincidence singularities. One-loop leading behavior alone drops the perturbative-renormalization requirement.
6. §4 does not select a [regulator](GLOSSARY.md#scales-and-renormalization) or scheme. A chosen constructive presentation needs an equivalence/sufficiency argument before it becomes a universal obligation. Allowing quantified admissible schemes with fixed transformation laws is different from letting the proof author choose arbitrary predictions.
7. Footnote1 describes an expected filtered relationship and warns against naive bijection. It does not prescribe an exact filtered isomorphism as a separate mandatory theorem. Any stronger adopted condition must be justified as a presentation of correspondence rather than promoted from expectation to new requirement.
8. Connected compact simple Lie groups is the customary convention for the problem, but the source says compact simple gauge group and does not explicitly discuss disconnected extensions; document this convention rather than claim it is a literal source definition. Global forms with finite center must remain included.

## Nonrequirements and qualifications

No compulsory lattice, Wilson character, Haar regulator, preferred representation,
confinement, isolated particle state, chiral-symmetry breaking, unique formalization, or
different [carrier](GLOSSARY.md#operators-and-spectrum) per G. The extensions are explicitly separated in §5 pp6–7; methods
in §6.1 p7 are alternatives. §6.5 p11 describes lattice limits as a possible route.
Footnote2 p12 rejects weak compactness existence alone unless the limit's axioms and gap
are established; this is consistent with witness data needing all fixed properties, not
with requiring a specific construction.

## Exact central issue and next work

The outstanding issue is a mathematically fixed bridge from the pure G-Yang–Mills action
to the perturbative predictions and the same nonperturbative fields. A general OPE
expansion with existential coefficients can always be tuned and does not encode that
bridge. Adding a positive [beta](GLOSSARY.md#scales-and-renormalization) coefficient captures only one leading feature, and
imposing a Wilson-lattice limit silently selects a construction.

To complete this bridge, choose and document an admissible perturbative renormalization
presentation; define its gauge/ghost combinatorics, graph amplitudes, local [counterterms](GLOSSARY.md#scales-and-renormalization),
composite insertion mixing and symmetry identities; derive fixed G-sensitive
beta/anomalous/OPE coefficients; define precisely the RG-improved scaling and remainder
conditions imposed on the actual quantum correlations; and establish scheme-independence
or sufficiency of the chosen presentation. This is substantial missing
definition/equivalence work, separable from the future existence proof.

Until it is supplied, no complete exact-target admission is justified.
