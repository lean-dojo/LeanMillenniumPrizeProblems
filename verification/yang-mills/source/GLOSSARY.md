# Terminology and notation guide

Use this guide alongside the [README](../README.md) and the
[document map](DOCUMENTATION_GUIDE.md). Definitions here give a first reading
of the terminology; the linked source files and equations specify the exact
mathematical conditions. A term's presence in a historical review does not
mean its associated task is still open.

## Reading a formalization

| Term | Meaning in this repository |
| --- | --- |
| Specification | A proposition that states precisely which objects must exist and which properties they must satisfy. Defining it does not prove it. |
| Witness | The objects and proofs that satisfy a specified collection of requirements. |
| Closed target | A proposition with no extra, unspecified assumptions or parameters standing for the intended physics. Its group quantifier is part of the proposition. |
| Predicate | A property expressed as a proposition depending on an input. Concrete predicates are essential; an arbitrary supplied predicate cannot define what “Yang–Mills” means. |
| Fidelity; sufficiency argument | An argument that the formal statement captures the intended source requirements. This involves mathematical interpretation in addition to machine checking. |
| Supporting lemma; bridge | A theorem connecting two concrete definitions or conventions. Such a theorem may support the specification without constructing a quantum theory. |
| Admission | The verifier's decision to accept a specification or submitted theorem under the repository's checking contract. It is not external endorsement. |
| Negative control | A deliberately insufficient or invalid example used to check that a definition or verifier rejects a known failure mechanism. |
| Universe; universe-polymorphic | Lean's hierarchy of type sizes, and a declaration parameterized by a level in that hierarchy. `Type 0` is the smallest data universe used here. |
| Kernel; transitive axiom audit | Lean's core proof checker; an inspection of every axiom used by a declaration, including through its dependencies. `sorry` introduces an unfinished proof and is rejected by the admission rules. |
| Totalized operation | An operation defined even outside its usual mathematical domain, using a default value. Integrals and derivatives therefore need explicit integrability or differentiability hypotheses when those meanings matter. |

See the [certification contract](../CERTIFICATION.md),
[statement policy](STATEMENT_POLICY.md), and Lean's official references on
[universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)
and [axioms](https://lean-lang.org/doc/reference/latest/Axioms/).

## Gauge fields and observables

| Term | First-reading explanation |
| --- | --- |
| Gauge group; gauge transformation | The group specifying local changes of field representation. Gauge-invariant observables are unchanged by these transformations. |
| Connection; curvature | A gauge potential `A` and its field strength `F`. Curvature contains a derivative term and a Lie-bracket term; conventions determine where the coupling appears. |
| Covariant derivative; descendant | A derivative incorporating the connection so that it transforms correctly under gauge transformations; a descendant is an observable obtained by differentiation. |
| Adjoint action; invariant tensor | The action induced by group conjugation on its Lie algebra; a tensor unchanged by the relevant group action. |
| Color frame; structure constants | A basis for the gauge Lie algebra, and the coefficients of its bracket in that basis. These are internal gauge indices, not spacetime indices. |
| Casimir contraction | A contraction of Lie-algebra structure constants producing an invariant group factor, such as `C_A` in perturbative coefficients. |
| Composite observable | A local expression made from fields and derivatives, such as a curvature-square expression. Its quantum definition includes renormalization. |
| Evaluation quotient; setoid | Identifying classical expressions that agree on every smooth connection. A setoid is Lean's packaging of an equivalence relation for forming a quotient. |
| Filtration; homogeneous grade | A nested family of spaces bounded by degree; a homogeneous grade contains expressions of one exact degree. A filtered map may mix lower degrees. |
| Engineering dimension | The weight assigned by classical spacetime scaling. Here curvature has weight two and each covariant derivative adds one. It differs from a quantum anomalous dimension. |

For the exact conventions, see the
[classical observable review](YANG_MILLS_REVIEW.md),
[basis construction](CLASSICAL_BASIS_BV_DESCENT_REVIEW.md), and
[current group-scope discussion](CURRENT_JW4_READINESS_CROSSWALK.md#global-groups-and-local-observable-scope).
The introductory physical source is Jaffe–Witten,
[*Quantum Yang–Mills Theory*, §1](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf).

## Quantum fields and distributions

| Term | First-reading explanation |
| --- | --- |
| QFT; Wightman framework | Quantum field theory; a formulation using fields on a Hilbert space with domain, symmetry, locality, spectrum and vacuum conditions. |
| O(4); E(4) | The orthogonal group preserving the Euclidean quadratic form; Euclidean rotations/reflections together with translations. These are auxiliary Euclidean symmetries. |
| Poincaré covariance; Lorentz multiplet | Compatibility with translations and relativistic spacetime symmetries; a finite collection of field components transforming together. |
| Bosonic observable | An observable obeying commutation, rather than anticommutation, at spacelike separation. The observable framework here is bosonic. |
| Common invariant domain | A dense subspace on which all fields act and which their action preserves, so products of fields can be formed there. |
| Smearing; test function | Integrating a field against a sufficiently regular function to give meaning to a distributional field. This does not assume a field operator exists at each individual point. |
| Schwartz function; tempered distribution | A smooth function whose derivatives decay faster than every inverse polynomial; a continuous linear functional on the space of such functions. |
| Kernel; n-point function; vacuum word | A distribution representing a multilinear expression; the vacuum expectation of a product of `n` fields. “Word” keeps track of the fields' order. |
| Tensor tests; dense tensor span | Products of test functions in separate variables; finite sums of these products form a dense subspace in the specified test space. Equality there determines a continuous kernel. |
| Spin cover | A group that distinguishes rotations identified in the ordinary Lorentz group, allowing half-integer-spin representations. The book uses SL(2,C), the double cover of the proper orthochronous Lorentz group; the code uses the ordinary group for bosonic observables. See the [source comparison](SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026), p.97. |
| Cyclic vacuum | Field words acting on the vacuum span a dense subspace. Composite-only cyclicity requires the specified observable family itself to generate the physical space. |
| Borchers positivity | Positivity of combinations of vacuum correlations corresponding to squared norms of field-word states. |
| Euclidean; Minkowski; OS reconstruction | Euclidean signature versus relativistic spacetime signature; the Osterwalder–Schrader route reconstructing a physical theory from suitably constrained Euclidean correlations. |

See the [QFT review](QFT_REVIEW.md),
[full-kernel construction](KERNEL_BV_COHOMOLOGY_REVIEW.md), and
[current comparison with the cited frameworks](CURRENT_JW4_READINESS_CROSSWALK.md#complete-qft-presentation-comparison).
The latter links the primary-source reading records, including the newly
available book chapter, the edition consulted and remaining comparison limits.

## Operators and spectrum

| Term | First-reading explanation |
| --- | --- |
| Hamiltonian; generator | The operator determining time evolution; more generally, the infinitesimal operator of a continuous symmetry action. |
| Self-adjoint operator | An operator equal to its Hilbert-space adjoint, including equality of domains. For an unbounded operator, a formal symmetry identity alone is insufficient. |
| Resolvent; spectrum | A parameter belongs to the resolvent when the shifted operator has the required bounded, everywhere-defined inverse. The spectrum is the complement; it includes continuous spectrum. |
| Mass gap; spectral mass | A positive interval above vacuum energy zero containing no spectrum; here the mass is the finite positive supremum of admissible gap sizes. |
| Graph core | A subdomain dense in the operator's graph norm, which controls both the vector and its image. Hilbert-space density alone is weaker. |
| PVM; SNAG theorem | Projection-valued measure; Stone–Naimark–Ambrose–Godement spectral representation for unitary representations of abelian groups. These describe spectral information also expressed here through Fourier tests. |
| Unitary transport; carrier | Moving a construction through an inner-product-preserving equivalence; a carrier is its underlying space or Lean type. |

See the [Hamiltonian and spectral review](QFT_REVIEW.md),
[carrier comparison](CANONICAL_TRACE_QFT_REVIEW.md), and
[current physical framework](FINAL_FIDELITY_ARGUMENT.md#complete-physical-framework).

## Perturbative calculations

| Term | First-reading explanation |
| --- | --- |
| Formal series; perturbative order | A coefficient-by-coefficient expansion without an assertion of convergence; an index specifying how many powers of a parameter are retained. |
| Tree order; loop order | Contributions with no loops versus the number of loops in the perturbative organization. The formal parameter `ℏ` records loop order; powers of `g` record coupling order. |
| Covariance; propagator; Gaussian contraction | The free two-point kernel and its use to pair fields in a Gaussian calculation. This use of “covariance” differs from symmetry covariance. |
| Wick contraction | Pairing fields using the free covariance, including the signs associated with odd fields. This differs from Wick rotation. |
| Vertex; external leg; arity | An interaction term; an external field argument of an amplitude; the number of arguments. A “species” is a field or antifield type. |
| Connected amputated amplitude (CAC) | A connected correlation quantity with its external free propagators removed. Here `L` denotes the corresponding generating family. |
| Legendre transform; 1PI; Gamma | The transformation relating connected quantities to one-particle-irreducible quantities; 1PI diagrams remain connected after cutting a single internal line. `Gamma` denotes the effective-action family here. |
| Faà di Bruno combinatorics | The partition sums expressing higher derivatives of a composition. Graded versions also track signs from odd variables. |
| Cauchy product; unshuffle | Distributing a total formal order between factors; a permutation that preserves order inside each selected block. |
| Switching function; adiabatic removal | A function localizing interaction insertions; a justified procedure removing this auxiliary localization. Choosing zero switching cannot define the final interacting predictions. |

See the [bare construction](PERTURBATIVE_IMPLEMENTATION.md),
[flow conventions](FLOW_IMPLEMENTATION.md), and
[Legendre review](SAME_ACTION_IDENTITY_REVIEW.md).
The primary perturbative presentations used by the repository are
[Fröb–Holland–Hollands](https://arxiv.org/abs/1511.09425) and
[Fröb–Holland](https://arxiv.org/abs/1603.08012).

## Scales and renormalization

| Term | First-reading explanation |
| --- | --- |
| UV; IR | Ultraviolet, meaning short distances or high momenta; infrared, meaning long distances or low momenta. |
| Regulator; cutoff | An auxiliary modification controlling singular behavior. Removing a cutoff is a separate limit, not selection of one convenient finite cutoff. |
| Bare; renormalized; counterterm | Quantities before versus after the specified normalization procedure; local terms used to adjust divergent or normalization-dependent contributions. |
| Relevant; marginal; irrelevant | Terms below, at, or above the dimension threshold appropriate to the flow or insertion. Their boundary conditions differ. |
| Power counting; graph grading | Dimension and combinatorial rules bounding terms and assigning powers of the coupling and loop parameter. |
| Renormalization scheme; finite mixing | A consistent normalization prescription; finite linear changes among composite observables, subject to dimension and symmetry constraints. |
| RG; running coupling; beta | Renormalization group; the scale-dependent coupling; the function governing its scale derivative. The chosen direction of the scale parameter fixes the sign convention. |
| Gamma; anomalous dimension | A matrix governing scale-dependent operator mixing beyond classical scaling. Lowercase `gamma` in this role differs from the effective action `Gamma`. |
| CS equation | The Callan–Symanzik equation linking scale changes, coupling changes and field or observable normalization. |
| Asymptotic freedom | The running coupling tends to zero toward short distances in the selected convention. |
| Stress tensor; trace anomaly | The local energy-momentum tensor; the quantum correction to its classical trace/scaling relation. Its charges must match the physical generators. |
| Vacuum centering; one-point function | Subtracting an operator's vacuum expectation times the identity; the expectation of a single field. The subtraction here is computed from the actual vacuum. |

See the [prescription and transport formulas](PERTURBATIVE_PRESCRIPTION.md),
[fixed-flow uniqueness review](FIXED_FLOW_UNIQUENESS_REVIEW.md), and
[current stress interpretation](FINAL_FIDELITY_ARGUMENT.md#same-observables-predictions-and-stress).

## Graded gauge symmetry

| Term | First-reading explanation |
| --- | --- |
| Grassmann parity; superalgebra; Koszul sign | Even/odd grading; an algebra respecting that grading; the sign obtained when odd factors are permuted. Odd factors anticommute. |
| Ghost; antighost; ghost number | Auxiliary graded fields used to encode gauge symmetry, and their integer grading. They are not physical particles in the positive Hilbert space. |
| BRST; ST | Becchi–Rouet–Stora–Tyutin differential; Slavnov–Taylor symmetry operator or identity. Their explicit conventions are fixed by the action here. |
| BV; antifield; antibracket | Batalin–Vilkovisky formalism; a source paired with a field's symmetry variation; the odd bracket pairing field and antifield derivatives. |
| Master action; CME | The action including antifield couplings; the classical master equation `(S,S)=0` in the specified BV bracket. |
| Gauge fixing; gauge fermion | Choosing an auxiliary gauge presentation; an odd functional used to encode that choice. The shifted auxiliary field `B` is distinct from an invariant quadratic form also written `B`. |
| Chevalley–Eilenberg differential | The differential built from a Lie algebra’s bracket to define Lie-algebra cohomology. The historical ghost-sector proof uses the Jacobi identity to establish its square is zero. |
| Noether identity; equivariant cohomology | A relation among equations of motion implied by gauge symmetry; cohomology with the specified symmetry restrictions retained. |
| Augmentation | The algebra map selecting the constant term, used after differentiation to extract polynomial coefficients. |
| Nilpotent; differential | An operator `Q` with `Q²=0`. This property must be proved for the actual operator or required by explicit equations. |
| Cocycle/closed; boundary/exact; cohomology | `Qx=0`; `x=Qy`; the quotient `ker Q / im Q`. Nilpotency makes this quotient possible. A primitive is such a `y`. |
| Ward identity; anomaly | An equation encoding symmetry in correlation functions or amplitudes; a failure term in that equation. Restoring identities requires the specified local corrections. |
| Euler derivative; divergence quotient; EOM | A variational derivative including integration by parts; identifying densities differing by a total divergence; equations of motion. Local and integrated identities must be distinguished. |
| Jet; superjet | A field together with its derivative coordinates; a jet algebra containing even and odd generators. A momentum Taylor jet is related derivative data for an amplitude. |

For formulas and conventions, see the historical
[BRST/BV interface](BRST_BV_INTERFACE.md) and the current
[same-action fidelity argument](FINAL_FIDELITY_ARGUMENT.md#actual-yangmills-action-and-prescription).
The interface's “unfinished” lists describe its original implementation stage.

## Short-distance products and contact terms

| Term | First-reading explanation |
| --- | --- |
| OPE | Operator product expansion: an asymptotic description of nearby observable products in terms of local observables and coefficient distributions. |
| Truncation; oversubtraction | Retaining outputs up to a degree bound; imposing additional subtraction conditions to control remainders. These are distinct from truncating coupling order. |
| Spectator; cluster | An insertion kept away from the points being brought together; the group of points undergoing that collision. |
| Partial diagonal; off-diagonal | A configuration where some insertion points coincide; a region avoiding the specified coincidences. |
| Contact term; local extension | A distribution supported at coincidence, often a delta derivative; extension of a distribution across a collision set with controlled local ambiguity. |
| Scaling degree; codimension | A measure of singular growth under dilation transverse to a collision; the number of independent normal coordinates. A cluster of `k` points in four dimensions has collision codimension `4(k−1)`. |
| Cumulant; partition-local correction | Connected correlation data versus full moments; a correction that collapses an insertion block into the same lower-insertion family. Spectator dependence is not free data. |
| BPHZ; forest subtraction | Bogoliubov–Parasiuk–Hepp–Zimmermann renormalization; organizing subtractions over nested or disjoint divergent substructures. Mentioning it does not supply a gauge-compatible construction. |

See the [prescribed OPE extraction](PERTURBATIVE_PRESCRIPTION.md#coefficients-are-extracted-not-assigned),
[contact review](BV_CONTACT_INTERFACE_REVIEW.md), and
[local-extension example](LOCAL_WARD_ADVERSARIAL_REVIEW.md).

## Analysis and asymptotics

| Term | First-reading explanation |
| --- | --- |
| Weak/distributional limit | Convergence after pairing with specified test functions or matrix elements. It does not assert operator-norm convergence. |
| Germ; flat term | Behavior near a chosen point or limit; a smooth contribution whose derivatives at the expansion point all vanish. For example, `exp(-1/g²)`, extended by zero at `g=0`. |
| Little-o remainder | `r(g)=o(g^N)` means `r(g)/g^N → 0` in the stated limit. A separate finite remainder is required at each order. |
| Smooth versus analytic | Smooth means derivatives of every finite order exist continuously; analytic requires local representation by a convergent power series. The pinned `ContDiff` uses `∞` for smooth and outer `⊤`/`ω` for analytic. |
| Holomorphy; tube domain; boundary value | Complex analyticity; a complex domain restricting imaginary coordinate differences to a cone; the distributional limit approaching real spacetime. |
| Wick rotation | Analytic continuation between Euclidean and Minkowski descriptions, including the required phases on tensor labels. It is more than substituting the time coordinate. |
| Cofinal cutoff map | A change of cutoff variable that still tends to the same limiting endpoint, such as `UV ↦ a*UV` with `a>0`. |
| Baire property; seminorm | A topological property used in continuity arguments; a norm-like size function that may vanish on nonzero vectors. Families of seminorms specify the Schwartz topology. |
| Fréchet; barrelled; nuclear kernel theorem | A complete metrizable locally convex space; a condition supporting uniform-boundedness arguments; a result identifying suitable multilinear test-function functionals with kernels on a product space. |
| Mollifier; polarization | A smooth approximation used to define or test distributional limits; recovery of multilinear data from diagonal evaluations, with grading handled explicitly here. |
| Canonical projector; determinacy | A prescribed derivative/coefficient extraction operation; a theorem that its data determine the amplitude under the stated hypotheses. |

See the [smoothness correction](SMOOTH_ORDER_REVIEW.md),
[canonical determinacy review](SMOOTH_CANONICAL_INSERTION_REVIEW.md), and
[analysis needed for full kernels](KERNEL_BV_COHOMOLOGY_REVIEW.md).
The smoothness convention can also be checked in the
[pinned mathlib definition](https://github.com/leanprover-community/mathlib4/blob/1ccd71f89cbbd82ae7d097723ce1722ca7b01c33/Mathlib/Analysis/Calculus/ContDiff/Defs.lean).

## Notation and source abbreviations

| Notation | How to read it |
| --- | --- |
| `G`, `Q`, `C`, `H` | Usually the gauge group, physical quantum theory, composite-observable map and Hamiltonian. In BRST calculations `Q` can instead be the differential, and `C` can be a covariance or OPE coefficient; check the local definition. |
| `g`, `μ`, `Λ`, `UV`, `ℏ` | Coupling, positive normalization scale, flow cutoff, upper cutoff and formal loop parameter. |
| “Same” or “actual” object | The equation uses the already specified group, field, action or operator, rather than independently supplied replacement data. |
| Balanced momenta | External momenta satisfying the background momentum-conservation constraint. Local insertions can retain independent momenta. |
| Dictionary; lift; recovery | A correspondence between observable labels and representatives; a corrected representative; extraction of physical outputs from those representatives. Each has explicit equations. |
| JW; FH; FHH; IZ | Jaffe–Witten; Fröb–Holland; Fröb–Holland–Hollands; Itzykson–Zuber. |
| OS; CMI | Osterwalder–Schrader; Clay Mathematics Institute. |
| [27], [35], [45] | Reference numbers in the Jaffe–Witten bibliography: Itzykson–Zuber, Osterwalder–Schrader I/II, and Streater–Wightman respectively. They are not Markdown footnotes. |
| PRIMARY; root; owner; tranche | Historical development language: the reviewed staging tree, integrating agent, responsible implementer, and a batch of work. Snapshot line numbers, hashes and `/tmp` or `work/` paths record that stage. |

For bibliographic details and access qualifications, see
[SOURCE_ANALYSIS.md](SOURCE_ANALYSIS.md#primary-reference-findings-and-limits)
and the [current crosswalk](CURRENT_JW4_READINESS_CROSSWALK.md).
