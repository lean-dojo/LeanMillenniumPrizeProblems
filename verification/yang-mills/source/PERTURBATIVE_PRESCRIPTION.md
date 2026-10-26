# A concrete perturbative presentation and its exact limits

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This design note follows a proposed calculation from the group and action to flow
amplitudes, extracted [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) coefficients, and physical matching conditions. Its
equations make the normalization and sign conventions explicit.

Read the first four sections in order. The later sections explain why symmetry
identities, [contact terms](GLOSSARY.md#short-distance-products-and-contact-terms) and scale transport are needed in addition to a coefficient
recursion. Historical implementation obligations are retained as such.

For terminology, start with the [relevant glossary section](GLOSSARY.md#scales-and-renormalization); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This document records mathematical design, not a Lean implementation or completed
fidelity theorem. It supplements source/SOURCE_ANALYSIS.md with equations inspected in
the full primary texts.

## Chosen sufficient presentation

Use Euclidean [renormalization](GLOSSARY.md#scales-and-renormalization)-group flow with auxiliary BRST/BV fields **only to fix
perturbative predictions**. The actual physical theory remains the
positive-Hilbert-space [Wightman](GLOSSARY.md#quantum-fields-and-distributions) theory. Requiring a physical Wilson-lattice limit is
unnecessary. A gauge-fixed [ghost](GLOSSARY.md#graded-gauge-symmetry) algebra is auxiliary and must not be confused with
the physical [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions).

Primary sources downloaded and read:

* Fröb–Holland, arXiv:1603.08012, 70-page version: https://arxiv.org/abs/1603.08012 . Local `work/central/frob-holland.pdf` and `.txt`.
* Fröb–Holland–Hollands, arXiv:1511.09425, 82-page version: https://arxiv.org/abs/1511.09425 . Local `work/central/frob-holland-hollands.pdf` and `.txt`.
* Itzykson–Zuber [27], locally downloaded full textbook, printed pp649–659 and 672–680. Local `work/iz-relevant.txt`.

The later papers are additional precise mathematical presentations of the perturbative
requirements, not authorities that change §4. Their applicability and interpretation
must be justified.

## Actual G enters vertices, propagators and observable insertions

Choose an invariant positive quadratic form B on the actual compact simple Lie algebra,
and a B-orthonormal basis. The [structure constants](GLOSSARY.md#gauge-fields-and-observables) are **defined** by `[e_b,e_c]=Σ_a f^a_bc e_a`, not independent
data. Basis changes must act on every color index. Overall normalization of B is coupled
to normalization of g; it is not a physical restriction on gauge groups.

Use elementary fields `(A^a_µ,B^a,cbar^a,c^a)` with engineering dimensions `(1,2,1,1)`, [Grassmann](GLOSSARY.md#graded-gauge-symmetry)
parity `(0,0,1,1)` and usual [ghost number](GLOSSARY.md#graded-gauge-symmetry). The free covariance is determined by the
quadratic gauge-fixed action. The cutoff multiplier is

`R_Λ(p)=exp(-|p|²/Λ²)`,

`C^{Λ,Λ0}(p)=(R_Λ0(p)-R_Λ(p)) C_free(p)`.

The YM color factor is δ_ab in orthonormal coordinates. Take ξ=1 if one wants a single
convenient auxiliary gauge and establish independence on physical [cohomology](GLOSSARY.md#graded-gauge-symmetry).
Fröb–Holland equations (2.13)–(2.19), printed pp11–12, spell out the matrix; their
field-redefined B makes the [bosonic](GLOSSARY.md#quantum-fields-and-distributions) [Gaussian](GLOSSARY.md#perturbative-calculations) positive. Do not silently use a
different ordering of `(B,cbar,c)` from their matrix.

The cubic, quartic and ghost [vertices](GLOSSARY.md#perturbative-calculations) are coefficient derivatives of the same pure-YM
gauge-fixed [BV](GLOSSARY.md#graded-gauge-symmetry) action. In the conventions of 1511.09425, equations (46)–(49),
pp13–14, the action is

`S = 1/2 ∫ tr F∧*F + 1/2 ∫tr B∧*B + ξ²/2 ∫tr(*d*A∧d*A) + i∫tr cbar∧d*D c`

with the explicit [antifield](GLOSSARY.md#graded-gauge-symmetry) couplings `-∫tr((sA)∧A‡+(sc)∧c‡+(s cbar)∧cbar‡+(sB)∧B‡)`. Their [BRST](GLOSSARY.md#graded-gauge-symmetry) transformations
after B-redefinition are `(Dc, -ig[c,c]/2, ξB-iξ²*d*A, iξ*d*Dc)`. All formal color contractions use the actual
bracket. Equivalent real-Lie-algebra conventions may remove i factors, but every action,
propagator and BRST relation must transform coherently.

Composite insertions are finite derivative monomials in these elementary
fields/antifields. Physical [ghost-number](GLOSSARY.md#graded-gauge-symmetry)-zero classes correspond to invariant [curvature](GLOSSARY.md#gauge-fields-and-observables)
[jet](GLOSSARY.md#graded-gauge-symmetry) polynomials, using BRST cohomology: 1511.09425 Lemma1, eq(42), p12, and
eq(14), p7. The classical-to-quantum link is **[cohomological](GLOSSARY.md#graded-gauge-symmetry) with renormalized mixing**,
not a bijection of raw syntactic words.

## Fixed amplitudes: flow and boundary conditions

Let L^{Λ,Λ0} be the formal generating functional of connected [amputated](GLOSSARY.md#perturbative-calculations) amplitudes. Its
definition must be coefficientwise, using finite Wick contractions and convergent
momentum integrals at fixed cutoffs, or equivalently the explicitly fixed flow with
fixed local boundary data. It is not an arbitrary amplitude family.

With convolution and graded variational derivatives fixed, its flow is

`∂_Λ L = (ℏ/2) <δ, (∂_Λ C) * δ> L - (1/2) <δL,(∂_Λ C)*δL>`.

This is 1603.08012 (2.20), p12. The coefficient version (2.25), p13, is a one-loop
contraction of L at [loop order](GLOSSARY.md#perturbative-calculations) l−1 minus the sum of products over ordered partitions of
external legs and l′+(l−l′)=l. Graded signs follow the **fixed** ordered exterior
algebra of odd generators; they are not arbitrary constants. The action fixes tree
boundary coefficients. [Power-counting](GLOSSARY.md#scales-and-renormalization) renormalizable [counterterms](GLOSSARY.md#scales-and-renormalization) have local degree≤4 and
preserve the stated global symmetries.

At higher orders:

* irrelevant amplitudes and momentum derivatives vanish at Λ=Λ0;
* relevant ones vanish at Λ=0 and zero momentum;
* [marginal](GLOSSARY.md#scales-and-renormalization) ones have finite renormalization conditions at Λ=µ and zero momentum.

These are pp13–14. There is no permission to assign arbitrary momentum-dependent finite
amplitudes. Freedom is finite-dimensional local coefficients and is constrained by
[Ward](GLOSSARY.md#graded-gauge-symmetry) identities and coupling/field normalization. Thus quantifying over admissible
finite counterterms is not quantifying over the meaning of predictions. A fixed
canonical normalization is possible, but a universal nonperturbative specification
should allow finite scheme changes or prove the chosen normalization sufficient.

Single-insertion normalization (4.2), p21, is particularly explicit:

`D^B_0 L^{µ,Λ0}(O_A)=δ_A^B δ_l0` for `[B]≤[A]`,

`D^B_q L^{Λ0,Λ0}(O_A)=0` for `[B]>[A]`.

Here D^B_p is **defined** by ordered functional derivatives, momentum derivatives,
powers of i and multiindex factorials, equation(4.1), pp20–21. Finite changes of the
insertion basis generally change this simple normalization. Their effect must be
transported through every OPE and quantum observable formula.

For multiple insertions, define [oversubtracted](GLOSSARY.md#short-distance-products-and-contact-terms) F_D by the explicit linear flow (4.3), p21,
and zero boundary extraction at µ for `[B]<D` and at Λ0 for `[B]≥D`, (4.4). Set

`G_D(⊗A)=∏_k L(O_Ak) - ℏ F_D(⊗A)`.

This is (4.5), p21. The full functionals are G=G_0.

## Coefficients are extracted, not assigned

Definition3, equations (5.5)–(5.7), pp41–42, fixes regulated coefficients:

`C_A^1(x)=G^{µ,Λ0}(⊗_k O_Ak(xk))`,

`C_A^B(x)=D^B_0 [G^{µ,Λ0}(⊗A)-Σ_[C]<[B] C_A^C(x) L^{µ,Λ0}(O_C(xs))]`.

The sum is finite in every bounded [engineering degree](GLOSSARY.md#gauge-fields-and-observables). Take the coefficientwise [UV](GLOSSARY.md#scales-and-renormalization) limit
Λ0→∞ proved in that framework. Coefficients intentionally use Λ=µ>0, even though
physical correlations use the [IR](GLOSSARY.md#scales-and-renormalization) limit. Omitting this distinction changes the
coefficient scheme.

Free initial coefficients come from Wick pairings plus Taylor expansion of uncontracted
jets at xs. Equations(7.25)–(7.27), p65, give the finite graph sum with edges

`f_vw(x,y)=∂_x^v∂_y^w C^{µ,∞}(x,y)` and `g_vw(x,y)=∂_x^v (x-y)^w/w!`.

Scalar covariance is `exp(-µ²|x-y|²/4)/(4π²|x-y|²)`; YM adds the fixed Lorentz/color/ghost factors.
Coefficients are not merely arbitrary distributions with the right [scaling degree](GLOSSARY.md#short-distance-products-and-contact-terms).

## Why the shorter recursion alone does not close the definition

Theorem4, equation(1.2.1), p7, gives

`ℏ ∂_g C_A^B = ∫dy Σ_E I^E [-C_EA^B + Σ_[C]<[B] C_A^C C_EC^B + Σ_k Σ_[C]≤[Ak] C_EAk^C C_A(k→C)^B]`.

All products in this equation are combined **before integration**: individual terms may
be UV/IR divergent while the combination is integrable. Implementing totalized integrals
of separate nonintegrable terms is unsound.

For gauge theories `O_I=Σ_E I^E O_E` is not simply ∂gS to all orders. Theorem5 pp8–9 only gives
`O_I=∂g L|g=0+O(g)+O(ℏ)` and `qhat O_I=dO`. Theorem6 equations(1.2.6)–(1.2.9), pp8–9, simultaneously
constrains qhat and the quantum antibracket. The discussion p66 explicitly says the
inputs are free coefficients **and the interaction operator constrained by [gauge invariance](GLOSSARY.md#gauge-fields-and-observables)**.
Calling recursion alone deterministic from classical vertices would overstate the
result. A full flow/cohomology definition supplies those constraints.

## Gauge Ward constraints and anomaly qualification

1511.09425 Theorem4 eq(10), pp6–7, requires

`Σ_k <O_A1 ... (qhat O_Ak) ... O_As>_c = ℏ Σ_k<l <... (O_Ak,O_Al)_ℏ ...>_c`,

including fixed Grassmann signs. The quantum antibracket is supported on coincidence
diagonals. Require `qhat²=0`, graded Jacobi and compatibility, eqs(11)–(13). The
classical term is the BV differential of the same action. Away from coincidence,
ghost-number-zero physical correlations descend to its cohomology.

The theorem's anomaly-removal hypothesis is the relevant [equivariant cohomology](GLOSSARY.md#graded-gauge-symmetry)
vanishing. For pure YM, p7 explains that the possible gauge anomaly is parity odd and
the cutoff preserves full Euclidean O(4), so its invariant subsector is absent for all
semisimple Lie algebras, including su(n) with n>2. **Do not restrict universal G to
groups having no cubic [Casimir](GLOSSARY.md#gauge-fields-and-observables)**, which would wrongly omit SU(3). Do not assume that
arbitrary chiral matter would enjoy this argument; the target is pure YM.

## Weak OPE and UV relation imposed on actual fields

Let Q's renormalized composite operators provide the actual same-domain field
distributions. Exact coefficient distributions may be [witness](GLOSSARY.md#reading-a-formalization) data; their **all-order
perturbative asymptotics** must be fixed by the above generator, after allowed finite
[operator mixing](GLOSSARY.md#scales-and-renormalization) and coupling reparametrization. It is unnecessary and potentially too strong
to require a unique nonperturbative resummation. Terms flat in the [running coupling](GLOSSARY.md#scales-and-renormalization) can encode
legitimate nonperturbative effects.

1603.08012 Theorem1 eqs(1.1.2)–(1.1.3), pp4–5, prescribes for total input degree d_A and
truncation `[B]<D`, at each fixed perturbative order and δ>0,

`τ^(d_A-D+δ) [ <∏O_Ak(τxk)> - Σ_[B]<D C_A^B(τx)<O_B(τxs)> ] →0`,

`τ^(d_A-[B]+δ) C_A^B(τx)→0`.

These are weak/distributional scaling limits on the configuration domain with distinct
points. For the nonperturbative target, use test functions on relative [cluster](GLOSSARY.md#short-distance-products-and-contact-terms)
configurations compactly supported away from partial diagonals, and [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) test
functions supported away from the cluster. Pair the remainder before taking τ↓0. State
explicitly which field-word vectors test the weak identity. Extending across
partial/contact diagonals needs the fixed local extension/mixing rules, not pointwise
multiplication of singular distributions.

Arbitrary normalizable states or norm convergence are stronger than the primary
perturbative theorem, so avoid adding them without an argument.

For all-order agreement, fix the formal coefficient series C_pert(g), [beta](GLOSSARY.md#scales-and-renormalization)(g), and
anomalous matrix [gamma](GLOSSARY.md#scales-and-renormalization)(g) from the generator. For each N compare the scaled and
[RG](GLOSSARY.md#scales-and-renormalization)-transported exact coefficient to its degree-N formal truncation, requiring a
remainder [little-o](GLOSSARY.md#analysis-and-asymptotics) of the last retained running-coupling order, weakly against those
test functions. The running coupling and matrix transport may be exact witness functions
if their derivative/asymptotic jets match the fixed formal beta/gamma to all orders.

They cannot supply free beta coefficients. Include logarithmic powers and possible
matrix-Jordan logarithms rather than replacing mixing by scalar exponents.

This paragraph is a proposed sufficient interpretation. A full equivalence/sufficiency
argument connecting its exact topology, truncation convention, and uniformity to §4
remains necessary; the perturbative paper proves its own orderwise result, not all such
nonperturbative claims.

## Fixed numerical checks and stress normalization

[IZ](GLOSSARY.md#notation-and-source-abbreviations) printed p653 eq(13-81) gives, for pure theory and conventional B
normalization,

`beta(g)= -(11 C_A/3)g³/(4π)² -(34 C_A²/3)g⁵/(4π)^4 + O(g⁷)`.

Here C_A is derived by contraction of actual structure constants. The group-sensitive
leading coefficients are mandatory checks on any generator; two terms alone are
insufficient to encode perturbative renormalization. IZ p651 eq(13-75) gives composite
anomalous matrices; p678 eq(13-155) gives their action on OPE coefficients. IZ pp677–678
eqs(13-149), (13-152)–(13-155) fix dimensional power and RG logarithms.

[Stress tensor](GLOSSARY.md#scales-and-renormalization) must be a symmetric conserved rank-two operator in the same renormalized
family. Normalize its integrated charges by the actual Q translations, rather than admit
a zero tensor satisfying conservation. A clean [smeared](GLOSSARY.md#quantum-fields-and-distributions) formulation uses spatial
cutoffs approaching one and a time [smearing](GLOSSARY.md#quantum-fields-and-distributions) of integral one, with charge convergence
on the common field domain to the generator action. Conservation is a distribution
identity. Allow the usual divergence improvements and contact terms while preserving
charge action.

IZ p679 explains protected current/stress anomalous dimension; eqs(13-159)–(13-163),
pp679–680, derive normalized Ward identities. Those equations are current examples, not
a ready-made complete stress-field construction; the chosen charge-limit domain must be
reviewed.

## Exact remaining implementation obligations

Implementing only the classical vertices, beta polynomial or abstract OPE remainder is
incomplete. The generator needs ordered graded monomials; coefficient extraction;
regulated covariance and Wick contraction/integration; local [counterterm](GLOSSARY.md#scales-and-renormalization) constraints;
composite insertions and oversubtractions; quantum Ward identities/cohomology; and the
exact finite redefinition laws transporting coefficients into the actual Q field basis.
References above provide concrete formulas for these tasks. No arbitrary Prop field or
arbitrary prediction family is an acceptable stand-in.

The scheme equivalence needed here is local finite renormalization: field maps are
[filtration](GLOSSARY.md#gauge-fields-and-observables) preserving formal matrices (with derivatives/contact terms specified),
invertible with classical leading term, and coupling changes preserve the fixed leading
normalization. Transport both incoming and outgoing OPE labels, the action insertion,
beta/gamma and Q's correspondence by the same maps. Merely calling a free matrix a
scheme change is not enough; locality, degree, symmetry, BRST compatibility and
normalization are its fixed defining equations.

A proof that this presentation is sufficient for §4, independent of a preferred
[regulator](GLOSSARY.md#scales-and-renormalization), remains required before calling the target complete.

## Explicit transport and matching convention for implementation

Write the coefficient distribution as a multilinear map `C(x): V^⊗s→V` on the label space.
On homogeneous labels define `D_λ(v_A)=λ^[A] v_A`. The canonically normalized coefficient is

`Cbar_λ = D_λ⁻¹ ∘ C(λx) ∘ D_λ^⊗s`.

Its `(A1,...,As;B)` component is `λ^(Σ[Ak]−[B]) C_A^B(λx)`. This convention prevents accidental reversal of
engineering weights.

Fix the running-operator convention `d_t Q_run(v)=−Q_run(Γ(g_t)v)` and define the label transport by
`Q_µ(v)=Q_µexp(t)(R_t v)`. Then

`g'_t=β(g_t)`, `R'_t=Γ(g_t)∘R_t`, `R_0=id`.

The RG-stripped coefficient is consequently

`Ctilde_λ = R_t ∘ Cbar_λ ∘ (R_t⁻¹)^⊗s`, `t=log(1/λ)`.

At scale µ=1 in the chosen units, fixed perturbative distributions `Cpert_n(x)` supply the
comparison. For every finite set of input/output labels, compactly supported
relative-configuration test f away from partial diagonals, and N≥0, impose

`< Ctilde_λ − Σ_(n=0)^N g_t^n Cpert_n , f > / g_t^N → 0` as λ↓0.

Thus degree N means the last retained power g^N, and the error is little-o(g^N), not
merely little-o(1). At fixed unit geometric configuration, coefficient logarithms are
part of Cpert_n, while large scale logarithms are transported by the running system. If
the selected normalization begins with a Laurent power or extra fixed g-dependent
invariant representatives, factor that explicit power/basis map before applying this
formula; silently treating F(g)-labels as g-independent monomials is incorrect.

For an elementary finite basis change `Q_new(v)=Q_old(Mv)`, the coefficient law is `C_new=M⁻¹∘C_old∘M^⊗s`; all
mixing orientations follow from this identity. If matrix entries are written as
`Q_new,A=M_A^B Q_old,B`, this becomes the usual incoming product of M and outgoing inverse M.
Conventions must state whether arrays represent maps on labels or arrays of operator
components.

The clean transport formula uses equal-canonical-degree blocks. Lower-degree filtered
mixing requires dimensionful factors `µ^([A]−[B])`; include those in M and perform the Dλ
conjugation before comparing schemes. A particular mass-independent homogeneous scheme
is a possible presentation, but conversion from the flow normalization to it is
equivalence work that cannot be assumed by a name.

Smooth β and Γ may be witness completions of the **fixed** formal perturbative jets.
Require all-order small-g expansion with those jets, g>0, g_t→0, invertibility on finite
filtration pieces, and the ODE/initial conditions above. The leading pure-YM conditions
`β(g)=−b0 g³+O(g⁵)`, `Γ(g)=O(g²)` imply g_t is of order t^(-1/2) and R grows at most as powers of t
on each finite block, once the elementary ODE estimates are proved.

This prevents transport with arbitrary rapidly growing matrices from hiding wrong
principal UV behavior. Flat corrections to β or Γ may remain, because the source does
not choose a unique nonperturbative completion. They cannot change any prescribed
perturbative coefficient. Arbitrary initial mixing must instead be accounted for as a
normalized admissible scheme map, not slipped into R_0.

This exact transport/remainder convention is a proposed sufficient interpretation
assembled from the primary RG and weak-OPE formulas. Its relation to the source must
still be defended; the perturbative references do not prove the existence of the
nonperturbative data it asks a future proof to supply.
