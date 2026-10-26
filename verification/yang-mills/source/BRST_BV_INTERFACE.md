# BRST/BV interface for fixed renormalized predictions

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This design note explains how gauge symmetry is encoded algebraically and attached to
the perturbative amplitudes. The fields, [ghost](GLOSSARY.md#graded-gauge-symmetry) variables and antifields form a
graded algebra; the signs and derivative order are part of the mathematics.

Read the field grades before the derivative and bracket formulas. The [Ward](GLOSSARY.md#graded-gauge-symmetry)
equations then show why a quantum differential cannot be chosen independently of the
amplitudes. The unfinished-work lists describe the original design stage.

For terminology, start with the [relevant glossary section](GLOSSARY.md#graded-gauge-symmetry); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This specifies algebra and equations to implement. It does not label a partial
implementation complete. Primary source is Fröb–Holland–Hollands, arXiv:1511.09425
(82-page PDF), supplemented by Fröb–Holland arXiv:1603.08012 (70 pages). Source PDFs and
extracted text are in this directory.

## Checked classical core

[BRST.lean](../YangMills/BRST.lean) imports the existing actual-G [renormalization](GLOSSARY.md#scales-and-renormalization) definitions. It defines
exterior-valued ghosts, proves their squares vanish and their generators anticommute,
defines the actual-bracket quadratic ghost variation, and proves the degree-one
[Chevalley–Eilenberg](GLOSSARY.md#graded-gauge-symmetry) differential squares to zero using G's Jacobi identity. It also
defines the [antifield](GLOSSARY.md#graded-gauge-symmetry)-free [superjet](GLOSSARY.md#graded-gauge-symmetry) algebra as commuting gauge/auxiliary [jet](GLOSSARY.md#graded-gauge-symmetry)
polynomials tensored with exterior ghost/antighost jets. Canonical even partial
derivatives and odd exterior contractions define an explicit coordinate differential,
total jet derivatives, and the full antifield-free classicalBRST map on every
polynomial.

Finite partial support is proved by Clifford and tensor induction; the coordinate sums
therefore cannot vanish through infinite-support [totalization](GLOSSARY.md#reading-a-formalization). Linearity and exact
generator evaluation are proved. Ordered external differentiation and [augmentation](GLOSSARY.md#graded-gauge-symmetry) fix
the polynomial-to-amplitude coefficient map, including factorials/signs.

This is a genuine [Grassmann](GLOSSARY.md#graded-gauge-symmetry) algebra, not an assignment of real values to ghost fields.
The full graded Leibniz and [nilpotency](GLOSSARY.md#graded-gauge-symmetry) equivalence proofs for the concrete classicalBRST
map, antifields and the local-functional [BV](GLOSSARY.md#graded-gauge-symmetry) quotient remain unfinished. The CE
nilpotency result is the ghost sector, not a claim of full [BRST](GLOSSARY.md#graded-gauge-symmetry) nilpotency.
Exterior contraction's graded product identity is proved by induction; it supplies the
core odd-partial Leibniz step.

The checked images are the real-bracket **unshifted** convention `sA=Dc`, `sc=−g[c,c]/2`,
`s cbar=B`, `sB=0`. The positive diagonal covariance currently used by the flow file
employs the shifted B convention of primary equations(45)–(49). Before composing these
modules, transport the action and s through that field substitution, including its i
factors, or derive an equivalent real convention. Combining unshifted transformations
with shifted propagators is not valid.

## Canonical jet labels and grades

Let BasicField be the actual-G fields already defined. Extended generators are basic or
antifield labels, plus ordinary derivative multiindex α:Fin4→N. The basic grades are

| field | [engineering dimension](GLOSSARY.md#gauge-fields-and-observables) | [ghost number](GLOSSARY.md#graded-gauge-symmetry) | Grassmann parity |
|---|---:|---:|---:|
| A | 1 | 0 | 0 |
| c | 1 | 1 | 1 |
| cbar | 1 | −1 | 1 |
| B | 2 | 0 | 0 |

For the antifield of φ set dimension `3−dim φ`, ghost number `−1−gh φ`, parity
`1−parity φ`. Add |α| to dimension, leave other grades unchanged. This is exactly primary
TableI and eq(54), p14. The engineering assignment is a convention chosen for these
[analytic](GLOSSARY.md#analysis-and-asymptotics) estimates; it differs from some physics ghost assignments, so document it.

On homogeneous jet words all grades add. Odd generators exterior commute, even generators
commute. A finite word with repeated identical odd jet is zero; different odd derivative
jets are independent generators. The algebra is not merely a list of noncommuting words:
relations must be imposed/proved and coefficient extraction must respect them.

## Graded derivative signs

For an ordered word `w=x1...xn`, the left partial derivative by a generator z is the sum
over matching occurrences i of the word with xi removed, multiplied by

`(-1)^(p(z) Σ_(j<i) p(xj))`.

The right derivative instead uses `Σ_(j>i) p(xj)`. For a homogeneous polynomial F,

`D_R,z F = (-1)^(p(z)(p(F)+1)) D_L,z F`.

This convention is fixed by `δF=(δ_R F/δφ)δφ=δφ(δ_L F/δφ)`, primary eq(57), p15. It determines all loop and
partition signs. For the ordered covariance convention `C_cbar,c=−C`, `C_c,cbar=+C`, the
[Gaussian](GLOSSARY.md#perturbative-calculations) contraction operator `Δ_C=(1/2)Σ_MN C_MN D_L,N D_L,M` satisfies `Δ_C(φ_Aφ_B)=C_AB`; the odd reverse-order
term has both the derivative and covariance signs. This is a useful exact regression
lemma.

For jets, variational derivatives on local functionals are [Euler derivatives](GLOSSARY.md#graded-gauge-symmetry): sum over α of
`(-∂)^α D_(φ,α)`. Total derivatives ∂µ must first be defined as even derivations sending each
jet α to α+eµ. The quotient by total divergences implements integration by parts. One
cannot apply an ordinary finite polynomial derivative to a local functional and call it
the BV variational derivative.

## Fixed classical BV bracket and master action

Primary eq(56), p15, is

`(F,G)=∫Σ_K[(δ_R F/δφK)(δ_L G/δφ‡K)−(δ_R F/δφ‡K)(δ_L G/δφK)]`.

The bracket is odd, ghost number+1. In local-functional dimension conventions it lowers
the sum of engineering dimensions by3. Its antisymmetry is

`(F,G)=−(-1)^((pF+1)(pG+1))(G,F)`.

The classical action including the specified actual-G antifield couplings is fixed by
eq(49). Define `s_hat F=(S,F)`. Prove `(S,S)=0` from the actual Lie bracket, invariance of
B, graded integration by parts and auxiliary [gauge fixing](GLOSSARY.md#graded-gauge-symmetry); then graded Jacobi proves
`s_hat²=0`. These are eqs(50)–(60), pp14–15. Neither S nor s_hat is a
proof-author-selected meaning.

On the pointwise classical jet algebra before the local-functional quotient, the basic
BRST images extend by the odd Leibniz rule and must commute with total derivatives.
Descending to the [divergence quotient](GLOSSARY.md#graded-gauge-symmetry) and proving [master-action](GLOSSARY.md#graded-gauge-symmetry) identities are separate supporting
lemmas.

## Allowed counterterms: finite-dimensional local freedom, restored Ward identities

Primary eq(70), p16, fixes `L_bare=S_int+O(ℏ)`. At finite cutoff its higher-loop [counterterms](GLOSSARY.md#scales-and-renormalization) may
be BRST breaking, because the cutoff itself breaks BRST. The source explicitly says to
allow the most general local polynomial of dimension≤4 preserving unbroken E(4) and
ghost number. Forcing each finite-cutoff [counterterm](GLOSSARY.md#scales-and-renormalization) to be classically BRST closed can
exclude the required restoration terms.

One-insertion counterterms are linear maps δ:local operators→local operators with
δ=O(ℏ), preserved ghost number/parity/global tensor type and output dimension≤input
dimension. This is eqs(77)–(79), p18. Higher insertion counterterms are local on partial
coincidence diagonals, with derivative order bounded by dimension. Their coefficients
are finite-dimensional at every bounded label degree and perturbation order. Translation
invariance makes coefficients independent of spacetime position; arbitrary smooth
momentum functions are not local counterterms.

The prescribed flow generates amplitudes from that local data; continuum Ward identities
constrain it. Remaining homogeneous local counterterm solutions must be classified
modulo s_hat-exact terms and divergences, with the physical coupling/field normalization
fixing the [gauge-invariant](GLOSSARY.md#gauge-fields-and-observables) F² direction. For a compact simple algebra the quadratic invariant
is one-dimensional after choosing B. In the parity-even pure-YM sector the CP-odd F∧F
direction is excluded in the auxiliary perturbative scheme; this need not add parity
invariance of a future nonperturbative vacuum as a new axiom.

A proof of this cohomology/stability classification is still required; naming it is not
a substitute.

Thus the appropriate interface quantifies finite local counterterm coefficients
satisfying explicit [power-counting](GLOSSARY.md#scales-and-renormalization), global covariance, tree normalization, flow equations
and all restored Ward equations. This is legitimate [witness](GLOSSARY.md#reading-a-formalization) freedom. An arbitrary
continuum coefficient distribution tagged “renormalized” remains illegitimate.

## Quantum BRST and contact data are coefficient families constrained by amplitudes

Use formal coefficient families Q_A^B and B_AB^{C,α} in g and ℏ. Fixed classical terms
are the above s_hat and BV bracket; corrections begin at ℏ. Their support/grading
equations are

* Q_A^B=0 unless `[B]≤[A]+1`, `ghB=ghA+1`, `pB=pA+1`.
* B_AB^{C,α}=0 unless `[C]+|α|=[A]+[B]−3`, `ghC=ghA+ghB+1`, `pC=pA+pB+1`.

The second gives the distribution

`(O_A(x),O_B(y))_ℏ=Σ_C,α B_AB^{C,α} O_C(x) ∂_x^α δ⁴(x−y)`.

This is 1603.08012 eqs(1.1.5)–(1.1.6), p5. It is a concrete [partial-diagonal](GLOSSARY.md#short-distance-products-and-contact-terms) distribution; a
freely chosen [predicate](GLOSSARY.md#reading-a-formalization) “local [contact term](GLOSSARY.md#short-distance-products-and-contact-terms)” is insufficient. The dimension bounds make
its sum finite.

Impose q_hat²=0, odd bracket antisymmetry, odd Jacobi, and

`q_hat(F,G)_ℏ=(q_hat F,G)_ℏ+(-1)^(pF+1)(F,q_hat G)_ℏ`.

These are primary1511.09425 eqs(11)–(13), pp6–7. **Do not require a naive quantum
Leibniz rule with the raw classical pointwise product.** Composite renormalization
changes products and creates [contact terms](GLOSSARY.md#short-distance-products-and-contact-terms); the cited theorem does not justify adding that
extra axiom. Classical s is a derivation, while quantum q_hat is fixed on composite
labels through the amplitude Ward identities.

For connected [amputated](GLOSSARY.md#perturbative-calculations) functionals L, the full restored conditions are primary
Proposition17 eqs(281)–(283), pp54–55:

`s_hat0 L=0`, `s_hat0 L(O_A)=L(q_hat O_A)`,

`s_hat0 L(⊗A)=Σ_k L(⊗_(j≠k) A_j ⊗q_hat A_k)+Σ_(k<l)L(remaining⊗(A_k,A_l)_ℏ)`.

These are formal coefficientwise distribution identities in external fields/antifields,
not merely vacuum scalar equations. The signs for odd inserted composites are determined
by adjoining a distinct auxiliary odd ε_k to each odd insertion, applying the [bosonic](GLOSSARY.md#quantum-fields-and-distributions)
formula to ε_k O_Ak and extracting the ordered ε product. This is the source's explicit
prescription immediately after eq(283). It avoids guessing contact permutation signs.
For disconnected functionals G the corresponding identity has **−ℏ** in front of the
contact term, 1603.08012 eq(3.3.4), p20; do not copy the connected sign into it.

Gauge-invariant [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) closure then imposes eq(1.1.4), p5, on the **same extracted**
coefficient system. Input q_hat terms minus output q_hat terms minus ℏ contact terms
vanish, with the same [Koszul](GLOSSARY.md#graded-gauge-symmetry) prescription. Asymptotic OPE alone does not imply that
exact Ward equation; the paper explicitly warns about this on p6 and p20.

## Anomaly removal and non-free physical correspondence

The gauge anomaly is a local form at ghost number1 and form degree4. The relevant
equivariant [cohomology](GLOSSARY.md#graded-gauge-symmetry) vanishes in parity-invariant pure YM; groups with cubic
invariants are not excluded. Finite corrections remove the action anomaly A0. For
physical insertions the residual A1 obeys a consistency equation; primary
eqs(360)–(364), p71, writes its leading term as `A1(O)=s_hat B1(O)` with B1 of the same
[engineering degree](GLOSSARY.md#gauge-fields-and-observables) and ghost number as O, and changes the insertion counterterm by −B1.

This precisely explains allowable [operator mixing](GLOSSARY.md#scales-and-renormalization) and why arbitrary quantum q_hat corrections
cannot simply be chosen independently.

A completed implementation must construct the deformed maps from the fixed
amplitude/counterterm system or impose all these coefficient equations on that system.
Then prove that [ghost-number](GLOSSARY.md#graded-gauge-symmetry)-zero physical cohomology, mapped to Q's observable family
with fixed mixing relations, gives the intended invariant [curvature](GLOSSARY.md#gauge-fields-and-observables) polynomials. Mere
q_hat nilpotency with an unused classical action would leave the disconnected-sector
loophole.

## Concrete unfinished steps

1. Extend the checked classical generator images to the superjet graded derivation and transport the B shift consistently with the flow covariance.
2. Add antifields, total derivatives/Euler operators and the quotient of local functionals by divergences; prove the actual master equation and BV identities.
3. Enumerate local counterterm and insertion spaces with exact dimension/ghost/parity/covariance constraints; normalize the physical coupling direction and transport [finite mixing](GLOSSARY.md#scales-and-renormalization).
4. Attach full coefficientwise restored Ward equations to the same flow amplitudes and local contact distributions; prove equivalence of the auxiliary-ε and explicit Koszul implementations.
5. Establish physical cohomology/correspondence and its finite-renormalization covariance before claiming fixed all-order YM predictions.

These are central mathematical tasks. The checked ghost core is useful progress toward
them, not evidence that they are finished.

## Coherent shifted-B component action and its fixed free differential

For the current component flow convention with positive ghost density `∂cbar·Dc`,
Feynman gauge and positive auxiliary B², a coherent complex auxiliary convention is

`sA=Dc`, `sc=−g[c,c]/2`, `s cbar=div A+iB`, `sB=i div Dc`.

It makes `s² cbar=div Dc+i² div Dc=0`; invariance of the gauge-fixing/ghost sector follows by integration
by parts: `sS_gf=(div A+iB)div Dc` and `sS_ghost=−(s cbar)div Dc`. This is a component convention equivalent to the
source's form/antighost phase convention only after a consistent field substitution;
that equivalence must be proved rather than asserting identical printed signs.

With `S_BV=S−Σ(sφ)φ‡`, the free action contains the quadratic physical/gauge-fixing terms and
the source bilinears

`−∂µc A‡µ −(div A+iB)cbar‡ −i∆c B‡`.

The interaction action excludes these bilinears and adds the g-dependent [vertices](GLOSSARY.md#perturbative-calculations)

`−g[Aµ,c] A‡µ + g[c,c]c‡/2 −ig div[A,c] B‡`.

The last term can be written `+ig[Aµ,c]∂µB‡` modulo a total derivative. All brackets are
actual-G contractions. There is no independent cbar‡ interaction at this order.

The **derived** free [ST](GLOSSARY.md#graded-gauge-symmetry) images in this convention are

`s0 Aµ=∂µc`, `s0 c=0`, `s0 cbar=div A+iB`, `s0B=i∆c`,

`s0 A‡µ=−∆Aµ+∂µ cbar‡`, `s0B‡=B−i cbar‡`,

`s0 cbar‡=∆c`, `s0 c‡=−∆cbar−div A‡+i∆B‡`.

They follow from the fixed right/left [Euler derivative](GLOSSARY.md#graded-gauge-symmetry) convention and S0, not a free
functional operator. Composing s0 on each generator cancels exactly, using commuting
total derivatives; e.g. on c‡ the ∆div A, ∆B and ∆cbar‡ contributions cancel separately.
The flow agent owns an explicit freeActionVertices list; the [QFT](GLOSSARY.md#quantum-fields-and-distributions) agent owns
coefficient extraction of this same S0.

## Bare coupling and mixing normalization: exact textbook source

Itzykson–Zuber printed p593, eqs(12-124)–(12-126), decomposes the Ward-restored action
into gluon kinetic coefficient Z3, cubic gZ1, quartic g²Z4, ghost kinetic Ztilde3 and
ghost [vertex](GLOSSARY.md#perturbative-calculations) gZtilde1. It fixes

`A0=sqrt(Z3) A`, `c0=sqrt(Ztilde3)c`, `cbar0=sqrt(Ztilde3)cbar`,

`g0=g Z1/(Z3)^(3/2)`, `λ0=λ/Z3`.

The ST constraints are

`Z1/Z3=Ztilde1/Ztilde3=Z4/Z1`.

Thus `g0=g Ztilde1/(Ztilde3 sqrtZ3)=g sqrtZ4/Z3` as well. All roots and reciprocals are unit [formal-series](GLOSSARY.md#perturbative-calculations) operations with
constant coefficient1. No arbitrary root branch is permitted. Printed pp600–603,
eqs(12-157)–(12-168), gives the all-order local counterterm decomposition; p604 repeats
the universality ratios to all orders.

One must extract Z3 from the quadratic action **including S0**, Z1 from the cubic
coefficient divided by g, and then divide out the gluon wavefunction factors. The raw
cubic coefficient alone is not g0. Composite matrices likewise come from actual
insertion jet coefficients and their unit formal inverse, with dimension/tensor/ghost
constraints.

This textbook decomposition is a Ward-preserving renormalization presentation. A raw
finite-cutoff flow action also contains BRST-breaking local counterterms, so projecting
one of its coefficients and naming it Z1 does not prove this decomposition. A finite
scheme transport and Ward-restored decomposition, including
gauge-fixing/shifted-B/antifield rescalings, is required to identify the bare
coordinates. Until that bridge is encoded, beta/gamma derived from arbitrary g0/Z inputs
would remain disconnected.
