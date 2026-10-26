# Independent integrated review: connected Ward hierarchy and local extension

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This review uses three examples to test local [Ward](GLOSSARY.md#graded-gauge-symmetry) identities and distributional
extensions. The key lesson is that agreement away from collisions, even with scaling
bounds, can leave unrestricted dependence on [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) insertions.

Read P1–P3 and the explicit delta-function example before the proposed extension
interface. The final repair audit describes the changes actually inspected after those
findings.

For terminology, start with the [relevant glossary section](GLOSSARY.md#short-distance-products-and-contact-terms); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This stage reviewed the staged connected/multi-Ward, continuum/cohomology recovery,
stress, contact and generated-coefficient definitions. It concerns mathematical
consistency and [source fidelity](GLOSSARY.md#reading-a-formalization), not existence of Yang–Mills. No owner files were edited.

## P1 — Background all-momentum permutation condition (repaired)

The frozen [ConnectedInsertionFlow.lean](../YangMills/ConnectedInsertionFlow.lean) SHA256 `8ac69782461d9037723439fbfaa5d725286c4a213f6f9786069c92c13b35d615`, lines 105–107, imposed `graded_external` on **all
input lists including empty** and every external momentum tuple. The same background has
`reduced_extension`, ignoring the last momentum. Full permutation symmetry for arbitrary
unbalanced tuples, together with last-momentum independence for every permuted leg list,
forces independence of each momentum. That contradicts the nonzero fixed classical cubic
momentum jets.

The physical background coefficients contain a conservation delta and their reduced
extension only needs graded symmetry on [balanced momenta](GLOSSARY.md#notation-and-source-abbreviations). Inserted amplitudes do have
independent momenta. The root confirmed the finding and is restricting this additional
connected condition to nonempty input; the already defined balanced background symmetry
then applies. This is a concrete non-vacuity repair, not an added physical restriction.

## P2 — Finite A2 channels cannot discard their irrelevant UV tail (initial defect repaired)

`ContactAnomalyTransport.transportedContactAnomaly` initially represents every finite-cutoff channel as a finite combination of
ordinary standard single-insertion fields L_C with `dim C + |w| + 3 <= dim A + dim B`. But its `ultraviolet_boundary`
equates this to the **full** internal-momentum Taylor coefficient of the regulated bare
[BV](GLOSSARY.md#graded-gauge-symmetry) pair kernel, including derivatives of the exponential [regulator](GLOSSARY.md#scales-and-renormalization) R_UV(p).
Those derivatives create [UV](GLOSSARY.md#scales-and-renormalization)-suppressed higher-dimensional external field
amplitudes.

Concrete test: select one even gauge component phi (dimension 1), A=phi^2/2 (dimension
2) and B=phi* phi (the [antifield](GLOSSARY.md#graded-gauge-symmetry) times phi, dimension 3). Their tree bare pair kernel
with two external phi legs at q=0 is a nonzero constant times R_UV(p). Set r=2 and
w=(2,0,0,0). Its centered Taylor coefficient is nonzero, of order UV^-2 times the phi^2
field amplitude; the classical point bracket has no w=2 term.

The support bound permits only C of dimension 0 for this channel, hence only the unit;
ordinary L_unit has no tree two-phi amplitude. The initial equality thus demands zero
equal nonzero.

[FHH](GLOSSARY.md#notation-and-source-abbreviations) 1511.09425 after (346) explicitly explains that the A2 full UV boundary has
irrelevant terms and does not have the standard single-insertion normalization. The
coefficient bounds assign it an effective dimension; they do not say its finite-cutoff
boundary is a finite polynomial of that dimension. In contrast A1 uses the separate
anomaly family and normalized transport, so that interface does not make the same
mistake.

Required repair: make the finite A2 channel its own amplitude family with the full fixed
UV seed and homogeneous insertion flow; impose finite-dimensional degree-bounded local
recovery only on the appropriate continuum/local anomaly coefficients. Alternatively
split the regulator-suppressed irrelevant Taylor tails into an explicit remainder and
prove the chosen split equivalent to the source. Merely declaring finite L_C
coefficients to obey the small dimension bound cannot match the full regulated seed.

Sent urgently to root and [QFT](GLOSSARY.md#quantum-fields-and-distributions) owner.

## P3 — Off-diagonal limits, scaling bounds and Ward identities do not fix local extensions

The root's concern is valid. For an allowed dimension channel, a correction of the form

`delta(x1-x2) h(x1-x3,q)`

with h smooth, translation/O(4)-compatible, and supported away from the total collision
is invisible to all off-insertion-diagonal observations. It can obey the pair transverse
scaling bound and vanish near the total collision. A Ward-closed output channel can
leave the homogeneous Ward equations unable to exclude this unrestricted spectator
dependence. This is a loophole mechanism, not a claimed fully constructed Lean
countermodel of every assembled equation.

A finite number of delta derivatives with an **arbitrary distribution along its
diagonal** is not yet an admissible finite local insertion [counterterm](GLOSSARY.md#scales-and-renormalization). A genuine pair
insertion counterterm must feed its output into the same lower-insertion hierarchy;
spectator dependence then comes from that hierarchy, not a freely selected h.

### Concrete extension interface

For every finite insertion block B and output local monomial C:

1. Choose only finitely many constant coefficient channels `Z_B^(C,alpha)` at each coupling/loop order, with exact [power-counting](GLOSSARY.md#scales-and-renormalization), ghost/parity, tensor/color and translation constraints. Coefficients may depend on reference scale/coupling/cutoff as prescribed; they may not depend on spectator positions or external momenta as arbitrary functions.
2. Define a fixed block-collapse [Schwartz](GLOSSARY.md#quantum-fields-and-distributions) test map: differentiate in the block's normal/removed coordinates, restrict those positions to its selected anchor, retain spectator positions/order and external momenta, and replace B by C in the label list.
3. Evaluate every correction by the **same lower-[arity](GLOSSARY.md#perturbative-calculations) connected W/L distribution** on that collapsed test. For several collision blocks, use finite set partitions with exact independent coupling/loop [Cauchy](GLOSSARY.md#perturbative-calculations) allocations and [Koszul](GLOSSARY.md#graded-gauge-symmetry) signs. For full moments, require the corresponding same-hierarchy distributional [cumulant](GLOSSARY.md#short-distance-products-and-contact-terms) relation.
4. Anchor one reference extension by an actual Taylor/forest-subtracted finite-cutoff [weak limit](GLOSSARY.md#analysis-and-asymptotics) on compact tests. A freely selected reference distribution with the same bulk values would leave the loophole unchanged. The fixed subtraction must handle nested/disjoint collision forests and normal derivative bounds; remaining finite changes are precisely the partition-local channels above.
5. Apply the restored Ward/contact equations to these same coefficients and extensions, including overlaps, rather than infer their normalization from Ward closure alone.

For B={1,2} in a three-insertion amplitude, this permits only sums of delta derivatives
times the same two-insertion W(C at x1, A3 at x3), with finite constants; it excludes
delta(x1-x2) times an unrelated h(x1-x3,q).

## Positive checks and scope

- `pairWardSign` has the correct extra p_i term for the raw odd antibracket: b(A,B)=(-1)^p(A)(A,B) is the graded-symmetric binary coderivation. Moving the pair to the front and returning its odd output to position i gives prefixOdd(i)+p_i+p_j*betweenOdd. Singles use the ordinary prefix sign. No extra sign defect was found.
- Anchored proper insertion splits count each unordered split once; covariance contraction is graded symmetric, so no extra half is required. The canonical partition encoding chooses the least member of each block, and its Koszul sign accounts for regrouping odd insertions. The finite moment shift (-hbar)^(arity-number of blocks) agrees with the same G_0 convention.
- The distributional cumulant helper forms tensor products only on disjoint position/momentum blocks, using genuine compact [mollification](GLOSSARY.md#analysis-and-asymptotics) and explicit limits. It connects full contact values of connected and disconnected W rather than permitting an independent moment hierarchy. It does not by itself determine the allowed extension of the connected hierarchy (P3).
- `firstPairContactTest` correctly differentiates the removed second coordinate with positive sign before restricting to the first-centered diagonal. The support theorem correctly proves every such derivative vanishes on separated insertion tests.
- The corrected invariant [dictionary](GLOSSARY.md#notation-and-source-abbreviations) respects equality-on-connections modulo the same generated quantum exact relation. At intrinsic degree zero no lower-degree primitive exists, closing the fake higher-loop unit ambiguity for classically zero labels. The recovery equation uses generated raw outputs and actual same-W insertion fields rather than a classical input polynomial treated as its own dual.
- Stress [graph grading](GLOSSARY.md#scales-and-renormalization) correctly has exponent [external-leg](GLOSSARY.md#perturbative-calculations) count+2 loop-2, so the canonical kinetic tree stress is g^0. The source dictionary keeps the regular numerator and clears g^-2 by multiplication by g^2; no totalized inverse at g=0 is used. Its [RG](GLOSSARY.md#scales-and-renormalization) transport and differential agree with the column-label convention. The classical symbol is only tree-normalized; no all-order tracelessness is asserted.

## Disposition

P1 is a concrete inconsistent-condition repair acknowledged by root. P2 requires
changing the finite A2 transport representation before it can be used as a faithful,
nonvacuous prescription. P3 requires a genuine partition-local extension prescription
tied to the same lower-insertion data; scaling/support/Ward checks alone are
insufficient. These issues concern specification definitions and supporting fidelity
work, not an unproved continuum existence theorem. A successful build would not resolve
them.

## Repair audit — current staged definitions

Read the revised primary files [ConnectedInsertionFlow.lean](../YangMills/ConnectedInsertionFlow.lean), [ContactAnomalyTransport.lean](../YangMills/ContactAnomalyTransport.lean), [PartitionContact.lean](../YangMills/PartitionContact.lean), and [LocalContactRenormalization.lean](../YangMills/LocalContactRenormalization.lean)
directly after the owner reported the repairs.

**P1:** `ConnectedInsertionFlow.lean:106` now explicitly requires `input ≠ []` in `graded_external`. This removes the
background contradiction identified above. The background's separate balanced-momentum
permutation condition remains the appropriate one.

**P2:** `FullContactAnomaly` is now an independent amplitude family. Its entire finite-UV boundary
is the regulated bare contact seed, and its evolution is the same homogeneous insertion
equation with background `L []`. Only the finite local representative is subject to
the engineering bound. At the common positive normalization scale it matches relevant
extraction jets; the actual coupling derivatives of the full-minus-local remainder must
vanish weakly as the UV cutoff is removed.

In the earlier two-phi counterexample the UV^-2 term can now remain in the full
amplitude at finite cutoff and disappear in the remainder limit. The finite coefficient
support no longer excludes that regulator tail. I found no further blocking defect in
this repair. This is a concrete continuum local-recovery condition, whose construction
and source equivalence still require proof.

**P3:** The new partition interface removes arbitrary spectator dependence from the
counterterm data. Every block coefficient has only scale/cutoff, its own input labels,
one output label, normal derivative, and perturbative-order arguments. It has no
spectator position/momentum arguments. The finite partition sum evaluates its outputs
through the same lower-arity finite-cutoff `G_0` computed from `L/F`, on an
actual derivative-and-diagonal-collapse Schwartz test. The identity partition retains
the original finite-cutoff amplitudes.

The UV limit is imposed on this complete expression on all compact tests, and one
universal `Z` serves every [IR](GLOSSARY.md#scales-and-renormalization) cutoff. There is no independent
already-extended reference distribution. Thus the specific unrestricted `delta12*h`
mechanism above is no longer admitted merely by choosing an unrelated extension. This
does allow the intended finite local normalization freedom; it does not require a unique
scheme.

The diagonal embedding has a proved norm lower bound and copies external momenta, so the
restriction is a genuine proper Schwartz map. The finite normal grid kills derivatives
at block centers. Block members are sorted in original insertion order, and the sign
counts regrouping inversions relative to the actual fixed root enumeration. The degree
bound includes the [codimension](GLOSSARY.md#short-distance-products-and-contact-terms) `4*(block size-1)`. Counterterm output/derivative sums are finite
at each order.

Still needed for a complete fidelity argument are the supporting normalization/forest
equivalence and finite-normalization freedom results, extraction-basis duality,
compatibility with the restored Ward identities and distributional [cumulants](GLOSSARY.md#short-distance-products-and-contact-terms), and the
relevant tensor/color covariance facts. These are not established just by defining the
interface. In assembly, the Ward, cumulant, and contact conditions must constrain this
exact same `W`, `L`, `F`, `Z` and limit, as the module
documentation explicitly requires.

The audit does not prove [analytic](GLOSSARY.md#analysis-and-asymptotics) existence or reopen admission of the full target.

Current disposition: the three concrete defects/loopholes in this report have received
structurally adequate repairs on inspection. No fresh blocking mathematical
inconsistency was found in those exact repairs. Strict compilation, if successful,
remains separate evidence from source fidelity and existence.
