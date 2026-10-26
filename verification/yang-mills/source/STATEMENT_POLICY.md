# Current statement policy

The fixed target is `YangMills.YangMillsExistenceAndMassGap.{u}`, which requires one `FilteredGeneratedCandidate` for every allowed
[gauge group](GLOSSARY.md#gauge-fields-and-observables). The specification is an **internally reviewed formal proposal** whose source
fidelity has not been independently validated. Existence of its
witnesses and external acceptance remain separate questions.

This policy explains how to describe that status without confusing a mathematical
definition, a proof and a review. The [glossary](GLOSSARY.md#reading-a-formalization) introduces those distinctions.

## Which documents govern current claims?

Use the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md), [current source crosswalk](CURRENT_JW4_READINESS_CROSSWALK.md) and [final adversarial review](FINAL_ADVERSARIAL_REVIEW.md). Earlier implementation reviews are
historical snapshots; their open-work lists do not create new admission requirements.
The [verification record](VERIFICATION_RECORD.md) reports the completed checks.

Internal readiness does not close external scrutiny. Claims that no further
gap was identified describe the internal review, not a theorem excluding
under-constraint or over-constraint. The [witness audit](WITNESS_AUDIT.md) records
concrete unresolved validation questions. Newly demonstrated defects require
revisiting the interpretation or definitions regardless of earlier status.

## What is fixed, and what may a witness supply?

Every required meaning is a concrete mathematical definition. A [witness](GLOSSARY.md#reading-a-formalization) may supply
fields, operators, coefficient distributions, formal corrections and constructions
satisfying those definitions. It cannot supply the meaning of Yang–Mills, the prescribed
predictions, or an arbitrary correctness [predicate](GLOSSARY.md#reading-a-formalization). No existence proof, axiom or
assumed conclusion fills a missing definition.

The physical theory must be the same object throughout the following links:

1. The actual group and Lie bracket determine the [master action](GLOSSARY.md#graded-gauge-symmetry) and generated
   flow, including the quantum symmetry differential.
2. The corrected local observable correspondence uses those generated data,
   with the full [Ward](GLOSSARY.md#graded-gauge-symmetry) and [Callan–Symanzik](GLOSSARY.md#scales-and-renormalization) ([CS](GLOSSARY.md#scales-and-renormalization)) normalization identities.
3. Vacuum correlations and the operator product expansion ([OPE](GLOSSARY.md#short-distance-products-and-contact-terms)) use those
   same physical fields and prescribed predictions.
4. The [stress tensor](GLOSSARY.md#scales-and-renormalization)'s charge limits recover the same translations and
   physical [Hamiltonian](GLOSSARY.md#operators-and-spectrum) whose spectrum defines the gap.

Quantum operator relations and lower-degree mixing are allowed. Finite projections used
for diagnosis do not replace the full Ward and CS identities. The glossary explains
[gauge symmetry](GLOSSARY.md#graded-gauge-symmetry), [scale equations](GLOSSARY.md#scales-and-renormalization) and [OPE terminology](GLOSSARY.md#short-distance-products-and-contact-terms).

## What does the auxiliary prescription require?

The [Gaussian](GLOSSARY.md#perturbative-calculations) prescription fixes perturbative predictions. Its justification uses the
same-action [gauge-fixing](GLOSSARY.md#graded-gauge-symmetry), classical master equation and [nilpotency](GLOSSARY.md#graded-gauge-symmetry) proofs, together with
the source contraction, Fourier and projector comparisons. It does not require a
particular construction of the nonperturbative theory.

The original admissible canonical low and high boundary rows are retained. Their smooth
[determinacy](GLOSSARY.md#analysis-and-asymptotics) and insertion/OPE uniqueness are supporting theorems; stronger all-coordinate
boundary conditions are not added implicitly. See [the current action-prescription argument](FINAL_FIDELITY_ARGUMENT.md#actual-yangmills-action-and-prescription).

## Regularity, stress and interpretation boundaries

In the pinned calculus API, `C∞` means `ContDiff` order `∞`, not [analytic](GLOSSARY.md#analysis-and-asymptotics)
outer `⊤`. Exact smooth completions may have divergent formal expansions and flat
terms. Genuine complex analytic [Wightman](GLOSSARY.md#quantum-fields-and-distributions) continuation conditions remain required. The
[smoothness review](SMOOTH_ORDER_REVIEW.md) explains the distinction.

The stress [dictionary](GLOSSARY.md#notation-and-source-abbreviations) has dimension bound four; its [BRST](GLOSSARY.md#graded-gauge-symmetry) response has bound five.
The [trace anomaly](GLOSSARY.md#scales-and-renormalization) centers both actual fields using the same vacuum. Equivalently, its
identity contribution is computed from their vacuum expectations. This does not fix
absolute local vacuum energy or add a positive cutoff-profile condition. See the
[stress argument](FINAL_FIDELITY_ARGUMENT.md#same-observables-predictions-and-stress).

The source footnote's dimension-[filtration](GLOSSARY.md#gauge-fields-and-observables) expectation is guidance. It does not require
a quantum bijection or a universal classification theorem. [Beta](GLOSSARY.md#scales-and-renormalization)-representative
uniqueness, general [cohomology](GLOSSARY.md#graded-gauge-symmetry) classification, a PVM/SNAG construction, [OS](GLOSSARY.md#notation-and-source-abbreviations)
reconstruction of an already complete Minkowski model, and construction or restoration
of existence witnesses are not extra readiness requirements. The [glossary](GLOSSARY.md) explains
these terms. Any such stronger result claimed independently needs its own proof.

## Verification and acceptance

The source registry preserves required versus guidance roles and provenance
classifications. Its labels neither establish [semantic fidelity](GLOSSARY.md#reading-a-formalization) nor activate admission by
themselves.

A future proof must have the exact closed [universe-polymorphic](GLOSSARY.md#reading-a-formalization) target and pass independent
inspection of the compiled environment and all axiom dependencies. [QFT](GLOSSARY.md#quantum-fields-and-distributions)-only
checking remains separate. Kernel validity, source interpretation and external
acceptance must be reported distinctly; this repository issues no Clay Mathematics
Institute certificate. The [certification contract](../CERTIFICATION.md) gives the admission rules.
