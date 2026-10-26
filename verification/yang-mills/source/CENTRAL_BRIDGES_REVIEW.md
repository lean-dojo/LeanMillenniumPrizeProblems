# Central same-action and same-quantum bridges

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This report connects four descriptions of the same construction: the action and symmetry
differential, connected and effective-action insertions, quantum observable classes, and
classical scaling dimensions.

Each section states what a supporting theorem establishes and where its hypotheses still
matter. The concluding obligations belong to this historical stage.

For terminology, start with the [relevant glossary section](GLOSSARY.md#graded-gauge-symmetry); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

These results support the fixed generated proposal. They neither prove Yang--Mills
existence nor by themselves admit the exact full target.

## Actual action and its local differential

`FullBVActualGaugeNilpotency`, `FullBVActualAuxiliaryNilpotency` and `FullBVAntighostAntifield` complete the four basic interacting [nilpotency](GLOSSARY.md#graded-gauge-symmetry)
identities directly from the same local [master-action](GLOSSARY.md#graded-gauge-symmetry) [vertices](GLOSSARY.md#perturbative-calculations). The actual Lie
[structure constants](GLOSSARY.md#gauge-fields-and-observables), odd-[jet](GLOSSARY.md#graded-gauge-symmetry) anticommutation, total derivative product rules and Jacobi
identity discharge the nonlinear terms. The shifted [antighost](GLOSSARY.md#graded-gauge-symmetry) and auxiliary [antifield](GLOSSARY.md#graded-gauge-symmetry)
squares also vanish.

`FullBVGhostAntifield` extracts the full [ghost](GLOSSARY.md#graded-gauge-symmetry) antifield coordinate by actual right Euler
differentiation of every physical and source [vertex](GLOSSARY.md#perturbative-calculations). A formula for that coordinate
is not a proof of its nilpotency. The remaining gauge antifield coordinate, those two
remaining antifield squares, polynomial promotion, classical master equation and
divergence descent remain open. The earlier kernel review's A/B nilpotency work is
superseded here.

## Actual all-order source Legendre inverse

`LegendreSignFactorization` proves the universal weighted [Koszul](GLOSSARY.md#graded-gauge-symmetry) partition factorization. `LegendreSelectedTransport`
applies it to the actual selected legs, independent external momenta, root sums and
finite-index casts. `LegendreCompositionGraded` reindexes the actual complete finite sums and proves the
recursive insertion inverse has graded statistics. Its `insertion_inverse_from_source` proves the full
inverse equation without assuming symmetry of an unknown inverse. The source adapter
derives the existing directional compatibility guard from actual flow statistics.

The background law is used only at [balanced momenta](GLOSSARY.md#notation-and-source-abbreviations); nonempty local source insertions retain
all independent momenta. This is essential for local [Callan--Symanzik](GLOSSARY.md#scales-and-renormalization) insertions. The separate
background [Legendre](GLOSSARY.md#perturbative-calculations) equations still require the actual quadratic target's balanced
statistics and its normalization; this result does not silently discharge that issue.

## Actual mixing columns and quantum classes

`QuantumLabelCohomology` turns the same [dictionary](GLOSSARY.md#notation-and-source-abbreviations)'s finite Q primitive into an actual boundary in
its all-hbar complex. Thus labels equal on all smooth connections have equal generated-Q
classes, and classical finite basis resolution preserves that class. `GeneratedGammaCohomology.gammaColumn_class`
identifies each computed [gamma](GLOSSARY.md#scales-and-renormalization) column with the class of the actual local mixing
insertion at every positive normalization scale. Its input dimension bound is the bound
needed to inhabit the chosen finite slice, not an extra physical condition.

The existing `coordinates_field` separately gives the same resolution on the actual composite
operators. No injectivity, quantum surjectivity or ghost Hilbert quotient follows or is
required.

## Actual engineering dimensions

`ClassicalDilation` dilates smooth connections themselves and proves the [curvature](GLOSSARY.md#gauge-fields-and-observables) and every
iterated [covariant derivative](GLOSSARY.md#gauge-fields-and-observables) have the assigned engineering weights. A homogeneous actual curvature
polynomial therefore has the stated power of scale under evaluation on those same
connections. Lower-degree mixtures remain allowed. The proof does not establish
availability of a homogeneous quantum subtraction scheme.

## Remaining fidelity boundary

Full BV/CME and background Legendre identities, local [cohomological](GLOSSARY.md#graded-gauge-symmetry) classification of
finite [counterterms](GLOSSARY.md#scales-and-renormalization) and scale anomalies, availability of the chosen homogeneous massless
[Ward](GLOSSARY.md#graded-gauge-symmetry)-compatible scheme, and the cited axiomatic-framework equivalences remain
supporting work. Exact full-target admission stays closed. The absence of a
nonperturbative existence proof is a separate matter and does not explain these
remaining obligations.
