# Actual smooth canonical insertion determinacy

> **Historical snapshot.** Findings and “remaining work” below refer to the
> reviewed stage. For current status, read the [final fidelity argument](FINAL_FIDELITY_ARGUMENT.md)
> and [verification record](VERIFICATION_RECORD.md).

This report explains how the original canonical normalization data determine smooth
insertion amplitudes. The proof works with finite derivative data and does not require
[analytic](GLOSSARY.md#analysis-and-asymptotics) functions or a convergent infinite Taylor series.

Read [determinacy](GLOSSARY.md#analysis-and-asymptotics), insertion uniqueness and Fourier reconstruction in that order. The
stress sections then separate transport of the physical tensor from the different
dimension bound on its [BRST](GLOSSARY.md#graded-gauge-symmetry) variation.

For terminology, start with the [relevant glossary section](GLOSSARY.md#analysis-and-asymptotics); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

## What the canonical data determine

CanonicalProjectorDeterminacy now proves genuine C∞ uniqueness from the ORIGINAL
admissible canonical low rows at zero and high rows at all momenta. It does not add
all-coordinate boundary clauses. The proof uses actual projector/coordinate transport,
odd cancellation at coincident momenta, the finite admissible-subindex dichotomy, the
actual differential ideal and finite anchored one-coordinate smooth-[jet](GLOSSARY.md#graded-gauge-symmetry)
determinacy. No [analyticity](GLOSSARY.md#analysis-and-asymptotics) or growth assumption appears.

## Applying determinacy to the insertion flow

CanonicalLinearInsertionUniqueness applies that result to the same actual homogeneous
insertion flow by loop/arity induction. Its internal [arity](GLOSSARY.md#perturbative-calculations) restriction prevents
using scale constancy at unproved higher arities. InsertionFlowConditions.single_unique
derives uniqueness from the actual fixed-background and original single-insertion
conditions, including every insertion position through actual translation. No response
existence is asserted or needed for the fixed meaning.

## Recovering the Fourier/Taylor density

Literal FourierTaylorUniformEnumeration now recovers the actual finite
reducedTaylorDensity amplitude as the same amplitude's finite diagonal Taylor
polynomial, including all source/color enumeration, Fourier phases, [Koszul](GLOSSARY.md#graded-gauge-symmetry) signs and
factorials. IntegratedTaylorJetRecovery then proves the actual integrated density
recovers every required nonempty μ jet after conserving-momentum composition. The final
raw pointwise/reduced response comparison is still being connected using these proved
identities.

## Transporting the physical stress tensor

GeneratedStressFieldTransport proves that the reference same-C stress binding, actual
same-C transport and transported [dictionary](GLOSSARY.md#notation-and-source-abbreviations) numerator force the same physical T at every
running scale. SameStressRG.field_derived does not use the structure's declared
same_field condition to establish it.

## Smoothness and the remaining source comparison

A separate central definition correction replaces 45 unintended analytic ContDiff-order
top conditions in 18 files by actual C∞ order infinity. This removes an unjustified
convergence restriction on exact stress/finite scheme coupling germs; genuine complex
analytic continuation conditions remain in place. See SMOOTH_ORDER_REVIEW.md and its
exact inventory.

Source scope is narrowed in the [assembled-scope review](ASSEMBLED_SCOPE_REVIEW.md): existence/restoration of
witnesses, universal [cohomology](GLOSSARY.md#graded-gauge-symmetry) classification and [beta](GLOSSARY.md#scales-and-renormalization) representative uniqueness
are not extra admission gates. The remaining concrete source comparison includes the
ordered ghost/antifield convention across covariance, [master action](GLOSSARY.md#graded-gauge-symmetry), sources and Fourier
rules. The source eq.(67) [ghost](GLOSSARY.md#graded-gauge-symmetry) order has opposite displayed signs; a consistent
transpose/rephasing dictionary must be exhibited before claiming exact agreement. Exact
target admission stays closed while this finite dictionary and final response comparison
are open.

## Stress dictionary filtration correction

The physical stress dictionary now uses the same active dimension-four sector and its
frame. Previously it enumerated every active dimension-five label while demanding that
every enumerated label have dimension at most four, even when its coefficient was zero.
This imposed an unjustified restriction on the full composite basis. Dimension-five
descendants are allowed in that basis. The BRST stress-response cutoff remains five:
that is a distinct bound on the variation, not the stress dictionary itself.

Both the current filtered assembly and the earlier homogeneous comparison assembly use
the corrected dictionary sector.
