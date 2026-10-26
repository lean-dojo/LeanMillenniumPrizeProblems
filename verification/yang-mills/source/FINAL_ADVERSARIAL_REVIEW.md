# Internal adversarial review of the finite prescription

> **Review status:** This is an internal AI-assisted assessment, not independent
> human expert validation. Its historical conclusions remain revisable;
> `FINAL` and `READINESS` in file names are workflow labels. See the
> [witness audit and open validation questions](WITNESS_AUDIT.md).

> **Current disposition:** The concrete source/action, canonical reconstruction,
> Fourier/Taylor, normalization, insertion/OPE uniqueness and stress-transport
> checks are recorded as completed. See the [verification record](VERIFICATION_RECORD.md).
> No existence proof or external acceptance is asserted.

The review below preserves the staged findings and their subsequent repairs.
Instructions to keep admission closed refer to that earlier stage; use the [current policy](STATEMENT_POLICY.md)
for present admission rules.

This review checks that the finite perturbative prescription and the physical theory
remain connected. Its central example is a [ghost](GLOSSARY.md#graded-gauge-symmetry)-covariance sign discrepancy:
changing derivative order can change displayed signs without changing the full
contraction.

Follow the initial finding through the explicit contraction/Fourier repair and final
resolved scope. The closing recommendation records integration conditions that the
current disposition reports as completed.

For terminology, start with the [relevant glossary section](GLOSSARY.md#perturbative-calculations); [the document map](DOCUMENTATION_GUIDE.md) places this note in the wider
reading sequence.

This review inspects the current [PRIMARY](GLOSSARY.md#notation-and-source-abbreviations) staged definitions and the pinned [FHH](GLOSSARY.md#notation-and-source-abbreviations)
1511.09425 / [FH](GLOSSARY.md#notation-and-source-abbreviations) 1603.08012 text. It concerns the concrete finite-order
prescription and its bindings. It does not establish existence, universal scheme
classification, or full-target admission. The [analytic](GLOSSARY.md#analysis-and-asymptotics)-order correction must pass its
dependent rebuild; all new [determinacy](GLOSSARY.md#analysis-and-asymptotics) lemmas use genuine C-infinity.

## Finding requiring a precise finite convention comparison

FHH printed p.16, Eq. (67), explicitly orders its basic fields as (A,c,cbar,B). Its
displayed ghost covariance has C(c,cbar) = -C and C(cbar,c) = +C. PRIMARY
[Renormalization](GLOSSARY.md#scales-and-renormalization).basicCovariance instead assigns C(c,cbar) = +C and C(cbar,c) = -C;
PerturbativeFlow.basicDerivativeCovariance uses that same orientation. The
implementation is internally consistent with its ordered-left calculus and positive
component ghost density. These are not literally identical printed covariance entries.

The implemented [BRST](GLOSSARY.md#graded-gauge-symmetry) convention is sA = Dc, sc = -g[c,c]/2, s(cbar) = div A + iB,
sB = i div Dc. FHH Eqs. (46)-(49) use form-valued fields and explicit imaginary
bracket/ghost phases. Existing source/BRST_BV_INTERFACE.md already says that the
component convention must be transported consistently rather than identified by printed
signs. The YM owner confirms no existing exact source-to-component [Gaussian](GLOSSARY.md#perturbative-calculations) and
[antifield](GLOSSARY.md#graded-gauge-symmetry) pullback theorem is available.

This is not a counterexample or a proved sign error. A transpose resulting from
derivative conventions, together with fixed field/antifield phases and Lie-algebra
conventions, can change these displayed entries. The remaining comparison is concrete:
state one substitution for basic fields, inverse-dual antifields, the odd differential
and Fourier convention, then check its free quadratic action, Gaussian contraction, and
all nonlinear antifield [vertices](GLOSSARY.md#perturbative-calculations). Alternatively cite a primary component prescription
with exactly these conventions and compare directly to it.

This is finite algebra, not a demand for an additional universal renormalization or
[cohomology](GLOSSARY.md#graded-gauge-symmetry) theorem.

## Formulas inspected and what they establish

* Actual group and action: physicalActionVertices uses the actual color-frame
  [structure constants](GLOSSARY.md#gauge-fields-and-observables). antifieldActionVertices contains all three nonlinear
  sectors: c c c-dagger / 2, -A c A-dagger, and +i A c partial B-dagger.
  The last term is the integration-by-parts representative of -sB B-dagger.
  The quadratic vertices include the shifted-B sector, ghost kinetic term,
  and every free antifield coupling. No physical-only cubic/quartic substitute
  was found. FullBVBridge.densityAmplitude_masterAction ties that same density
  to these literal vertices. This is an internal exact link, distinct from
  the printed convention comparison above.
* Graded contractions: linearFlowRHS uses the ordered M,N insertion and the
  actual covariance derivative with the p,-p pairing and (2pi)^-4 measure.
  The background RHS is one half of linear minus quadratic; the insertion
  RHS has half the linear term and one full mixed quadratic term. Ordered
  subset unshuffles and loop convolution are explicit. The independent
  insertion contraction integrates its connecting momentum; the background
  contraction fixes it from momentum conservation. Ghost and antifield
  parities remain intrinsic, not numerical commuting ghost values.
* Regulated [BV](GLOSSARY.md#graded-gauge-symmetry): rightDerivativeSign implements (-1)^[p(z)(p(F)+1)]. The
  antibracket retains its two ordered terms. The BV Laplacian explicitly
  orders the right antifield derivative before the basic derivative and
  carries its loop shift. The free BV kernel cancels R only on the kinetic
  Hessian sector and retains it on free antifield couplings, matching the
  distinction in source (290). The action defect contains s0 L, half (L,L),
  and the shifted-loop Delta L. It is not a [witness](GLOSSARY.md#reading-a-formalization)-selected anomaly seed.
* Local insertion [ST](GLOSSARY.md#graded-gauge-symmetry): bareInsertionWardDefect subtracts the actual LOCAL
  evolutionary ST of the normalized monomial. It does not replace it by
  the integrated [divergence quotient](GLOSSARY.md#graded-gauge-symmetry). monomialsBelow(A.dimension+2) includes
  exactly the possible dimension <= A.dimension+1 output range. The quantum
  [Ward](GLOSSARY.md#graded-gauge-symmetry) limit and pair anomaly are bound to the same actual finite seeds and
  same lower-insertion engine; they are not supplied independently.
* Normalization/extraction: FH (4.1)-(4.2) uses a canonical admissible
  monomial projector with i^|w| and multiplicity factorial. The implemented
  local vertices use -ip for each ordinary derivative. The finite projector
  factors invert these phases, including repeated even fields. Independent
  all-[arity](GLOSSARY.md#perturbative-calculations) [polarization](GLOSSARY.md#analysis-and-asymptotics) proofs and canonical low/high determinacy support
  actual [jet](GLOSSARY.md#graded-gauge-symmetry) reconstruction; the source conditions have not been replaced
  by stronger all-coordinate high-[UV](GLOSSARY.md#scales-and-renormalization) premises. FHH (91),(95), Table II and
  FH (2.25)-(2.27) distinguish relevant [IR](GLOSSARY.md#scales-and-renormalization)-zero background conditions from
  point-insertion relevant normalization at positive mu. That distinction
  is retained. It is not necessary to add a separate relevant-mu restoration
  tower as an axiom of the directly imposed simultaneous massless family.
* [OPE](GLOSSARY.md#short-distance-products-and-contact-terms) extraction: the regulated output is the actual disconnected-minus-
  [oversubtraction](GLOSSARY.md#short-distance-products-and-contact-terms) functional, followed by the dimension-triangular recurrence
  subtracting lower-dimensional insertions before the same output projector.
  This is the order of FH (5.5)-(5.7), not a freely selected coefficient table.
  UV and IR limits have compact/nonexceptional test guards and actual
  integrability, avoiding totalized-integral or collision-limit shortcuts.
* Scale/gamma: full [CS](GLOSSARY.md#scales-and-renormalization) residuals use the same computed [Gamma](GLOSSARY.md#scales-and-renormalization) and corrected
  insertion/lift. euclideanGammaSeries uses actual classical basis
  coordinates, and physical gamma is W gamma_E W^-1 with the same finite
  Wick substitution as words/OPE. The filtered frame allows lower-degree
  mixing and scale dependence. R acts before canonical powers; those powers
  are not commuted through a triangular matrix. No additional homogeneous
  quantum scheme assumption was found in the filtered replacement.
* Physical links: one common [running coupling](GLOSSARY.md#scales-and-renormalization), coherent finite frames, actual
  same-C transport, all-order coefficient matching, and actual same-C vacuum
  words occur together. Stress uses the same C, its actual [Hamiltonian](GLOSSARY.md#operators-and-spectrum) and
  charge limits, and the same generated numerator/dictionary. The centered
  trace relation fixes the [curvature](GLOSSARY.md#gauge-fields-and-observables)-square classical evaluation and removes
  only a scalar identity part computed from the same vacuum [one-point](GLOSSARY.md#scales-and-renormalization) functions.
  I found no independently excited [spectator](GLOSSARY.md#short-distance-products-and-contact-terms) sector hidden by these bindings.

## Limits of this verdict

No additional missing central [predicate](GLOSSARY.md#reading-a-formalization) or explicit unrelated/free-model counterexample
was found in the formulas inspected. In particular, possible null/exact directions in CS
witnesses do not by themselves authorize arbitrary physical predictions: the full
same-Gamma identities and same-C word matching remain required. No uniqueness of every
beta/gamma witness or quantum classical-label injectivity is asserted or needed for this
observation.

The fixed reference-scale coefficient comparison is a chosen simultaneous presentation.
Actual dimensional covariance of the background is now proved; insertion covariance
still consumes its honest canonical uniqueness adapter. This review does not infer
arbitrary-scheme covariance, convergence of formal series, or a nonperturbative theory
from those supporting results.

The remaining finite source-comparison item above should be resolved explicitly before
saying the source [dictionary](GLOSSARY.md#notation-and-source-abbreviations) is completely checked. Its resolution would remove this
specific objection; it should not be replaced by a generic, unbounded request for
universality or Ward-restoration existence proofs.

## Concrete contraction/Fourier repair proved after the review

NEW SourceCovarianceOrder.lean proves, for all actual basic species, that the printed
(67) covariance is precisely the transpose of the implementation's chronologically
ordered covariance. More substantively, it proves equality of the COMPLETE Gaussian and
scale-flow contraction operators on the actual FullBV [superjet](GLOSSARY.md#graded-gauge-symmetry) algebra when the
derivative order is translated at the same time. Source (86) writes a product D_K D_L,
acting rightmost first; the implementation's externalJetDerivative [K,L] applies K
first.

The new all-arity printedLeftDerivativeWord_eq_reverse proves this exact conversion for
every basic and antifield jet. No commutation of odd derivatives or independent
covariance witness is used.

The same file proves the source exp(+ipx) jet factor equals the implemented exp(-ipx)
factor under one global p -> -p substitution, and combines these facts into an exact
all-arity coefficient-term identity for ANY polynomial of the same FullBV algebra, hence
also the actual master polynomial. This discharges the apparent covariance-sign
discrepancy at the concrete Gaussian/contraction and ordered Fourier-coefficient level.
It is stronger than saying the entries happen to look transposed, and weaker than
falsely claiming that two raw matrices with unchanged derivative order agree.

A remaining caution applies only to the form-valued action presentation: source s
anticommutes with exterior d and odd forms. Its equations (46)-(49) cannot be compared
to ordinary coefficient derivatives by simply reading form symbols as commuting
numerical components. The exact density-amplitude bridge already concerns the
implemented full master density. A claim that it is literally a pullback of the source's
total-form expression must state that componentization, or use the coherent component
BRST [gauge-fixing](GLOSSARY.md#graded-gauge-symmetry) presentation directly.

The contraction result does not assert a guessed [antighost](GLOSSARY.md#graded-gauge-symmetry) phase or silently promote
that separate claim.

## Final resolved scope and assembled negative controls

The total-form caveat above is NOT an additional admission gate. A direct standard
component BV presentation is sufficient and is already concrete:
FullBVGaugeFixedAction.masterDensity_gaugeFermion_curvature identifies the same
implemented master density with the actual nonabelian curvature action, actual ST of its
fixed [gauge fermion](GLOSSARY.md#graded-gauge-symmetry), and full antifield sources, up to two explicit divergence currents.
FullBVSourceCharacteristicIdentity identifies those source terms with minus the same
nonlinear BRST characteristics, again with its explicit integration-by-parts current.

Together with the actual master-equation/nilpotency proofs, this is precisely a coherent
component BV [gauge fixing](GLOSSARY.md#graded-gauge-symmetry) of pure Yang--Mills. Source (34) allows this [gauge-fermion](GLOSSARY.md#graded-gauge-symmetry)
construction; a literal total-form (47) pullback theorem is unnecessary when that
stronger literal claim is not made. The source analyst independently agrees with this
sufficient-presentation route. The new contraction and Fourier proofs provide the
remaining explicit computational convention translation, rather than relying on an
unexplained assertion about signs.

The corrected PRIMARY FilteredRG.GeneratedSector now selects active degree FOUR for
stressFamily and its frame. The prior active-five choice, together with the dictionary's
per-label degree<=4 clause, overrestricted the entire basis even when coefficients
vanished. Dimension-five BRST responses belong in the [cocycle](GLOSSARY.md#graded-gauge-symmetry) output bound, not the
stress dictionary. The correction is necessary and resolves this concrete extra
condition. Current candidate smoothness clauses use genuine C-infinity; literal omega
was an unwanted analytic restriction, especially on stress exact numerator jets.

I inspected the corrected outer FilteredGeneratedCandidate and tried these failure
mechanisms:

1. Vacuum-only/zero-stress assignment: fails the positive finite mass of the
   same physical Hamiltonian and its generated stress-charge normalization;
   stress_nonzero is an actual derived theorem.
2. Unused G or disconnected classical action sidecar: G fixes the bracket,
   color factors, tree action, flow and insertion seeds. The corresponding
   generated coefficients feed the same C's actual vacuum-word germs and OPE.
   Independently selecting an asymptotic prediction table does not remove
   these equations.
3. Independently excited spectator Hilbert factor invisible to C: violates
   composite-only [cyclicity](GLOSSARY.md#quantum-fields-and-distributions) of that same [Hilbert space](GLOSSARY.md#quantum-fields-and-distributions). A spectator on which
   C genuinely acts would have to satisfy the full generated word/OPE,
   normalization and stress equations; the type does not supply it for free.
4. An arbitrary massive free [Wightman](GLOSSARY.md#quantum-fields-and-distributions) model: satisfies only the QFT/gap
   fragment. It cannot be promoted merely by choosing a matching name, stress
   or coefficients: actual all-order C words, fixed same-G perturbative data,
   physical OPE and same generated stress must still agree. I found no
   concrete free-model assignment satisfying all these relations. I do not
   claim a formal universal Gaussian-countermodel exclusion theorem.
5. Arbitrary beta/gamma or asymptotic coefficients: full same-Gamma CS,
   generated basis coordinates, all-scale Wick conjugation, actual transport
   and same-family word matching constrain them simultaneously. Null/exact
   directions or smooth flat completions are legitimate witness freedom
   unless uniqueness/resummation is separately claimed. They do not justify
   an additional quantum-injectivity or deterministic-coefficient axiom.

No further specific missing central predicate, contradictory restriction or verified
false-model mechanism was identified. This conclusion does not claim that structural
dependencies alone prove every non-YM model impossible. It means the attempted
elementary vacuity/sidecar/free-table assignments do not bypass the explicit conditions,
and no additional such loophole was exhibited.

## Conditional admission recommendation

For the central finite prescription, I recommend completing exact definition admission
once the pending same pointwise-response/literal reduced-Taylor mu-jet bridge and actual
canonical insertion/oversubtraction uniqueness adapters are integrated and all required
combined checks pass. The standalone canonical determinacy theorem already uses only the
original source rows; it is not an extra boundary premise. These pending steps are
concrete supporting bridges, not requests for nonperturbative existence.

No additional generic universal-classification, arbitrary-scheme equivalence,
[beta](GLOSSARY.md#scales-and-renormalization)-uniqueness, or restoration-construction gate is justified by this review.
This recommendation concerns the mathematical meaning and assembled definition only. It
supplies neither a witness of that definition, an existence proof, nor external/CMI
certification; separately recorded cited-[QFT](GLOSSARY.md#quantum-fields-and-distributions) access and presentation
qualifications remain accurately stated rather than silently claimed as formal theorems.
