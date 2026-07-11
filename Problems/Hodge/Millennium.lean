import Problems.Hodge.Variety

namespace MillenniumHodge

open AlgebraicGeometry Scheme Complex Algebra VarietyDefinition

universe u₁ u₂ u₃

/-!
# The Hodge Conjecture

Lean statement of the Clay Millennium problem “Hodge conjecture”.

For a projective nonsingular algebraic variety `X` over `ℂ`, every rational `(p,p)` Hodge class in
`H^{2p}(X, ℚ)` should be a finite `ℚ`-linear combination of cohomology classes of algebraic cycles.

The definitions below use `HodgeData` from `Problems.Hodge.Variety`: cohomology groups, Hodge
summands, the Hodge filtration, algebraic cycles, and the cycle-class map.

`HodgeTheoryAssignment.ClayStatement` is stated for a coherent `HodgeTheoryAssignment`, which packages the
Hodge-theoretic realization attached to every smooth projective complex variety.
-/

/--
Clay's phrase “projective non-singular algebraic variety over `ℂ`”, as represented in this
repository.

The nonsingular/projective/complex-analytic realization data is carried by
`SmoothProjectiveVariety ℂ` in `Problems.Hodge.Variety`.
-/
@[reducible]
def SmoothProjectiveComplexVariety : Type 1 :=
  SmoothProjectiveVariety ℂ

/--
The Hodge Conjecture for a fixed smooth complex projective variety `X`.
-/
def HodgeConjecture (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.hodge_class p ≤ data.algebraic_cohomology p

/--
Clay-wording form of the Hodge Conjecture for a fixed projective nonsingular variety over `ℂ`:
every rational `(p,p)` class is represented by an explicit finite rational linear combination of
cycle classes.
-/
def HodgeConjecture.Formulations.CycleSpan
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ (p : ℕ) (x : data.cohomology_q (2 * p)),
    x ∈ data.hodge_class p →
      ∃ coefficients : data.algebraic_cycle p →₀ ℚ,
        data.cycle_class_combination p coefficients = x

/--
Clay's Chow-theorem wording for projective varieties: closed analytic subspaces of codimension `p`.
-/
@[reducible]
def ClosedAnalyticSubspaceCycle
    {X : SmoothProjectiveVariety ℂ} (data : HodgeData.{u₁, u₂, u₃} X) (p : ℕ) : Type u₃ :=
  data.closed_analytic_subspace p

/--
Chow-theorem wording of the Hodge conjecture:
every rational Hodge class is a finite rational linear combination of classes of closed analytic
subspaces, using Chow's theorem to pass from closed analytic subspaces to cycle classes.
-/
def HodgeConjecture.Formulations.AnalyticCycleSpan
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ (p : ℕ) (x : data.cohomology_q (2 * p)),
    x ∈ data.hodge_class p →
      ∃ coefficients : ClosedAnalyticSubspaceCycle (data := data) p →₀ ℚ,
        data.analytic_cycle_class_combination p coefficients = x

/--
The literal per-class Clay assertion: a given Hodge class is a rational linear combination of
cycle classes.
-/
def HodgeConjecture.Formulations.ClassHasCycleSpan
    {X : SmoothProjectiveVariety ℂ} (data : HodgeData.{u₁, u₂, u₃} X)
    (p : ℕ) (x : data.cohomology_q (2 * p)) : Prop :=
  x ∈ data.hodge_class p →
    ∃ coefficients : data.algebraic_cycle p →₀ ℚ,
      data.cycle_class_combination p coefficients = x

/--
Image form of the Hodge Conjecture:
the rational Hodge classes lie in the image of the cycle-class map on
`ℚ`-linear combinations of algebraic cycles.
-/
def HodgeConjecture.Formulations.CycleImage
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.hodge_class p ≤ LinearMap.range (data.rational_cycle_class p)

/--
Equality form of the Hodge conjecture.

The inclusion `algebraic_cohomology ≤ hodge_class` is the formalized easy direction
`cycle classes are Hodge classes`; hence this equality form is equivalent to
`_root_.MillenniumHodge.HodgeConjecture X data`.
-/
def HodgeConjecture.Formulations.Equality
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.hodge_class p = data.algebraic_cohomology p

/--
Filtration form of the Hodge conjecture, using
`H^{2p}(X,ℚ) ∩ F^p H^{2p}(X,ℂ)`.

The Clay PDF identifies this with the `(p,p)` formulation for smooth projective varieties; below,
that identification is expressed by `HodgeDataCoherence.Formulations.FiltrationAgreement`.
-/
def HodgeConjecture.Formulations.Filtration
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.hodge_class_filtration p ≤ data.algebraic_cohomology p

/--
Filtration equality form:
`H^{2p}(X,ℚ) ∩ F^p H^{2p}(X,ℂ)` is exactly the rational span of cycle classes.
-/
def HodgeConjecture.Formulations.FiltrationEquality
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.hodge_class_filtration p = data.algebraic_cohomology p

/-- The Hodge data satisfies the Clay identification of `(p,p)` and filtration classes. -/
def HodgeDataCoherence.Formulations.FiltrationAgreement
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.hodge_class p = data.hodge_class_filtration p

/--
Clay PDF equality defining rational Hodge classes:
`H^{2p}(X,ℚ) ∩ H^{p,p}(X) = H^{2p}(X,ℚ) ∩ F^p`.
-/
def HodgeDataCoherence.Formulations.ClassFiltrationAgreement
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence.Formulations.FiltrationAgreement X data

/-- Global all-coherent-data form of the Clay rational-Hodge-class definition agreement. -/
def HodgeDataCoherence.Formulations.AllDefinitionsAgree : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → HodgeDataCoherence.Formulations.ClassFiltrationAgreement X data

/-- Coherent Hodge data supplies the Clay rational-Hodge-class definition agreement. -/
theorem hodge_class_filtration_agreement
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X)
    (coh : HodgeDataCoherence data) :
    HodgeDataCoherence.Formulations.ClassFiltrationAgreement X data :=
  coh.filtration_agreement

/-- Global coherent-data version of the Clay rational-Hodge-class definition agreement. -/
theorem all_hodge_definitions_agree :
    HodgeDataCoherence.Formulations.AllDefinitionsAgree.{u₁, u₂, u₃} := by
  intro X data hcoh
  exact hodge_class_filtration_agreement X data hcoh

/--
Clay PDF easy direction for one fixed Hodge-theoretic realization:
the class `cl(Z)` of an algebraic cycle is a rational Hodge class.
-/
def CycleClassesAreHodge
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ (p : ℕ) (Z : data.algebraic_cycle p),
    data.cycle_class p Z ∈ data.hodge_class p

/--
Clay PDF easy direction in subspace form:
the rational span of algebraic cycle classes lies inside the rational Hodge classes.
-/
def AlgebraicClassesAreHodge
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  ∀ p : ℕ,
    data.algebraic_cohomology p ≤ data.hodge_class p

/-- Global version of the Clay easy direction: every algebraic cycle class is a Hodge class. -/
def ClayHodge.Support.AllCycleClassesAreHodge : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → CycleClassesAreHodge X data

/-- Global subspace form of the Clay easy direction. -/
def ClayHodge.Support.AllAlgebraicClassesAreHodge : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → AlgebraicClassesAreHodge X data

/-- The chosen cycle-class map in `HodgeData` makes every algebraic cycle class a Hodge class. -/
theorem cycle_classes_are_hodge
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    CycleClassesAreHodge X data := by
  intro p Z
  exact data.cycle_class_mem_hodge_class p Z

/-- The rational span of algebraic cycle classes is contained in the Hodge classes. -/
theorem algebraic_classes_are_hodge
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    AlgebraicClassesAreHodge X data := by
  intro p
  exact data.algebraic_cohomology_le_hodge_class p

/-- The global coherent-data Clay easy direction for individual cycle classes. -/
theorem all_cycle_classes_are_hodge :
    ClayHodge.Support.AllCycleClassesAreHodge.{u₁, u₂, u₃} := by
  intro X data _hcoh
  exact cycle_classes_are_hodge X data

/-- The global coherent-data Clay easy direction for spans of algebraic classes. -/
theorem all_algebraic_classes_are_hodge :
    ClayHodge.Support.AllAlgebraicClassesAreHodge.{u₁, u₂, u₃} := by
  intro X data _hcoh
  exact algebraic_classes_are_hodge X data

/-- The Hodge conjecture together with the coherence properties of the chosen Hodge data. -/
def HodgeConjecture.Formulations.Coherent.Conjecture
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧ _root_.MillenniumHodge.HodgeConjecture X data

/-- Coherent Hodge conjecture in equality form. -/
def HodgeConjecture.Formulations.Coherent.Equality
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧ HodgeConjecture.Formulations.Equality X data

/-- Coherent Hodge conjecture in filtration form. -/
def HodgeConjecture.Formulations.Coherent.Filtration
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧ HodgeConjecture.Formulations.Filtration X data

/-- Coherent Hodge conjecture in explicit finite cycle-class-combination form. -/
def HodgeConjecture.Formulations.Coherent.CycleSpan
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧ HodgeConjecture.Formulations.CycleSpan X data

/-- Coherent Hodge conjecture in Chow closed-analytic-subspace wording. -/
def HodgeConjecture.Formulations.Coherent.AnalyticCycleSpan
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧ HodgeConjecture.Formulations.AnalyticCycleSpan X data

/--
Clay's “any Hodge class is a rational linear combination of classes of algebraic cycles” wording
for one fixed smooth projective complex variety, with the needed Hodge-theoretic foundations made
explicit.
-/
def HodgeConjecture.Formulations.FixedCycleSpan
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧
    ∀ (p : ℕ) (x : data.cohomology_q (2 * p)),
      HodgeConjecture.Formulations.ClassHasCycleSpan data p x

/--
Clay fixed-variety wording:
on a projective non-singular algebraic variety over `ℂ`, every rational Hodge class is a rational
linear combination of algebraic cycle classes, with coherent Hodge data made explicit.
-/
def HodgeConjecture.Formulations.FixedVariety
    (X : SmoothProjectiveComplexVariety)
    (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeConjecture.Formulations.FixedCycleSpan X data

/-- Coherent Hodge conjecture in rational cycle-class image form. -/
def HodgeConjecture.Formulations.Coherent.CycleImage
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) : Prop :=
  HodgeDataCoherence data ∧ HodgeConjecture.Formulations.CycleImage X data

/--
Choice of Hodge-theoretic data for every smooth complex projective variety.

The Clay statement uses the Hodge theory attached to each variety.  The assignment makes that
varietywise choice explicit and records the coherence properties used by the equivalent forms below.
-/
structure HodgeTheoryAssignment where
  data : ∀ X : SmoothProjectiveVariety ℂ, HodgeData.{u₁, u₂, u₃} X
  coherent : ∀ X : SmoothProjectiveVariety ℂ, HodgeDataCoherence (data X)

/--
Hodge-theory realization for all smooth projective complex varieties.

This packages the same global data as `HodgeTheoryAssignment` under a geometry-facing name:
singular cohomology, Hodge decomposition, cycle classes, and the coherence identities used below.
-/
structure HodgeTheoryRealization where
  /-- Hodge-theoretic data attached to each smooth projective complex variety. -/
  data : ∀ X : SmoothProjectiveVariety ℂ, HodgeData.{u₁, u₂, u₃} X
  /-- The data satisfies the degree and filtration identities used in the Clay formulation. -/
  coherent : ∀ X : SmoothProjectiveVariety ℂ, HodgeDataCoherence (data X)

namespace HodgeTheoryRealization

/-- The Hodge-theory assignment determined by a realization. -/
def assignment (realization : HodgeTheoryRealization.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.{u₁, u₂, u₃} :=
  { data := realization.data
    coherent := realization.coherent }

end HodgeTheoryRealization

/--
Global Clay-style Hodge statement for the assigned Hodge theory of each smooth complex projective
variety.
-/
def HodgeTheoryAssignment.Formulations.HodgeConjecture (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ, _root_.MillenniumHodge.HodgeConjecture X (assignment.data X)

/--
Global Clay-wording statement for the assigned Hodge theory of each projective nonsingular
algebraic variety over `ℂ`.
-/
def HodgeTheoryAssignment.Formulations.CycleSpan
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ,
    HodgeConjecture.Formulations.CycleSpan X (assignment.data X)

/--
Global image form: rational Hodge classes are in the image of the cycle-class map on rational
linear combinations of algebraic cycles.
-/
def HodgeTheoryAssignment.Formulations.CycleImage
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ,
    HodgeConjecture.Formulations.CycleImage X (assignment.data X)

/--
Packed form of the global Hodge statement, bundling coherence with the conjecture for each variety.
-/
def HodgeTheoryAssignment.Formulations.CoherentHodge
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ, HodgeConjecture.Formulations.Coherent.Conjecture X (assignment.data X)

/--
Global quantifier over all coherent Hodge-theoretic data.

This is useful for comparison with the assignment-based Clay-style statement.
-/
def ClayHodge.Formulations.AllCoherentConjectures : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → HodgeConjecture.Formulations.Coherent.Conjecture X data

/-- Equality form of the global all-coherent-data Hodge statement. -/
def ClayHodge.Formulations.AllCoherentEquality : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → HodgeConjecture.Formulations.Coherent.Equality X data

/-- Filtration form of the global all-coherent-data Hodge statement. -/
def ClayHodge.Formulations.AllCoherentFiltration : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → HodgeConjecture.Formulations.Coherent.Filtration X data

/-- Explicit finite cycle-class-combination form of the all-coherent-data Hodge statement. -/
def ClayHodge.Formulations.AllCoherentCycleSpan : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → HodgeConjecture.Formulations.Coherent.CycleSpan X data

/-- Chow closed-analytic-subspace form of the all-coherent-data Hodge statement. -/
def ClayHodge.Formulations.AllCoherentAnalyticCycleSpan : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data →
      HodgeConjecture.Formulations.Coherent.AnalyticCycleSpan X data

/--
Clay Hodge statement for one coherent Hodge-theory assignment.

The body is the PDF's cycle-class wording: every rational Hodge class is a finite rational linear
combination of algebraic-cycle classes for the assigned Hodge theory of each smooth projective
complex variety.
-/
def HodgeTheoryAssignment.ClayStatement
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  HodgeTheoryAssignment.Formulations.CycleSpan assignment

/-- Rational cycle-class image form of the all-coherent-data Hodge statement. -/
def ClayHodge.Formulations.AllCoherentCycleImage : Prop :=
  ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
    HodgeDataCoherence data → HodgeConjecture.Formulations.Coherent.CycleImage X data

/--
Global equality form: for the assigned Hodge theory of every smooth projective variety, rational
`(p,p)` classes are exactly the rational span of algebraic cycle classes.
-/
def HodgeTheoryAssignment.Formulations.Equality
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ, HodgeConjecture.Formulations.Equality X (assignment.data X)

/--
Global filtration form: for the assigned Hodge theory of every smooth projective variety, rational
classes in the Hodge filtration are algebraic.
-/
def HodgeTheoryAssignment.Formulations.Filtration
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ, HodgeConjecture.Formulations.Filtration X (assignment.data X)

/--
Global filtration equality form: rational filtration classes are exactly the rational span of
cycle classes.
-/
def HodgeTheoryAssignment.Formulations.FiltrationEquality
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) : Prop :=
  ∀ X : SmoothProjectiveVariety ℂ, HodgeConjecture.Formulations.FiltrationEquality X (assignment.data X)

/--
The packed and unpacked assignment-based global Hodge statements are equivalent.
-/
theorem HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_coherent
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment ↔
      HodgeTheoryAssignment.Formulations.CoherentHodge assignment := by
  constructor
  · intro h X
    exact ⟨assignment.coherent X, h X⟩
  · intro h X
    exact (h X).2

/-- The subset formulation of the Hodge conjecture is equivalent to the equality formulation. -/
theorem HodgeConjecture.iff_equality
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    _root_.MillenniumHodge.HodgeConjecture X data ↔ HodgeConjecture.Formulations.Equality X data := by
  constructor
  · intro h p
    exact le_antisymm (h p) (data.algebraic_cohomology_le_hodge_class p)
  · intro h p
    exact le_of_eq (h p)

/--
The subset formulation is equivalent to the explicit Clay wording with a rational finite linear
combination of cycle classes.
-/
theorem HodgeConjecture.iff_cycle_span
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    _root_.MillenniumHodge.HodgeConjecture X data ↔ HodgeConjecture.Formulations.CycleSpan X data := by
  constructor
  · intro h p x hx
    exact (data.mem_algebraic_cohomology_iff_cycle_span p x).1 (h p hx)
  · intro h p x hx
    exact (data.mem_algebraic_cohomology_iff_cycle_span p x).2 (h p x hx)

/--
The explicit cycle-combination conjecture is the same as saying the literal per-class Clay
assertion for every rational Hodge class.
-/
theorem HodgeConjecture.Formulations.CycleSpan.iff_classes
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.CycleSpan X data ↔
      ∀ (p : ℕ) (x : data.cohomology_q (2 * p)),
        HodgeConjecture.Formulations.ClassHasCycleSpan data p x := by
  rfl

/--
The algebraic-cycle wording and the Chow closed-analytic-subspace wording are equivalent via the
Chow equivalence carried by the projective Hodge data.
-/
theorem HodgeConjecture.iff_analytic_cycle_span
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    _root_.MillenniumHodge.HodgeConjecture X data ↔
      HodgeConjecture.Formulations.AnalyticCycleSpan X data := by
  constructor
  · intro h p x hx
    exact
      (data.mem_algebraic_cohomology_iff_analytic_cycle_class p x).1
        (h p hx)
  · intro h p x hx
    exact
      (data.mem_algebraic_cohomology_iff_analytic_cycle_class p x).2
        (h p x hx)

/-- The subset formulation is equivalent to the image of the rational cycle-class map. -/
theorem HodgeConjecture.iff_cycle_image
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    _root_.MillenniumHodge.HodgeConjecture X data ↔ HodgeConjecture.Formulations.CycleImage X data := by
  constructor
  · intro h p
    rw [← data.algebraic_eq_range_rational_cycle p]
    exact h p
  · intro h p
    rw [data.algebraic_eq_range_rational_cycle p]
    exact h p

/-- The assignment-based subset and equality Hodge statements are equivalent. -/
theorem HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_equality
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment ↔
      HodgeTheoryAssignment.Formulations.Equality assignment := by
  constructor
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_equality X (assignment.data X)).1 (h X)
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_equality X (assignment.data X)).2 (h X)

/-- The assignment-based subset and rational-cycle-combination statements are equivalent. -/
theorem HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_cycle_span
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment ↔
      HodgeTheoryAssignment.Formulations.CycleSpan assignment := by
  constructor
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_span X (assignment.data X)).1 (h X)
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_span X (assignment.data X)).2 (h X)

/-- The assignment-based subset and rational cycle-class image statements are equivalent. -/
theorem HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_cycle_image
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment ↔
      HodgeTheoryAssignment.Formulations.CycleImage assignment := by
  constructor
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_image X (assignment.data X)).1 (h X)
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_image X (assignment.data X)).2 (h X)

/--
Surjectivity of the cycle-class map in every codimension proves the Hodge conjecture.

This is a direct algebraic sufficient condition: a Hodge class is algebraic once it is known to be
the cycle class of some algebraic cycle.
-/
theorem HodgeConjecture.surjective_cycle_class
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X)
    (hSurj :
      ∀ p : ℕ, ∀ x : data.cohomology_q (2 * p),
        ∃ Z : data.algebraic_cycle p, data.cycle_class p Z = x) :
    _root_.MillenniumHodge.HodgeConjecture X data :=
  data.hodge_conjecture_surjective_cycle_class hSurj

/--
Under the standard Hodge-theoretic identification
`H^{2p}(X,ℚ) ∩ H^{p,p} = H^{2p}(X,ℚ) ∩ F^p`, the `(p,p)` and filtration formulations agree.
-/
theorem HodgeConjecture.iff_filtration
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X)
    (hAgree : HodgeDataCoherence.Formulations.FiltrationAgreement X data) :
    _root_.MillenniumHodge.HodgeConjecture X data ↔ HodgeConjecture.Formulations.Filtration X data := by
  constructor
  · intro h p
    rw [← hAgree p]
    exact h p
  · intro h p
    rw [hAgree p]
    exact h p

/-- The filtration subset formulation is equivalent to the filtration equality formulation. -/
theorem HodgeConjecture.Formulations.Filtration.iff_equality
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.Filtration X data ↔ HodgeConjecture.Formulations.FiltrationEquality X data := by
  constructor
  · intro h p
    exact le_antisymm (h p) (data.algebraic_le_hodge_class_filtration p)
  · intro h p
    exact le_of_eq (h p)

/-- Coherent Hodge data supplies the filtration agreement needed for the filtration formulation. -/
theorem HodgeDataCoherence.filtration_agreement
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X)
    (coh : HodgeDataCoherence data) :
    HodgeDataCoherence.Formulations.FiltrationAgreement X data :=
  coh.filtration_agreement

/--
For coherent Hodge data, the `(p,p)` and filtration versions of the conjecture are equivalent
without any extra hypothesis.
-/
theorem HodgeConjecture.iff_filtration_coherent
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X)
    (coh : HodgeDataCoherence data) :
    _root_.MillenniumHodge.HodgeConjecture X data ↔ HodgeConjecture.Formulations.Filtration X data :=
  _root_.MillenniumHodge.HodgeConjecture.iff_filtration X data (HodgeDataCoherence.filtration_agreement X data coh)

/-- The assignment-based `(p,p)` and filtration Hodge statements are equivalent. -/
theorem HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_filtration
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment ↔
      HodgeTheoryAssignment.Formulations.Filtration assignment := by
  constructor
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_filtration_coherent
      X (assignment.data X) (assignment.coherent X)).1 (h X)
  · intro h X
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_filtration_coherent
      X (assignment.data X) (assignment.coherent X)).2 (h X)

/--
Specializing the all-coherent-data statement to the Hodge data chosen by an assignment gives the
assignment-indexed Hodge conjecture.
-/
theorem ClayHodge.Formulations.AllCoherentConjectures.assignment_hodge
    (h : ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃})
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment := by
  intro X
  exact (h X (assignment.data X) (assignment.coherent X)).2

/--
Specializing the all-coherent-data cycle-combination statement to an assignment gives the explicit
rational linear-combination form for that assignment.
-/
theorem ClayHodge.Formulations.AllCoherentCycleSpan.assignment_cycle_span
    (h : ClayHodge.Formulations.AllCoherentCycleSpan.{u₁, u₂, u₃})
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.CycleSpan assignment := by
  intro X
  exact (h X (assignment.data X) (assignment.coherent X)).2

/--
Specializing the all-coherent-data cycle-image statement to an assignment gives the rational
cycle-class image formulation for that assignment.
-/
theorem ClayHodge.Formulations.AllCoherentCycleImage.assignment_cycle_image
    (h : ClayHodge.Formulations.AllCoherentCycleImage.{u₁, u₂, u₃})
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.CycleImage assignment := by
  intro X
  exact (h X (assignment.data X) (assignment.coherent X)).2

/-- Specialize the all-coherent-data statement to the coherent data chosen by an assignment. -/
theorem ClayHodge.Formulations.AllCoherentConjectures.assignment_coherent
    (h : ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃})
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.Formulations.CoherentHodge assignment := by
  intro X
  exact h X (assignment.data X) (assignment.coherent X)

/--
The assignment-based formulation is equivalent to quantifying over all coherent Hodge-theoretic
data.
-/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_assignments :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ∀ assignment : HodgeTheoryAssignment.{u₁, u₂, u₃},
        HodgeTheoryAssignment.Formulations.HodgeConjecture assignment := by
  constructor
  · intro h assignment
    exact h.assignment_hodge assignment
  · intro h X data hcoh
    let assignment : HodgeTheoryAssignment.{u₁, u₂, u₃} :=
      { data := fun Y => by
          by_cases hYX : Y = X
          · subst hYX
            exact data
          · exact (zero_hodge_data Y : HodgeData.{u₁, u₂, u₃} Y)
        coherent := fun Y => by
          by_cases hYX : Y = X
          · subst hYX
            simpa using hcoh
          · simpa [hYX] using
              (ZeroHodgeData.coherence Y :
                HodgeDataCoherence (zero_hodge_data Y : HodgeData.{u₁, u₂, u₃} Y)) }
    have hdata : assignment.data X = data := by
      dsimp [assignment]
      simp
    exact ⟨hcoh, by simpa [hdata] using h assignment X⟩

/--
Quantifying over all coherent Hodge data is equivalent to the packed statement for every coherent
assignment.
-/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_coherent :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ∀ assignment : HodgeTheoryAssignment.{u₁, u₂, u₃},
        HodgeTheoryAssignment.Formulations.CoherentHodge assignment := by
  constructor
  · intro h assignment
    exact h.assignment_coherent assignment
  · intro h
    rw [ClayHodge.Formulations.AllCoherentConjectures.iff_assignments]
    intro assignment
    exact (HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_coherent assignment).2 (h assignment)

/-- The coherent subset and equality formulations are equivalent. -/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.iff_equality
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.Coherent.Conjecture X data ↔ HodgeConjecture.Formulations.Coherent.Equality X data := by
  constructor
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_equality X data).1 h.2⟩
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_equality X data).2 h.2⟩

/-- The coherent subset formulation is equivalent to the explicit cycle-combination form. -/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.iff_cycle_span
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.Coherent.Conjecture X data ↔
      HodgeConjecture.Formulations.Coherent.CycleSpan X data := by
  constructor
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_span X data).1 h.2⟩
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_span X data).2 h.2⟩

/-- The coherent Hodge statement is equivalent to the Chow closed-analytic-subspace wording. -/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.iff_analytic_cycle_span
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.Coherent.Conjecture X data ↔
      HodgeConjecture.Formulations.Coherent.AnalyticCycleSpan X data := by
  constructor
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_analytic_cycle_span X data).1 h.2⟩
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_analytic_cycle_span X data).2 h.2⟩

/--
The fixed-data Clay wording is equivalent to the coherent cycle-class-combination formulation.
-/
theorem HodgeConjecture.Formulations.FixedCycleSpan.iff_coherent
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.FixedCycleSpan X data ↔
      HodgeConjecture.Formulations.Coherent.CycleSpan X data := by
  rfl

/-- The Clay fixed-variety form is exactly the fixed-data Clay statement. -/
theorem HodgeConjecture.Formulations.FixedVariety.iff_fixed_hodge_data
    (X : SmoothProjectiveComplexVariety)
    (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.FixedVariety X data ↔
      HodgeConjecture.Formulations.FixedCycleSpan X data := by
  rfl

/-- The coherent subset formulation is equivalent to the rational cycle-class image form. -/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.iff_cycle_image
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.Coherent.Conjecture X data ↔
      HodgeConjecture.Formulations.Coherent.CycleImage X data := by
  constructor
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_image X data).1 h.2⟩
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_cycle_image X data).2 h.2⟩

/-- The coherent `(p,p)` and filtration formulations are equivalent. -/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.iff_filtration
    (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X) :
    HodgeConjecture.Formulations.Coherent.Conjecture X data ↔ HodgeConjecture.Formulations.Coherent.Filtration X data := by
  constructor
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_filtration_coherent X data h.1).1 h.2⟩
  · intro h
    exact ⟨h.1, (_root_.MillenniumHodge.HodgeConjecture.iff_filtration_coherent X data h.1).2 h.2⟩

/-- The global Hodge statement is equivalent to the equality formulation. -/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_equality :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ClayHodge.Formulations.AllCoherentEquality.{u₁, u₂, u₃} := by
  constructor
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_equality X data).1 (h X data hcoh)
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_equality X data).2 (h X data hcoh)

/-- The global Hodge statement is equivalent to the cycle-span formulation. -/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_cycle_span :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ClayHodge.Formulations.AllCoherentCycleSpan.{u₁, u₂, u₃} := by
  constructor
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_cycle_span X data).1 (h X data hcoh)
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_cycle_span X data).2 (h X data hcoh)

/-- The global Hodge statement is equivalent to the closed-analytic-cycle formulation. -/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_analytic_cycle_span :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ClayHodge.Formulations.AllCoherentAnalyticCycleSpan.{u₁, u₂, u₃} := by
  constructor
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_analytic_cycle_span X data).1
      (h X data hcoh)
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_analytic_cycle_span X data).2
      (h X data hcoh)

/--
The global Hodge statement is equivalent to the assignment-indexed cycle-span formulation.
-/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_assignment_cycle_span :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ∀ assignment : HodgeTheoryAssignment.{u₁, u₂, u₃},
        HodgeTheoryAssignment.Formulations.CycleSpan assignment := by
  rw [ClayHodge.Formulations.AllCoherentConjectures.iff_assignments]
  constructor
  · intro h assignment
    exact (HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_cycle_span assignment).1
      (h assignment)
  · intro h assignment
    exact (HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_cycle_span assignment).2
      (h assignment)

/-- Clay Hodge statement using a specified Hodge-theory realization. -/
def HodgeTheoryRealization.ClayStatement
    (realization : HodgeTheoryRealization.{u₁, u₂, u₃}) : Prop :=
  HodgeTheoryAssignment.ClayStatement realization.assignment

/--
Global Hodge statement used by this repository: every coherent Hodge-theoretic data package for
every smooth projective complex variety satisfies the Clay cycle-class statement.

The assignment-specific declaration `HodgeTheoryAssignment.ClayStatement assignment` remains available for a fixed
realization, while this statement quantifies over all coherent realizations.  This is stronger
than a future native formalization that quantifies only over the canonical Hodge theory attached to
each variety.
-/
def ClayHodge : Prop :=
  ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃}

/-- The realization form is exactly the statement for its Hodge-theory assignment. -/
theorem HodgeTheoryRealization.ClayStatement.iff_assignment
    (realization : HodgeTheoryRealization.{u₁, u₂, u₃}) :
    HodgeTheoryRealization.ClayStatement realization ↔
      HodgeTheoryAssignment.ClayStatement realization.assignment :=
  Iff.rfl

/-- `HodgeTheoryAssignment.ClayStatement assignment` is the assignment-parameterized cycle-class statement. -/
theorem HodgeTheoryAssignment.ClayStatement.iff_cycle_span
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔ HodgeTheoryAssignment.Formulations.CycleSpan assignment :=
  Iff.rfl

/--
The global Hodge statement is equivalent to quantifying the assignment-indexed Clay statement
over every coherent Hodge-theory assignment.
-/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_clay :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ∀ assignment : HodgeTheoryAssignment.{u₁, u₂, u₃},
        HodgeTheoryAssignment.ClayStatement assignment :=
  ClayHodge.Formulations.AllCoherentConjectures.iff_assignment_cycle_span.trans <| by
    constructor
    · intro h assignment
      exact (HodgeTheoryAssignment.ClayStatement.iff_cycle_span assignment).2 (h assignment)
    · intro h assignment
      exact (HodgeTheoryAssignment.ClayStatement.iff_cycle_span assignment).1 (h assignment)

/--
`HodgeTheoryAssignment.ClayStatement assignment` is equivalent to the subspace formulation:
rational Hodge classes lie in the rational span of algebraic cycle classes for each assigned
smooth projective complex variety.
-/
theorem HodgeTheoryAssignment.ClayStatement.iff_hodge_classes
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔ HodgeTheoryAssignment.Formulations.HodgeConjecture assignment :=
  (HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_cycle_span assignment).symm

/--
`HodgeTheoryAssignment.ClayStatement assignment` says exactly that each assigned fixed-data package
satisfies the fixed-data Clay assertion.
-/
theorem HodgeTheoryAssignment.ClayStatement.iff_fixed_hodge_data
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔
      ∀ X : SmoothProjectiveVariety ℂ,
        HodgeConjecture.Formulations.FixedCycleSpan X (assignment.data X) := by
  constructor
  · intro h X
    exact ⟨assignment.coherent X, h X⟩
  · intro h X
    exact (h X).2

/--
`HodgeTheoryAssignment.ClayStatement assignment` in the PDF's fixed-variety vocabulary: for every
projective non-singular algebraic variety over `ℂ`, every rational Hodge class is a rational
linear combination of algebraic cycle classes.
-/
theorem HodgeTheoryAssignment.ClayStatement.iff_varieties
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔
      ∀ X : SmoothProjectiveComplexVariety,
        HodgeConjecture.Formulations.FixedVariety X (assignment.data X) := by
  simpa [HodgeConjecture.Formulations.FixedVariety.iff_fixed_hodge_data] using
    HodgeTheoryAssignment.ClayStatement.iff_fixed_hodge_data assignment

/--
A proof of `HodgeTheoryAssignment.ClayStatement assignment` applies to each fixed projective non-singular algebraic variety
over `ℂ`.
-/
theorem HodgeTheoryAssignment.ClayStatement.for_variety
    {assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}}
    (h : HodgeTheoryAssignment.ClayStatement assignment)
    (X : SmoothProjectiveComplexVariety) :
    HodgeConjecture.Formulations.FixedVariety X (assignment.data X) :=
  (HodgeTheoryAssignment.ClayStatement.iff_varieties assignment).1 h X

/--
`HodgeTheoryAssignment.ClayStatement assignment` is equivalent to the Chow closed-analytic-subspace
wording used in the Clay exposition.
-/
theorem HodgeTheoryAssignment.ClayStatement.iff_analytic_cycle_span
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔
      ∀ X : SmoothProjectiveVariety ℂ,
        HodgeConjecture.Formulations.AnalyticCycleSpan X (assignment.data X) := by
  constructor
  · intro h X
    have hAssign : HodgeTheoryAssignment.Formulations.HodgeConjecture assignment :=
      (HodgeTheoryAssignment.ClayStatement.iff_hodge_classes assignment).1 h
    exact (_root_.MillenniumHodge.HodgeConjecture.iff_analytic_cycle_span X (assignment.data X)).1
      (hAssign X)
  · intro h
    exact (HodgeTheoryAssignment.ClayStatement.iff_hodge_classes assignment).2 fun X =>
      (_root_.MillenniumHodge.HodgeConjecture.iff_analytic_cycle_span X (assignment.data X)).2 (h X)

/--
`HodgeTheoryAssignment.ClayStatement assignment` is equivalent to the rational cycle-class image
formulation.
-/
theorem HodgeTheoryAssignment.ClayStatement.iff_cycle_image
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔
      HodgeTheoryAssignment.Formulations.CycleImage assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_hodge_classes assignment).trans
    (HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_cycle_image assignment)

/--
`HodgeTheoryAssignment.ClayStatement assignment` is equivalent to the filtration formulation, using the
coherence data in the assignment to identify rational `(p,p)` classes with rational filtration
classes.
-/
theorem HodgeTheoryAssignment.ClayStatement.iff_filtration
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃}) :
    HodgeTheoryAssignment.ClayStatement assignment ↔
      HodgeTheoryAssignment.Formulations.Filtration assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_hodge_classes assignment).trans
    (HodgeTheoryAssignment.Formulations.HodgeConjecture.iff_filtration assignment)

/-- The assignment-indexed Clay statement gives the rational `(p,p)` subspace statement. -/
theorem HodgeTheoryAssignment.ClayStatement.rational_hodge_classes
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement assignment) :
    HodgeTheoryAssignment.Formulations.HodgeConjecture assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_hodge_classes assignment).1 h

/-- The rational `(p,p)` subspace statement gives the assignment-indexed Clay statement. -/
theorem HodgeTheoryAssignment.ClayStatement.of_rational_hodge_classes
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.Formulations.HodgeConjecture assignment) :
    HodgeTheoryAssignment.ClayStatement assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_hodge_classes assignment).2 h

/-- Evaluate the assignment-indexed statement at each smooth projective complex variety. -/
theorem HodgeTheoryAssignment.ClayStatement.fixed_data
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement assignment) :
      ∀ X : SmoothProjectiveVariety ℂ,
        HodgeConjecture.Formulations.FixedCycleSpan X (assignment.data X) :=
  (HodgeTheoryAssignment.ClayStatement.iff_fixed_hodge_data assignment).1 h

/-- Fixed-data assertions for every variety give the assignment-indexed Hodge statement. -/
theorem HodgeTheoryAssignment.ClayStatement.of_fixed_data
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : ∀ X : SmoothProjectiveVariety ℂ,
        HodgeConjecture.Formulations.FixedCycleSpan X (assignment.data X)) :
    HodgeTheoryAssignment.ClayStatement assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_fixed_hodge_data assignment).2 h

/-- `HodgeTheoryAssignment.ClayStatement assignment` is expressible in the PDF's fixed-variety vocabulary. -/
theorem HodgeTheoryAssignment.ClayStatement.varieties
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement assignment) :
      ∀ X : SmoothProjectiveComplexVariety,
        HodgeConjecture.Formulations.FixedVariety X (assignment.data X) :=
  (HodgeTheoryAssignment.ClayStatement.iff_varieties assignment).1 h

/-- Build the assignment-indexed Hodge statement from the PDF's fixed-variety vocabulary. -/
theorem HodgeTheoryAssignment.ClayStatement.of_varieties
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : ∀ X : SmoothProjectiveComplexVariety,
        HodgeConjecture.Formulations.FixedVariety X (assignment.data X)) :
    HodgeTheoryAssignment.ClayStatement assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_varieties assignment).2 h

/-- Algebraic-cycle classes give the Chow closed-analytic-subspace statement. -/
theorem HodgeTheoryAssignment.ClayStatement.analytic_cycle_span
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement assignment) :
      ∀ X : SmoothProjectiveVariety ℂ,
        HodgeConjecture.Formulations.AnalyticCycleSpan X (assignment.data X) :=
  (HodgeTheoryAssignment.ClayStatement.iff_analytic_cycle_span assignment).1 h

/-- The Chow closed-analytic-subspace statement gives the assignment-indexed Hodge statement. -/
theorem HodgeTheoryAssignment.ClayStatement.of_analytic_cycle_span
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : ∀ X : SmoothProjectiveVariety ℂ,
        HodgeConjecture.Formulations.AnalyticCycleSpan X (assignment.data X)) :
    HodgeTheoryAssignment.ClayStatement assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_analytic_cycle_span assignment).2 h

/-- The assignment-indexed statement gives the rational cycle-class image statement. -/
theorem HodgeTheoryAssignment.ClayStatement.cycle_image
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement assignment) :
    HodgeTheoryAssignment.Formulations.CycleImage assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_cycle_image assignment).1 h

/-- The rational cycle-class image statement gives the assignment-indexed Hodge statement. -/
theorem HodgeTheoryAssignment.ClayStatement.of_cycle_image
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.Formulations.CycleImage assignment) :
    HodgeTheoryAssignment.ClayStatement assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_cycle_image assignment).2 h

/-- Coherence turns the assignment-indexed statement into the filtration statement. -/
theorem HodgeTheoryAssignment.ClayStatement.filtration
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement assignment) :
    HodgeTheoryAssignment.Formulations.Filtration assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_filtration assignment).1 h

/-- The filtration statement gives the assignment-indexed Hodge statement. -/
theorem HodgeTheoryAssignment.ClayStatement.of_filtration
    (assignment : HodgeTheoryAssignment.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.Formulations.Filtration assignment) :
    HodgeTheoryAssignment.ClayStatement assignment :=
  (HodgeTheoryAssignment.ClayStatement.iff_filtration assignment).2 h

/-- A realization-level Hodge statement induces the assignment-form Hodge statement. -/
theorem HodgeTheoryRealization.ClayStatement.assignment
    (realization : HodgeTheoryRealization.{u₁, u₂, u₃})
    (h : HodgeTheoryRealization.ClayStatement realization) :
    HodgeTheoryAssignment.ClayStatement realization.assignment :=
  (HodgeTheoryRealization.ClayStatement.iff_assignment realization).1 h

/-- The assignment-form statement is enough for the corresponding realization form. -/
theorem HodgeTheoryAssignment.ClayStatement.realization
    (realization : HodgeTheoryRealization.{u₁, u₂, u₃})
    (h : HodgeTheoryAssignment.ClayStatement realization.assignment) :
    HodgeTheoryRealization.ClayStatement realization :=
  (HodgeTheoryRealization.ClayStatement.iff_assignment realization).2 h

/-- The global Hodge statement is equivalent to the cycle-class-image formulation. -/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_cycle_image :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ClayHodge.Formulations.AllCoherentCycleImage.{u₁, u₂, u₃} := by
  constructor
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_cycle_image X data).1 (h X data hcoh)
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_cycle_image X data).2 (h X data hcoh)

/-- The global Hodge statement is equivalent to the Hodge-filtration formulation. -/
theorem ClayHodge.Formulations.AllCoherentConjectures.iff_filtration :
    ClayHodge.Formulations.AllCoherentConjectures.{u₁, u₂, u₃} ↔
      ClayHodge.Formulations.AllCoherentFiltration.{u₁, u₂, u₃} := by
  constructor
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_filtration X data).1 (h X data hcoh)
  · intro h X data hcoh
    exact (HodgeConjecture.Formulations.Coherent.Conjecture.iff_filtration X data).2 (h X data hcoh)

/--
The coherent Hodge conjecture gives the equality form:
rational `(p,p)`-classes are exactly the rational span of algebraic cycle classes.
-/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.hodge_class_eq_algebraic
    {X : SmoothProjectiveVariety ℂ} {data : HodgeData.{u₁, u₂, u₃} X}
    (h : HodgeConjecture.Formulations.Coherent.Conjecture X data) (p : ℕ) :
    data.hodge_class p = data.algebraic_cohomology p :=
  (_root_.MillenniumHodge.HodgeConjecture.iff_equality X data).1 h.2 p

/--
For coherent Hodge data, the filtration version also equals the rational span of algebraic cycle
classes.
-/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.filtration_eq_algebraic
    {X : SmoothProjectiveVariety ℂ} {data : HodgeData.{u₁, u₂, u₃} X}
    (h : HodgeConjecture.Formulations.Coherent.Conjecture X data) (p : ℕ) :
    data.hodge_class_filtration p = data.algebraic_cohomology p := by
  rw [← h.1.hodge_class_eq_hodge_class_filtration p]
  exact h.hodge_class_eq_algebraic p

/--
Under the coherent Hodge conjecture, a rational filtration Hodge class is represented by a rational
linear combination of algebraic cycle classes.
-/
theorem HodgeConjecture.Formulations.Coherent.Conjecture.filtration_mem_algebraic
    {X : SmoothProjectiveVariety ℂ} {data : HodgeData.{u₁, u₂, u₃} X}
    (h : HodgeConjecture.Formulations.Coherent.Conjecture X data) {p : ℕ}
    {x : data.cohomology_q (2 * p)}
    (hx : x ∈ data.hodge_class_filtration p) :
    x ∈ data.algebraic_cohomology p := by
  rw [← h.filtration_eq_algebraic p]
  exact hx

/-!
## Interface examples

The following examples show that the `HodgeData` interface has nonempty synthetic models where the
cycle-class and filtration machinery can be checked directly.  They are deliberately not used as
witnesses for `HodgeTheoryAssignment.ClayStatement`: the Clay statement above is about the coherent
Hodge-theoretic realization attached to smooth projective complex varieties.
-/

/-- The Hodge conjecture holds for the synthetic zero-cohomology Hodge theory. -/
theorem ZeroHodgeData.hodge_conjecture (X : SmoothProjectiveVariety ℂ) :
    _root_.MillenniumHodge.HodgeConjecture X (zero_hodge_data X) :=
  ZeroHodgeData.hodge_class_le_algebraic X

/-- Equality form for the zero-cohomology Hodge theory. -/
theorem ZeroHodgeData.hodge_equality (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Equality X (zero_hodge_data X) :=
  ZeroHodgeData.hodge_class_eq_algebraic X

/-- Filtration form for the zero-cohomology Hodge theory. -/
theorem ZeroHodgeData.hodge_filtration (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Filtration X (zero_hodge_data X) :=
  ZeroHodgeData.filtration_le_algebraic X

/-- The synthetic zero-cohomology Hodge theory satisfies the coherent Hodge conjecture. -/
theorem ZeroHodgeData.coherent_hodge (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Coherent.Conjecture X (zero_hodge_data X) :=
  ⟨ZeroHodgeData.coherence X, ZeroHodgeData.hodge_conjecture X⟩

/-- The Hodge conjecture holds for the synthetic nonzero one-dimensional Hodge theory. -/
theorem RationalHodgeData.hodge_conjecture (X : SmoothProjectiveVariety ℂ) :
    _root_.MillenniumHodge.HodgeConjecture X (rational_hodge_data X) :=
  RationalHodgeData.hodge_class_le_algebraic X

/-- Equality form for the one-dimensional rational Hodge theory. -/
theorem RationalHodgeData.hodge_equality (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Equality X (rational_hodge_data X) :=
  RationalHodgeData.hodge_class_eq_algebraic X

/-- Filtration form for the one-dimensional rational Hodge theory. -/
theorem RationalHodgeData.hodge_filtration (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Filtration X (rational_hodge_data X) := by
  intro p
  rw [RationalHodgeData.filtration_eq_top,
    RationalHodgeData.algebraic_eq_top]

/-- The synthetic nonzero one-dimensional Hodge theory satisfies the coherent Hodge conjecture. -/
theorem RationalHodgeData.coherent_hodge (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Coherent.Conjecture X (rational_hodge_data X) :=
  ⟨RationalHodgeData.coherence X, RationalHodgeData.hodge_conjecture X⟩

/-- Every Hodge class in the one-dimensional rational theory is the class of a cycle. -/
theorem RationalHodgeData.hodge_class_cycle_rep
    (X : SmoothProjectiveVariety ℂ) (p : ℕ)
    (x : (rational_hodge_data X).cohomology_q (2 * p))
    (hx : x ∈ (rational_hodge_data X).hodge_class p) :
    ∃ Z : (rational_hodge_data X).algebraic_cycle p,
      (rational_hodge_data X).cycle_class p Z = x :=
  RationalHodgeData.hodge_class_has_cycle X p x hx

/-- The Hodge conjecture holds for every synthetic finite-dimensional rational Hodge theory. -/
theorem FiniteRationalHodgeData.hodge_conjecture
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    _root_.MillenniumHodge.HodgeConjecture X (finite_rational_hodge_data m X) :=
  FiniteRationalHodgeData.hodge_class_le_algebraic m X

/-- Equality form for every finite-dimensional rational Hodge theory. -/
theorem FiniteRationalHodgeData.hodge_equality
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Equality X (finite_rational_hodge_data m X) :=
  FiniteRationalHodgeData.hodge_class_eq_algebraic m X

/-- Filtration form for every finite-dimensional rational Hodge theory. -/
theorem FiniteRationalHodgeData.hodge_filtration
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Filtration X (finite_rational_hodge_data m X) := by
  intro p
  rw [FiniteRationalHodgeData.filtration_eq_top,
    FiniteRationalHodgeData.algebraic_eq_top]

/--
Every synthetic finite-dimensional rational Hodge theory satisfies the coherent Hodge
conjecture.
-/
theorem FiniteRationalHodgeData.coherent_hodge
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    HodgeConjecture.Formulations.Coherent.Conjecture X (finite_rational_hodge_data m X) :=
  ⟨FiniteRationalHodgeData.coherence m X, FiniteRationalHodgeData.hodge_conjecture m X⟩

/-- Every Hodge class in the finite-dimensional rational theory is the class of a cycle. -/
theorem FiniteRationalHodgeData.hodge_class_cycle_rep
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ)
    (x : (finite_rational_hodge_data m X).cohomology_q (2 * p))
    (hx : x ∈ (finite_rational_hodge_data m X).hodge_class p) :
    ∃ Z : (finite_rational_hodge_data m X).algebraic_cycle p,
      (finite_rational_hodge_data m X).cycle_class p Z = x :=
  FiniteRationalHodgeData.hodge_class_has_cycle m X p x hx

/-- A coordinate basis cycle realizes the corresponding rational cohomology basis class. -/
theorem FiniteRationalHodgeData.basis_cycle_class
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) (i : Fin m) :
    (finite_rational_hodge_data m X).cycle_class p (Pi.single i (1 : ℚ)) =
      Pi.single i (1 : ℚ) :=
  FiniteRationalHodgeData.cycle_class_single m X p i

/-- Every coordinate basis class is algebraic in the finite-dimensional rational Hodge theory. -/
theorem FiniteRationalHodgeData.basis_class_algebraic
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) (i : Fin m) :
    Pi.single i (1 : ℚ) ∈ (finite_rational_hodge_data m X).algebraic_cohomology p :=
  FiniteRationalHodgeData.single_mem_algebraic m X p i

/-!
## Main theorem

This final theorem records the Hodge Conjecture target directly in the repository's coherent-data
interface. Replace the placeholder proof when one is available.
-/

/-- Clay Millennium Prize target for the Hodge Conjecture. -/
theorem clay_prize_hodge_conjecture :
    ∀ (X : SmoothProjectiveVariety ℂ) (data : HodgeData.{u₁, u₂, u₃} X),
      HodgeDataCoherence data →
        ∀ (p : ℕ) (x : data.cohomology_q (2 * p)),
          x ∈ data.hodge_class p →
            ∃ coefficients : data.algebraic_cycle p →₀ ℚ,
              data.cycle_class_combination p coefficients = x :=
  by
    sorry

end MillenniumHodge
