import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Logic.Function.Basic

set_option diagnostics true
set_option diagnostics.threshold 5000

namespace MillenniumYangMillsDefs

open LieGroup
/-!
# Yang-Mills Existence and Mass Gap Problem

This file provides scaffolding used to state the Clay Millennium problem “Yang–Mills existence and
mass gap”.

The official Clay problem description is:
`Problems/YangMills/references/clay/yangmills.pdf`.

At a high level it asks:
1. Construct a non-trivial 4D quantum Yang–Mills theory (satisfying strong axioms such as Wightman
   or Osterwalder–Schrader).
2. Prove it has a mass gap `Δ > 0` (a spectral gap above the vacuum).

## Some Key Mathematical Components

### Classical Foundation
- `Spacetime`: 4D space where physics happens (time + 3D space)
- `CompactSimpleGaugeGroup`: The symmetry group (like SU(2) or SU(3)) governing interactions
- `GaugeField`: The physical field carrying the force (generalizing electromagnetic potential)
- `FieldStrength`: How strongly the field acts at each point (generalizing E and B fields)
- `YangMillsAction`: The energy functional determining classical dynamics

### Quantum Framework
- `LinearOperator`: Mathematical objects representing physical measurements
- `OperatorValuedDistribution`: Quantum fields as "smeared" operators
- `SchwartzSpace`: Test functions for handling the mathematical singularities

### Axioms for Quantum Field Theory
We record (a simplified form of) the Wightman axioms as a baseline for “axiomatic properties at least
as strong as those cited” in the Clay statement.

1. `WightmanAxioms`: Direct approach in physical spacetime
   - Forces must obey special relativity (Poincaré invariance)
   - Energy must be positive (crucial for stability)
   - There exists a unique lowest-energy state (vacuum)
   - Physical states can be built from vacuum using fields
   - Causality: measurements at space-like separation don't interfere

### The Mass Gap
The mathematical statement that particles have positive mass:
- The Hamiltonian has no spectrum in the interval `(0, Δ)` for some `Δ > 0`
- This explains why force carriers like gluons don't appear as free particles

Proving that a quantum Yang-Mills theory:
1. Can be constructed with mathematical precision (beyond physicists' calculations)
2. Necessarily has this mass gap property (explaining confinement in nuclear physics)

## References
- Jaffe, A., & Witten, E. "Quantum Yang-Mills Theory"
- Streater & Wightman (1964): "PCT, Spin and Statistics, and All That"
- Osterwalder & Schrader (1973, 1975): "Axioms for Euclidean Green's functions"
-/

--𝕜: base field, H: model space, E: model vector space, with appropriate structures
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- I: Represents a model with corners - crucial for defining manifolds with boundary
variable {I: ModelWithCorners 𝕜 E H}

/-- Spacetime R⁴ --/
-- We use Mathlib's canonical `ℓ²` norm / inner product on `ℝ⁴`.
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- Spatial points `ℝ³` (used in the Clay clustering discussion). -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Decidable equality for spacetime points (noncomputable, via classical choice). --/
noncomputable instance : DecidableEq Spacetime := Classical.decEq _

/-- Use the Borel σ-algebra on `Spacetime = ℝ⁴`. -/
noncomputable instance : MeasurableSpace Spacetime := borel Spacetime

/-- `Spacetime` is a Borel space (by definition of the model). -/
noncomputable instance : BorelSpace Spacetime := ⟨rfl⟩

/-- Minkowski metric on R⁴ --/
-- Definition of Minkowski metric with (+,-,-,-) signature
-- Index 0 represents time, indices 1-3 represent spatial dimensions
def MinkowskiMetric (x y : Spacetime) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- Property of a set being a normal subgroup --/
-- Normal subgroups satisfy the conjugation invariance property: gHg⁻¹ ⊆ H
def IsNormalSubgroup {G : Type} [Group G] (H : Set G) : Prop :=
  ∀ g : G, ∀ h ∈ H, g * h * g⁻¹ ∈ H

/-- Property of a set being connected --/
-- Topological connectedness: can't be split into two disjoint open sets
def IsConnected {X : Type} [TopologicalSpace X] (S : Set X) : Prop :=
  ∀ (U V : Set X), IsOpen U → IsOpen V → S ⊆ U ∪ V → S ∩ U ≠ ∅ → S ∩ V ≠ ∅ → S ∩ U ∩ V ≠ ∅

/-- Property of a Lie group being simple (no non-trivial connected normal subgroups) --/
-- In Lie theory, a simple group has no non-trivial connected normal subgroups
class IsSimpleLieGroup (G : Type) [Group G] [TopologicalSpace G] : Prop where
  /-- G is non-abelian --/
  non_abelian : ¬(∀ (g h : G), g * h = h * g)
  /-- G has no non-trivial connected normal subgroups --/
  no_normal_subgroups : ∀ (H : Set G), IsNormalSubgroup H → IsConnected H → H = {1} ∨ H = Set.univ

/-- A compact simple gauge group (Lie group) --/
-- This is one of the key mathematical structures in Yang-Mills theory
class CompactSimpleGaugeGroup (G : Type) extends Group G, TopologicalSpace G where
  /-- The Lie algebra of the gauge group G --/
  lie_algebra : Type
  /-- The Lie algebra has a normed additive group structure --/
  norm_struct : NormedAddCommGroup lie_algebra
  /-- The Lie algebra is a normed vector space over ℝ --/
  space_struct : NormedSpace ℝ lie_algebra
  /-- The Lie algebra is finite-dimensional --/
  finite_dim : FiniteDimensional ℝ lie_algebra
  /-- G is compact --/
  compact : CompactSpace G
  /-- G is a simple Lie group --/
  simple : IsSimpleLieGroup G

/-- Lie algebra associated with gauge group G --/
-- Accessor for the Lie algebra of a gauge group
def LieAlgebra (G : Type) [CompactSimpleGaugeGroup G] : Type :=
  CompactSimpleGaugeGroup.lie_algebra G

/-- Connection/gauge field on R⁴ --/
-- This represents the fundamental field in Yang-Mills theory - the gauge connection
structure GaugeField (G : Type) [CompactSimpleGaugeGroup G] where
  connection : Spacetime → LieAlgebra G → LieAlgebra G
  fieldStrength : Spacetime → Spacetime → LieAlgebra G → LieAlgebra G
  action : ℝ

/-- Field strength tensor --/
-- The curvature of the gauge connection - describes the Yang-Mills field strength
def FieldStrength (G : Type) [CompactSimpleGaugeGroup G] (A : GaugeField G) :
  Spacetime → Spacetime → LieAlgebra G → LieAlgebra G :=
  A.fieldStrength

/-- Yang-Mills action functional --/
-- The action principle that governs classical Yang-Mills theory
def YangMillsAction (G : Type) [CompactSimpleGaugeGroup G] (A : GaugeField G) : ℝ :=
  A.action

/-- Schwartz space of rapidly decreasing smooth functions --/
-- Test functions for quantum field theory - imported from mathlib
def SchwartzSpace := SchwartzMap Spacetime ℝ

/-- Linear operator on a real inner product space --/
-- Represents quantum operators on Hilbert space
abbrev LinearOperator (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-- Operator-valued distributions --/
-- Quantum fields are operator-valued distributions
abbrev OperatorValuedDistribution (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  SchwartzSpace → LinearOperator H

/-- Property of vacuum state --/
-- The vacuum is the lowest energy state in the theory
def IsVacuum {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Ω : H) (H₀ : LinearOperator H) : Prop :=
  H₀ Ω = 0

/-- Conjugation action of a unitary operator `U` on an operator `A`: `U A U⁻¹`. -/
noncomputable def conjugateOperator {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (U : H ≃ₗᵢ[ℝ] H) (A : LinearOperator H) : LinearOperator H :=
  (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (A.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- The linear span of vectors obtained by applying smeared fields to the vacuum. -/
def fieldGeneratedSubmodule {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : OperatorValuedDistribution H) (Ω : H) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range fun f : SchwartzSpace => (Φ f) Ω)

/-- Wightman axioms for a quantum field theory --/
--These axioms formalize the mathematical requirements for relativistic QFT
class WightmanAxioms (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : OperatorValuedDistribution H) where
  -- W1: Relativistic invariance
  poincare_group : Type
  [poincare_structure : Group poincare_group]
  unitary_rep : poincare_group →* (H ≃ₗᵢ[ℝ] H)
  action_on_tests : poincare_group → SchwartzSpace → SchwartzSpace
  action_on_tests_one : ∀ f, action_on_tests (1 : poincare_group) f = f
  action_on_tests_mul :
    ∀ g₁ g₂ f, action_on_tests (g₁ * g₂) f = action_on_tests g₁ (action_on_tests g₂ f)
  covariance :
    ∀ g f, Φ (action_on_tests g f) = conjugateOperator (unitary_rep g) (Φ f)

  -- W2: Spectral condition
  hamiltonian : LinearOperator H
  is_hamiltonian_self_adjoint : IsSelfAdjoint hamiltonian
  is_hamiltonian_positive : hamiltonian.IsPositive

  /--
  The Clay writeup discusses clustering in terms of *spatial translations* generated by momentum
  operators `P⃗`. We do not formalize unbounded generators, but we record the resulting unitary
  representation of spatial translations `ℝ³` as data.
  -/
  spaceTranslation : Space → (H ≃ₗᵢ[ℝ] H)
  spaceTranslation_zero : spaceTranslation 0 = 1
  spaceTranslation_add :
    ∀ x y : Space, spaceTranslation (x + y) = spaceTranslation x * spaceTranslation y

  /--
  The Clay statement formulates the mass gap as: “`H` has no spectrum in `(0, Δ)`”.

  Here we use Mathlib's Banach-algebra spectrum `spectrum ℝ hamiltonian` of the (bounded) operator
  `hamiltonian`, and we additionally record two consequences explicitly referenced in the Clay
  text: non-negativity (positive energy) and vacuum energy `0`.
  -/
  spectrum_nonneg : ∀ E, E ∈ spectrum ℝ hamiltonian → 0 ≤ E
  vacuum_energy_zero : 0 ∈ spectrum ℝ hamiltonian

  -- W3: Existence of vacuum
  vacuum : H
  is_vacuum : IsVacuum vacuum hamiltonian
  vacuum_invariant : ∀ g, unitary_rep g vacuum = vacuum  -- Vacuum is Poincaré invariant
  vacuum_spatial_invariant : ∀ x : Space, spaceTranslation x vacuum = vacuum

  -- W4: Cyclicity of the vacuum
  vacuum_cyclic : Dense (fieldGeneratedSubmodule Φ vacuum : Set H)

  -- W5: Locality/causality
  locality : ∀ (f g : SchwartzMap Spacetime ℝ),
    (∀ (x y : Spacetime),
      (MinkowskiMetric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) →
    Φ f ∘L Φ g = Φ g ∘L Φ f  -- Fields commute at spacelike separation

/-!
Extra structure appearing explicitly in the Clay statement (Section 4 of the PDF).

We represent “local gauge-invariant polynomials in the curvature `F` and its covariant derivatives”
as a small *syntactic* datatype; a full treatment would require a substantial development of
classical gauge theory and renormalized QFT.
-/

/-- A syntactic language for (intended) gauge-invariant local polynomials in curvature and its derivatives. -/
inductive GaugeInvariantLocalPolynomial (G : Type) : Type
  | zero : GaugeInvariantLocalPolynomial G
  | one : GaugeInvariantLocalPolynomial G
  | curvature : GaugeInvariantLocalPolynomial G
  | covDeriv : ℕ → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | add : GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | mul : GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | trace : GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G

/-- The syntactic polynomial language is inhabited by `0`. -/
instance {G : Type} : Inhabited (GaugeInvariantLocalPolynomial G) := ⟨.zero⟩

/--
Assignment of local quantum field operators to gauge-invariant local polynomials (Clay statement, §4).

We record a *correspondence* as an injective map into operator-valued distributions.
-/
structure LocalOperatorAssignment (G : Type) (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  op : GaugeInvariantLocalPolynomial G → OperatorValuedDistribution H
  injective : Function.Injective op

/-- Vacuum expectation value of an operator. -/
noncomputable def vacuumExpectation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (A : LinearOperator H) : ℝ :=
  inner ℝ Ω (A Ω)

/-- Ordered product of smeared field operators (as a continuous linear operator). -/
noncomputable def smearedProduct {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : OperatorValuedDistribution H) : List SchwartzSpace → LinearOperator H
  | [] => ContinuousLinearMap.id ℝ H
  | f :: fs => (Φ f).comp (smearedProduct Φ fs)

/-- Wightman-style correlation functional for a list of test functions. -/
noncomputable def correlation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : OperatorValuedDistribution H) (Ω : H) (fs : List SchwartzSpace) : ℝ :=
  vacuumExpectation Ω (smearedProduct Φ fs)

/--
Short-distance agreement with perturbative predictions (Clay statement, §4).

We keep this abstract by allowing the user to pick a scaling action on test functions, and require
the correlators to converge to a “predicted” value as the scale tends to `0⁺`.
-/
structure ShortDistanceAgreement {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : OperatorValuedDistribution H) (Ω : H) where
  scale : ℝ → SchwartzSpace → SchwartzSpace
  prediction : ℝ → List SchwartzSpace → ℝ
  agrees :
    ∀ fs : List SchwartzSpace,
      Filter.Tendsto
        (fun ε : ℝ => correlation Φ Ω (fs.map (scale ε)) - prediction ε fs)
        (nhdsWithin (0 : ℝ) {ε : ℝ | 0 < ε})
        (nhds 0)

/--
A stress-energy tensor datum, with a (deliberately abstract) distributional conservation law.

The Clay statement mentions the existence of a stress tensor among the expected short-distance
structures; here we record a symmetry condition and a conservation identity in terms of a chosen
“partial derivative” operator on test functions.
-/
structure StressEnergyTensor (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- A chosen derivative operator on test functions, representing `∂_μ`. -/
  testDeriv : Fin 4 → SchwartzSpace → SchwartzSpace
  /-- Components `T_{μν}` as operator-valued distributions. -/
  T : Fin 4 → Fin 4 → OperatorValuedDistribution H
  /-- Symmetry `T_{μν} = T_{νμ}`. -/
  symmetric : ∀ μ ν, T μ ν = T ν μ
  /-- Conservation `∑_μ T_{μν}(∂_μ f) = 0` (as an operator) for all `ν` and test functions `f`. -/
  conserved : ∀ ν f, (Finset.univ.sum fun μ : Fin 4 => T μ ν (testDeriv μ f)) = 0

/-- An (abstract) operator product expansion datum. -/
structure OperatorProductExpansion (G : Type) (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  coefficient :
    GaugeInvariantLocalPolynomial G →
      GaugeInvariantLocalPolynomial G →
        GaugeInvariantLocalPolynomial G → ℝ
  /-- For fixed `A,B`, only finitely many `C` have nonzero coefficient (a minimal “local finiteness”). -/
  finite_support :
    ∀ A B, (Set.Finite {C : GaugeInvariantLocalPolynomial G | coefficient A B C ≠ 0})

/-- A quantum Yang-Mills theory --/
-- This structure combines all the components needed for a quantum Yang-Mills theory
structure QuantumYangMillsTheory (G : Type) [CompactSimpleGaugeGroup G] where
  hilbertSpace : Type  -- Physical state space
  [normedAddCommGroup : NormedAddCommGroup hilbertSpace]
  [innerProductSpace : InnerProductSpace ℝ hilbertSpace]
  [completeSpace : CompleteSpace hilbertSpace]
  field_operators : OperatorValuedDistribution hilbertSpace  -- Quantum fields
  wightman : WightmanAxioms hilbertSpace field_operators  -- Satisfies Wightman axioms
  localOperators : LocalOperatorAssignment G hilbertSpace
  shortDistance : ShortDistanceAgreement field_operators wightman.vacuum
  stressTensor : StressEnergyTensor hilbertSpace
  operatorProductExpansion : OperatorProductExpansion G hilbertSpace

  /--
  The local operator assignment is compatible with Poincaré covariance (Clay statement, §4).
  -/
  localOperators_covariant :
    ∀ g p f,
      (localOperators.op p) (wightman.action_on_tests g f) =
        conjugateOperator (wightman.unitary_rep g) ((localOperators.op p) f)

  /--
  The assigned local operators satisfy locality/causality in the same smeared sense as in the
  Wightman axioms.
  -/
  localOperators_locality :
    ∀ (p q : GaugeInvariantLocalPolynomial G) (f g : SchwartzMap Spacetime ℝ),
      (∀ (x y : Spacetime),
        (MinkowskiMetric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) →
      (localOperators.op p f) ∘L (localOperators.op q g) =
        (localOperators.op q g) ∘L (localOperators.op p f)

attribute [instance] QuantumYangMillsTheory.normedAddCommGroup
attribute [instance] QuantumYangMillsTheory.innerProductSpace
attribute [instance] QuantumYangMillsTheory.completeSpace

/-! Helper definitions for writing statements close to the Clay text. -/

/-- A “local operator at a spatial point” obtained by conjugating by spatial translation. -/
noncomputable def localOperatorAt {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (U : Space → (H ≃ₗᵢ[ℝ] H)) (x : Space) (O : LinearOperator H) : LinearOperator H :=
  conjugateOperator (U x) O

/-- “Centered” operator: its vacuum expectation value vanishes. -/
def IsCentered {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (O : LinearOperator H) : Prop :=
  vacuumExpectation Ω O = 0

/-- A “two-point function” on test functions, defined as a vacuum expectation of a product. -/
noncomputable def TwoPointFunction (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (f g : SchwartzSpace) : ℝ :=
  correlation qft.field_operators qft.wightman.vacuum [f, g]

end MillenniumYangMillsDefs
