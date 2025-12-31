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
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Logic.Function.Basic

set_option diagnostics true
set_option diagnostics.threshold 5000

namespace MillenniumYangMillsDefs

open LieGroup
/-!
# Yang-Mills Existence and Mass Gap Problem

This file formalizes the Millennium Prize problem on the Yang-Mills existence and mass gap by creating multiple definitions that I think are needed.

So my understanding is that Yang-Mills Millennium Prize problem asks two fundamental questions:
1. Does a mathematically rigorous quantum Yang-Mills theory exist?
2. Does this theory have a "mass gap" (positive minimum energy above vacuum)?

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
Two equivalent systems establishing what makes a valid quantum field theory:

1. `WightmanAxioms`: Direct approach in physical spacetime
   - Forces must obey special relativity (Poincaré invariance)
   - Energy must be positive (crucial for stability)
   - There exists a unique lowest-energy state (vacuum)
   - Physical states can be built from vacuum using fields
   - Causality: measurements at space-like separation don't interfere

2. `OsterwalderSchraderAxioms`: Alternative formulation in "imaginary time"
   - Makes mathematical analysis easier
   - Connects to statistical mechanics
   - Requires "reflection positivity" to connect back to physics

### The Mass Gap
The mathematical statement that particles have positive mass:
- Energy spectrum has a gap between vacuum (E=0) and first excited state (E≥m>0)
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

/-- Decidable equality for spacetime points (noncomputable, via classical choice). --/
noncomputable instance : DecidableEq Spacetime := Classical.decEq _

noncomputable instance : MeasurableSpace Spacetime := borel Spacetime
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

/-- Wightman axioms for a quantum field theory --/
--These axioms formalize the mathematical requirements for relativistic QFT
class WightmanAxioms (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : OperatorValuedDistribution H) where
  -- W1: Relativistic invariance
  poincare_group : Type
  [poincare_structure : Group poincare_group]
  unitary_rep : poincare_group →* (H ≃ₗᵢ[ℝ] H)
  covariance : Prop

  -- W2: Spectral condition
  hamiltonian : LinearOperator H
  is_hamiltonian_self_adjoint : IsSelfAdjoint hamiltonian
  is_hamiltonian_positive : hamiltonian.IsPositive
  spectrum_in_forward_light_cone : Prop

  -- W3: Existence of vacuum
  vacuum : H
  is_vacuum : IsVacuum vacuum hamiltonian
  vacuum_invariant : ∀ g, unitary_rep g vacuum = vacuum  -- Vacuum is Poincaré invariant

  -- W4: Cyclicity of the vacuum
  vacuum_cyclic : Prop  -- Fields acting on vacuum generate the whole Hilbert space

  -- W5: Locality/causality
  locality : ∀ (f g : SchwartzMap Spacetime ℝ),
    (∀ (x y : Spacetime),
      (MinkowskiMetric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) →
    Φ f ∘L Φ g = Φ g ∘L Φ f  -- Fields commute at spacelike separation

/-- Osterwalder-Schrader axioms --/
--Alternative axiomatization for Euclidean QFT, connecting to statistical mechanics
class OsterwalderSchraderAxioms (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : OperatorValuedDistribution H) where
  -- OS1: Temperedness
  schwinger_functions_tempered : Prop

  -- OS2: Euclidean invariance
  euclidean_group : Type
  [euclidean_structure : Group euclidean_group]
  euclidean_invariance : Prop

  -- OS3: Reflection positivity
  reflection_positivity : Prop

  -- OS4: Euclidean locality
  euclidean_locality : Prop

/-- A quantum Yang-Mills theory --/
-- This structure combines all the components needed for a quantum Yang-Mills theory
structure QuantumYangMillsTheory (G : Type) [CompactSimpleGaugeGroup G] where
  hilbertSpace : Type  -- Physical state space
  [normedAddCommGroup : NormedAddCommGroup hilbertSpace]
  [innerProductSpace : InnerProductSpace ℝ hilbertSpace]
  [completeSpace : CompleteSpace hilbertSpace]
  field_operators : OperatorValuedDistribution hilbertSpace  -- Quantum fields
  wightman : WightmanAxioms hilbertSpace field_operators  -- Satisfies Wightman axioms
  os_axioms : OsterwalderSchraderAxioms hilbertSpace field_operators  -- Satisfies OS axioms
  hamiltonian : LinearOperator hilbertSpace  -- Energy operator
  vacuum : hilbertSpace  -- Ground state
  is_vacuum : IsVacuum vacuum hamiltonian  -- Vacuum properties
  twoPointFunction : Spacetime → Spacetime → ℝ
  -- Connection to classical Yang-Mills
  classical_limit : Prop

attribute [instance] QuantumYangMillsTheory.normedAddCommGroup
attribute [instance] QuantumYangMillsTheory.innerProductSpace
attribute [instance] QuantumYangMillsTheory.completeSpace

/-- Two-point correlation function --/
--Physical measurable quantity - propagator in the quantum theory
def TwoPointFunction (G : Type) [CompactSimpleGaugeGroup G]
  (qft : QuantumYangMillsTheory G) (x y : Spacetime) : ℝ :=
  qft.twoPointFunction x y

end MillenniumYangMillsDefs
