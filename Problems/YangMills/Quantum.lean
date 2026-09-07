import Problems.Common.Euclidean
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
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Logic.Function.Basic

namespace MillenniumYangMillsDefs

open LieGroup
open MeasureTheory
open scoped BigOperators Manifold ContDiff
/-!
# Yang-Mills Existence and Mass Gap Problem

Definitions for the Clay Millennium problem “Yang–Mills existence and mass gap”.

**Warning (September 2026 review).**  This file and its companions are an axiomatic *sketch* of a
quantum Yang–Mills theory, not a faithful formal statement of the Clay problem, and the existence
statement in `Problems.YangMills.Millennium` is **not a valid prize target**.  The data below are
characterised by too few properties to pin down what they are meant to represent: `GaugeField`
stores the connection and the curvature as independent data, the Lie algebra carries no bracket,
`poincare_group` is an arbitrary group unrelated to the Hamiltonian, the Osterwalder–Schrader
reconstruction is stated as an equality of Schwinger and Wightman functions, and the "unbounded"
physical Hamiltonian is tied to the spectrum of a bounded operator.  As a result the existence
statement can be satisfied by a two-dimensional toy model.  (Before September 2026 the vacuum
uniqueness axiom was contradictory and the structure was uninhabited; that slip is fixed, but the
statement remains a sketch.)  See `README.md` for the status and the list of known defects.

The core objects are:
* four-dimensional spacetime and compact simple gauge groups;
* gauge fields, curvature, and the Yang--Mills action;
* Wightman-style quantum field properties;
* Hamiltonian spectral gap conditions and clustering estimates.

## References
- Jaffe, A., & Witten, E. "Quantum Yang-Mills Theory"
- Streater & Wightman (1964): "PCT, Spin and Statistics, and All That"
- Osterwalder & Schrader (1973, 1975): Euclidean Green's function framework
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {I: ModelWithCorners 𝕜 E H}

/-- Spacetime `ℝ⁴`, using Mathlib's canonical `ℓ²` norm and inner product. -/
@[reducible]
def Spacetime : Type :=
  EuclideanCoordinateSpace ℝ 4

/-- Coordinate directions for the four-dimensional spacetime in the Clay statement. -/
@[reducible]
def SpacetimeDirection : Type :=
  Fin 4

/-- Spatial points `ℝ³` (used in the Clay clustering discussion). -/
@[reducible]
def Space : Type :=
  EuclideanCoordinateSpace ℝ 3

/-- Coordinate directions for spatial translations. -/
@[reducible]
def SpatialDirection : Type :=
  Fin 3

/-- Decidable equality for spacetime points (noncomputable, via classical choice). --/
noncomputable instance : DecidableEq Spacetime := Classical.decEq _

/-- Use the Borel σ-algebra on `Spacetime = ℝ⁴`. -/
noncomputable instance : MeasurableSpace Spacetime := borel Spacetime

/-- `Spacetime` is a Borel space (by definition of the model). -/
noncomputable instance : BorelSpace Spacetime := ⟨rfl⟩

/--
Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`.

Index `0` represents time, and indices `1`, `2`, `3` represent spatial directions.
-/
def minkowski_metric (x y : Spacetime) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- A simple Lie group: non-abelian, with no non-trivial nonempty connected normal subgroups. -/
class IsSimpleLieGroup (G : Type) [Group G] [TopologicalSpace G] : Prop where
  /-- G is non-abelian --/
  non_abelian : ¬(∀ (g h : G), g * h = h * g)
  /-- G has no non-trivial nonempty connected normal subgroups. -/
  no_normal_subgroups :
    ∀ H : Subgroup G, H.Normal → IsPreconnected (H : Set G) →
      H = ⊥ ∨ H = ⊤

/--
A compact simple gauge group for the Yang--Mills statement.

This bundles the group/topology, continuity of group operations, compactness, and a finite
dimensional real Lie algebra.  It also records that the group admits a genuine smooth
`LieGroup` model.
-/
class CompactSimpleGaugeGroup (G : Type) extends Group G, TopologicalSpace G where
  /-- The group operations are continuous for the topology on `G`. -/
  is_topological_group : IsTopologicalGroup G
  /-- Clay's compact simple gauge groups are connected Lie groups. -/
  connected : ConnectedSpace G
  /-- The Lie algebra of the gauge group `G`. -/
  lie_algebra : Type
  /-- The Lie algebra has a normed additive group structure. -/
  norm_struct : NormedAddCommGroup lie_algebra
  /-- The Lie algebra is a normed vector space over `ℝ`. -/
  space_struct : NormedSpace ℝ lie_algebra
  /-- The Lie algebra is finite-dimensional. -/
  finite_dim : FiniteDimensional ℝ lie_algebra
  /-- A smooth manifold model witnessing that `G` is a smooth real Lie group. -/
  smooth_lie_group_model :
    ∃ (M V : Type) (_ : TopologicalSpace M) (_ : NormedAddCommGroup V)
      (_ : NormedSpace ℝ V), ∃ (I : ModelWithCorners ℝ V M) (_ : ChartedSpace M G),
        LieGroup I ∞ G ∧ FiniteDimensional ℝ V ∧
          Nonempty (lie_algebra ≃ₗ[ℝ] V)
  /-- G is compact --/
  compact : CompactSpace G
  /-- G is a simple Lie group --/
  simple : IsSimpleLieGroup G

instance (G : Type) [CompactSimpleGaugeGroup G] : IsTopologicalGroup G :=
  CompactSimpleGaugeGroup.is_topological_group

instance (G : Type) [CompactSimpleGaugeGroup G] : ConnectedSpace G :=
  CompactSimpleGaugeGroup.connected

instance (G : Type) [CompactSimpleGaugeGroup G] :
    NormedAddCommGroup (CompactSimpleGaugeGroup.lie_algebra G) :=
  CompactSimpleGaugeGroup.norm_struct

instance (G : Type) [CompactSimpleGaugeGroup G] :
    NormedSpace ℝ (CompactSimpleGaugeGroup.lie_algebra G) :=
  CompactSimpleGaugeGroup.space_struct

instance (G : Type) [CompactSimpleGaugeGroup G] :
    FiniteDimensional ℝ (CompactSimpleGaugeGroup.lie_algebra G) :=
  CompactSimpleGaugeGroup.finite_dim

/-- The smooth Lie-group model recorded in the compact-simple gauge-group package. -/
theorem CompactSimpleGaugeGroup.exists_smooth_model
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (M V : Type) (_ : TopologicalSpace M) (_ : NormedAddCommGroup V)
      (_ : NormedSpace ℝ V), ∃ (I : ModelWithCorners ℝ V M) (_ : ChartedSpace M G),
        LieGroup I ∞ G ∧ FiniteDimensional ℝ V ∧
          Nonempty (CompactSimpleGaugeGroup.lie_algebra G ≃ₗ[ℝ] V) :=
  CompactSimpleGaugeGroup.smooth_lie_group_model (G := G)

/-- The Lie algebra associated with a compact simple gauge group. -/
abbrev LieAlgebra (G : Type) [CompactSimpleGaugeGroup G] : Type :=
  CompactSimpleGaugeGroup.lie_algebra G

/-- A classical gauge field on spacetime, containing a connection and its curvature components. -/
structure GaugeField (G : Type) [CompactSimpleGaugeGroup G] where
  /-- Lie-algebra-valued connection components `A_μ(x)`. -/
  connection : Spacetime → SpacetimeDirection → LieAlgebra G
  /-- Lie-algebra-valued curvature components `F_{μν}(x)`. -/
  field_strength : Spacetime → SpacetimeDirection → SpacetimeDirection → LieAlgebra G

/-- The field-strength tensor, i.e. the curvature data of a gauge field. -/
def field_strength (G : Type) [CompactSimpleGaugeGroup G] (A : GaugeField G) :
  Spacetime → SpacetimeDirection → SpacetimeDirection → LieAlgebra G :=
  A.field_strength

/-- Pointwise squared norm `∑_{μ,ν} ‖F_{μν}(x)‖²` of the curvature. -/
noncomputable def curvature_norm_sq
    (G : Type) [CompactSimpleGaugeGroup G] (A : GaugeField G) (x : Spacetime) : ℝ :=
  ∑ μ : SpacetimeDirection, ∑ ν : SpacetimeDirection, ‖A.field_strength x μ ν‖ ^ 2

/-- The Euclidean Yang--Mills action `∫_{ℝ⁴} ∑_{μ,ν} ‖F_{μν}(x)‖² dx`. -/
noncomputable def yang_mills_action
    (G : Type) [CompactSimpleGaugeGroup G] (A : GaugeField G) : ℝ :=
  ∫ x : Spacetime, curvature_norm_sq G A x

/-- The bare Euclidean Yang--Mills action is nonnegative. -/
theorem yang_mills_action_nonneg
    (G : Type) [CompactSimpleGaugeGroup G] (A : GaugeField G) :
    0 ≤ yang_mills_action G A := by
  apply integral_nonneg
  intro x
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/--
The positive coupling constant `g` appearing in the classical Yang--Mills Lagrangian.
-/
structure YangMillsCoupling where
  /-- The numerical value of the coupling constant. -/
  value : ℝ
  /-- Clay's Yang--Mills setup uses a positive coupling. -/
  positive : 0 < value

namespace YangMillsCoupling

/-- The coupling constant is nonzero. -/
theorem ne_zero (g : YangMillsCoupling) : g.value ≠ 0 :=
  ne_of_gt g.positive

/-- The standard positive factor `1 / (4 g^2)` in the classical Yang--Mills action. -/
noncomputable def action_scale (g : YangMillsCoupling) : ℝ :=
  (4 * g.value ^ 2)⁻¹

/-- The factor `1 / (4 g^2)` is positive for positive coupling. -/
theorem action_scale_pos (g : YangMillsCoupling) : 0 < g.action_scale := by
  dsimp [action_scale]
  exact inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_ne_zero g.ne_zero))

/-- The unit coupling constant. -/
def unit : YangMillsCoupling where
  value := 1
  positive := by norm_num

end YangMillsCoupling

/--
Classical Yang--Mills Lagrangian density coefficient applied to a curvature norm-square term:
`(1 / (4 g^2)) ‖F_A‖^2`.
-/
noncomputable def yang_mills_lagrangian_density
    (g : YangMillsCoupling) (curvatureNormSq : ℝ) : ℝ :=
  g.action_scale * curvatureNormSq

/--
Classical Yang--Mills action with explicit positive coupling `g`.
-/
noncomputable def coupled_yang_mills_action
    (G : Type) [CompactSimpleGaugeGroup G] (g : YangMillsCoupling) (A : GaugeField G) : ℝ :=
  g.action_scale * yang_mills_action G A

/-- Nonnegative bare action gives nonnegative coupled classical Yang--Mills action. -/
theorem coupled_yang_mills_action_nonneg
    (G : Type) [CompactSimpleGaugeGroup G] (g : YangMillsCoupling) (A : GaugeField G) :
    0 ≤ coupled_yang_mills_action G g A :=
  mul_nonneg (le_of_lt g.action_scale_pos) (yang_mills_action_nonneg G A)

/-!
## A finite-dimensional classical Yang--Mills model

The classical starting point is a connection, its curvature, and the Yang--Mills action
`∫ ‖F_A‖²`.  The finite-dimensional matrix-connection model below gives direct definitions and
proofs for curvature, gauge conjugation, flatness, and the finite action.

For a finite index type `ι`, a matrix connection is a tuple of bounded linear operators.  Its
curvature is the commutator `[Aᵢ,Aⱼ]`, and its action is the finite sum of squared operator norms.
-/

/-- A finite-dimensional matrix connection: one bounded operator in each direction. -/
structure MatrixConnection (ι V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The connection component `Aᵢ`. -/
  potential : ι → V →L[ℝ] V

namespace MatrixConnection

variable {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Two matrix connections are equal when all their potential components are equal. -/
@[ext]
theorem ext {A B : MatrixConnection ι V}
    (h : ∀ i : ι, A.potential i = B.potential i) :
    A = B := by
  cases A
  cases B
  congr
  exact funext h

/-- Curvature of a matrix connection: the commutator `[Aᵢ,Aⱼ]`. -/
noncomputable def curvature (A : MatrixConnection ι V) (i j : ι) : V →L[ℝ] V :=
  (A.potential i).comp (A.potential j) - (A.potential j).comp (A.potential i)

/-- Covariant commutator with the connection component `Aᵢ`: `[Aᵢ,T]`. -/
noncomputable def covariant_commutator (A : MatrixConnection ι V) (i : ι) (T : V →L[ℝ] V) :
    V →L[ℝ] V :=
  (A.potential i).comp T - T.comp (A.potential i)

/-- Mixed curvature term from two matrix connections: `[Aᵢ,Bⱼ] + [Bᵢ,Aⱼ]`. -/
noncomputable def mixed_curvature (A B : MatrixConnection ι V) (i j : ι) : V →L[ℝ] V :=
  (A.potential i).comp (B.potential j) + (B.potential i).comp (A.potential j) -
    ((A.potential j).comp (B.potential i) + (B.potential j).comp (A.potential i))

/-- A matrix connection is flat when all curvature components vanish. -/
def IsFlat (A : MatrixConnection ι V) : Prop :=
  ∀ i j : ι, A.curvature i j = 0

/-- The zero matrix connection. -/
noncomputable def zero : MatrixConnection ι V where
  potential _ := 0

/-- Pointwise addition of matrix connections. -/
noncomputable def add (A B : MatrixConnection ι V) : MatrixConnection ι V where
  potential i := A.potential i + B.potential i

/-- A matrix connection whose components are scalar multiples of one fixed operator. -/
noncomputable def scalar_multiple (weight : ι → ℝ) (T : V →L[ℝ] V) : MatrixConnection ι V where
  potential i := weight i • T

/-- Scale every component of a matrix connection by the same real scalar. -/
noncomputable def scale (c : ℝ) (A : MatrixConnection ι V) : MatrixConnection ι V where
  potential i := c • A.potential i

/-- Negate every component of a matrix connection. -/
noncomputable def neg (A : MatrixConnection ι V) : MatrixConnection ι V :=
  A.scale (-1)

/-- Adding the zero matrix connection on the right leaves a matrix connection unchanged. -/
@[simp]
theorem add_zero (A : MatrixConnection ι V) :
    add A zero = A := by
  ext i v
  simp [add, zero]

/-- Adding the zero matrix connection on the left leaves a matrix connection unchanged. -/
@[simp]
theorem zero_add (A : MatrixConnection ι V) :
    add zero A = A := by
  ext i v
  simp [add, zero]

/-- Pointwise addition of matrix connections is commutative. -/
theorem add_comm (A B : MatrixConnection ι V) :
    add A B = add B A := by
  ext i v
  simpa [add] using _root_.add_comm ((A.potential i) v) ((B.potential i) v)

/-- Pointwise addition of matrix connections is associative. -/
theorem add_assoc (A B C : MatrixConnection ι V) :
    add (add A B) C = add A (add B C) := by
  ext i v
  simpa [add] using _root_.add_assoc ((A.potential i) v) ((B.potential i) v)
    ((C.potential i) v)

/-- Scaling by `0` gives the zero matrix connection. -/
@[simp]
theorem scale_zero (A : MatrixConnection ι V) :
    A.scale 0 = zero := by
  ext i v
  simp [scale, zero]

/-- Scaling by `1` leaves a matrix connection unchanged. -/
@[simp]
theorem scale_one (A : MatrixConnection ι V) :
    A.scale 1 = A := by
  ext i v
  simp [scale]

/-- Negating a matrix connection is scaling by `-1`. -/
theorem neg_eq_scale (A : MatrixConnection ι V) :
    A.neg = A.scale (-1) := rfl

/-- Successive scalings multiply their scale factors. -/
theorem scale_scale (c d : ℝ) (A : MatrixConnection ι V) :
    (A.scale c).scale d = A.scale (d * c) := by
  ext i v
  simp [scale, smul_smul]

/-- Scaling distributes over pointwise addition of matrix connections. -/
theorem scale_add (c : ℝ) (A B : MatrixConnection ι V) :
    (add A B).scale c = add (A.scale c) (B.scale c) := by
  ext i v
  simp [add, scale, smul_add]

/-- Scaling is additive in the scalar variable. -/
theorem scale_add_scalar (c d : ℝ) (A : MatrixConnection ι V) :
    A.scale (c + d) = add (A.scale c) (A.scale d) := by
  ext i v
  simp [add, scale, add_smul]

/-- Adding a matrix connection to its negation gives the zero connection. -/
@[simp]
theorem add_neg (A : MatrixConnection ι V) :
    add A A.neg = zero := by
  ext i v
  simp [add, neg, scale, zero]

/-- Adding the negation of a matrix connection to it gives the zero connection. -/
@[simp]
theorem neg_add (A : MatrixConnection ι V) :
    add A.neg A = zero := by
  rw [add_comm, add_neg]

/-- Double negation leaves a matrix connection unchanged. -/
@[simp]
theorem neg_neg (A : MatrixConnection ι V) :
    A.neg.neg = A := by
  ext i v
  simp [neg, scale]

/-- Conjugation of a bounded operator by a gauge transformation. -/
noncomputable def conjugate_by_gauge (U : V ≃ₗᵢ[ℝ] V) (T : V →L[ℝ] V) : V →L[ℝ] V :=
  (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (T.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- The zero matrix connection has zero curvature. -/
@[simp]
theorem curvature_zero (i j : ι) :
    (zero : MatrixConnection ι V).curvature i j = 0 := by
  simp [zero, curvature]

/-- Scalar-multiple matrix connections have zero curvature. -/
@[simp]
theorem curvature_scalar_multiple (weight : ι → ℝ) (T : V →L[ℝ] V) (i j : ι) :
    (scalar_multiple weight T).curvature i j = 0 := by
  ext v
  simp [scalar_multiple, curvature, smul_smul, mul_comm]

/-- Scaling a matrix connection scales curvature quadratically. -/
theorem curvature_scale (c : ℝ) (A : MatrixConnection ι V) (i j : ι) :
    (A.scale c).curvature i j = (c * c) • A.curvature i j := by
  ext v
  simp [scale, curvature, smul_sub, smul_smul]

/-- Curvature of a pointwise sum expands into both curvatures plus the mixed curvature term. -/
theorem curvature_add (A B : MatrixConnection ι V) (i j : ι) :
    (add A B).curvature i j =
      A.curvature i j + B.curvature i j + mixed_curvature A B i j := by
  ext v
  simp [add, curvature, mixed_curvature]
  abel

/-- The mixed curvature term is symmetric in the two connections. -/
theorem mixed_curvature_comm (A B : MatrixConnection ι V) (i j : ι) :
    mixed_curvature B A i j = mixed_curvature A B i j := by
  ext v
  simp [mixed_curvature]
  abel

/-- The mixed curvature term is antisymmetric in its two directions. -/
theorem mixed_curvature_swap (A B : MatrixConnection ι V) (i j : ι) :
    mixed_curvature A B j i = -mixed_curvature A B i j := by
  ext v
  simp [mixed_curvature]

/-- If each component of `A` commutes with each component of `B`, the mixed curvature vanishes. -/
theorem mixed_curvature_zero_of_cross_commute {A B : MatrixConnection ι V}
    (hcomm : ∀ i j : ι, (A.potential i).comp (B.potential j) =
      (B.potential j).comp (A.potential i)) (i j : ι) :
    mixed_curvature A B i j = 0 := by
  ext v
  simp [mixed_curvature, hcomm i j, hcomm j i]
  abel

/--
When the mixed curvature vanishes, the curvature of a sum is the sum of curvatures.
-/
theorem curvature_add_of_mixed_zero {A B : MatrixConnection ι V}
    (hmix : ∀ i j : ι, mixed_curvature A B i j = 0) (i j : ι) :
    (add A B).curvature i j = A.curvature i j + B.curvature i j := by
  rw [curvature_add A B i j, hmix i j]
  simp

/--
The sum of two flat matrix connections is flat when their mixed curvature term vanishes.
-/
theorem add_flat_of_mixed_zero
    {A B : MatrixConnection ι V} (hA : A.IsFlat) (hB : B.IsFlat)
    (hmix : ∀ i j : ι, mixed_curvature A B i j = 0) :
    (add A B).IsFlat := by
  intro i j
  rw [curvature_add A B i j, hA i j, hB i j, hmix i j]
  simp

/--
The sum of two flat matrix connections is flat when their components commute across the two
connections.
-/
theorem add_flat_of_cross_commute
    {A B : MatrixConnection ι V} (hA : A.IsFlat) (hB : B.IsFlat)
    (hcomm : ∀ i j : ι, (A.potential i).comp (B.potential j) =
      (B.potential j).comp (A.potential i)) :
    (add A B).IsFlat :=
  add_flat_of_mixed_zero hA hB
    (mixed_curvature_zero_of_cross_commute hcomm)

/-- Negating a matrix connection leaves curvature unchanged. -/
@[simp]
theorem curvature_neg (A : MatrixConnection ι V) (i j : ι) :
    A.neg.curvature i j = A.curvature i j := by
  rw [neg_eq_scale, curvature_scale]
  simp

/-- The zero matrix connection is flat. -/
theorem zero_flat :
    (zero : MatrixConnection ι V).IsFlat := by
  intro i j
  exact curvature_zero i j

/-- Scalar-multiple matrix connections are flat. -/
theorem scalar_multiple_flat (weight : ι → ℝ) (T : V →L[ℝ] V) :
    (scalar_multiple weight T).IsFlat := by
  intro i j
  exact curvature_scalar_multiple weight T i j

/-- Scaling preserves flatness of matrix connections. -/
theorem scale_flat {c : ℝ} {A : MatrixConnection ι V} (hflat : A.IsFlat) :
    (A.scale c).IsFlat := by
  intro i j
  rw [curvature_scale c A i j, hflat i j]
  simp

/-- Negation preserves flatness of matrix connections. -/
theorem neg_flat {A : MatrixConnection ι V} (hflat : A.IsFlat) :
    A.neg.IsFlat := by
  intro i j
  rw [curvature_neg A i j, hflat i j]

/-- Nonzero scaling preserves and reflects flatness of matrix connections. -/
theorem scale_flat_iff {c : ℝ} (hc : c ≠ 0) (A : MatrixConnection ι V) :
    (A.scale c).IsFlat ↔ A.IsFlat := by
  constructor
  · intro hflat i j
    have hij : (c * c) • A.curvature i j = 0 := by
      rw [← curvature_scale c A i j]
      exact hflat i j
    have hcc : c * c ≠ 0 := mul_ne_zero hc hc
    exact (smul_eq_zero.mp hij).resolve_left hcc
  · exact scale_flat

/-- Negation preserves and reflects flatness of matrix connections. -/
theorem neg_flat_iff (A : MatrixConnection ι V) :
    A.neg.IsFlat ↔ A.IsFlat := by
  rw [neg_eq_scale, scale_flat_iff (by norm_num : (-1 : ℝ) ≠ 0)]

/-- The components of a scalar-multiple matrix connection commute pairwise. -/
theorem scalar_multiple_pairwise_commute (weight : ι → ℝ) (T : V →L[ℝ] V) :
    ∀ i j : ι, ((scalar_multiple weight T).potential i).comp
        ((scalar_multiple weight T).potential j) =
      ((scalar_multiple weight T).potential j).comp
        ((scalar_multiple weight T).potential i) :=
  fun i j => by
    ext v
    simp [scalar_multiple, smul_smul, mul_comm]

/-- The zero matrix connection has zero covariant commutator. -/
@[simp]
theorem covariant_commutator_zero (i : ι) (T : V →L[ℝ] V) :
    (zero : MatrixConnection ι V).covariant_commutator i T = 0 := by
  ext v
  simp [covariant_commutator, zero]

/-- Curvature is zero on the diagonal. -/
@[simp]
theorem curvature_self (A : MatrixConnection ι V) (i : ι) :
    A.curvature i i = 0 := by
  simp [curvature]

/-- Curvature is antisymmetric in the two matrix directions. -/
theorem curvature_swap (A : MatrixConnection ι V) (i j : ι) :
    A.curvature j i = -A.curvature i j := by
  simp [curvature, sub_eq_add_neg]

/--
The finite matrix Bianchi identity:
`[Aᵢ,Fⱼₖ] + [Aⱼ,Fₖᵢ] + [Aₖ,Fᵢⱼ] = 0`.
-/
theorem bianchi_identity (A : MatrixConnection ι V) (i j k : ι) :
    A.covariant_commutator i (A.curvature j k) +
      A.covariant_commutator j (A.curvature k i) +
      A.covariant_commutator k (A.curvature i j) = 0 := by
  ext v
  simp [covariant_commutator, curvature]
  abel

/-- Flatness is exactly pairwise commutation of the connection components. -/
theorem flat_iff_pairwise_commute (A : MatrixConnection ι V) :
    A.IsFlat ↔
      ∀ i j : ι, (A.potential i).comp (A.potential j) =
        (A.potential j).comp (A.potential i) := by
  constructor
  · intro h i j
    exact sub_eq_zero.mp (h i j)
  · intro h i j
    exact sub_eq_zero.mpr (h i j)

/-- Gauge transformation of a matrix connection by conjugating all components. -/
noncomputable def gauge_transform (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    MatrixConnection ι V where
  potential i :=
    (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((A.potential i).comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- The identity gauge transformation leaves a matrix connection unchanged. -/
@[simp]
theorem gauge_transform_refl (A : MatrixConnection ι V) :
    A.gauge_transform (LinearIsometryEquiv.refl ℝ V) = A := by
  cases A
  rfl

/-- Gauge transformations compose as conjugations. -/
theorem gauge_transform_trans (U V' : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).gauge_transform V' = A.gauge_transform (U.trans V') := by
  ext i v
  simp [gauge_transform, LinearIsometryEquiv.trans]
  have hsymm : (U.trans V').symm v = U.symm (V'.symm v) := by
    apply (U.trans V').injective
    simp [LinearIsometryEquiv.trans]
  exact congrArg (A.potential i) hsymm.symm

/-- Applying a gauge transformation and then its inverse returns the original matrix connection. -/
@[simp]
theorem gauge_transform_symm (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).gauge_transform U.symm = A := by
  ext i v
  simp [gauge_transform]

/-- Applying the inverse gauge transformation and then the gauge transformation returns the original connection. -/
@[simp]
theorem gauge_transform_symm_left (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U.symm).gauge_transform U = A := by
  ext i v
  simp [gauge_transform]

/-- Gauge transformations fix the zero matrix connection. -/
@[simp]
theorem gauge_transform_zero (U : V ≃ₗᵢ[ℝ] V) :
    (zero : MatrixConnection ι V).gauge_transform U = zero := by
  ext i v
  simp [gauge_transform, zero]

/--
Gauge transformations preserve the scalar-multiple family, conjugating only the fixed operator.
-/
theorem gauge_transform_scalar_multiple
    (U : V ≃ₗᵢ[ℝ] V) (weight : ι → ℝ) (T : V →L[ℝ] V) :
    (scalar_multiple weight T).gauge_transform U =
      scalar_multiple weight (conjugate_by_gauge U T) := by
  ext i v
  simp [gauge_transform, scalar_multiple, conjugate_by_gauge]

/-- Gauge transformation distributes over pointwise addition of matrix connections. -/
theorem gauge_transform_add
    (U : V ≃ₗᵢ[ℝ] V) (A B : MatrixConnection ι V) :
    (add A B).gauge_transform U = add (A.gauge_transform U) (B.gauge_transform U) := by
  ext i v
  simp [gauge_transform, add]

/-- Gauge transformation commutes with scaling a matrix connection. -/
theorem gauge_transform_scale (U : V ≃ₗᵢ[ℝ] V) (c : ℝ) (A : MatrixConnection ι V) :
    (A.scale c).gauge_transform U = (A.gauge_transform U).scale c := by
  ext i v
  simp [gauge_transform, scale]

/--
The covariant commutator is gauge-covariant:
`[U Aᵢ U⁻¹, U T U⁻¹] = U [Aᵢ,T] U⁻¹`.
-/
theorem covariant_commutator_gauge_transform
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) (i : ι) (T : V →L[ℝ] V) :
    (A.gauge_transform U).covariant_commutator i
        ((U.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (T.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))) =
      (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((A.covariant_commutator i T).comp
          (U.symm.toContinuousLinearEquiv.toContinuousLinearMap)) := by
  ext v
  simp [covariant_commutator, gauge_transform]

/-- Curvature is gauge-covariant: `F_{U·A,ij} = U F_{A,ij} U⁻¹`. -/
theorem curvature_gauge_transform (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) (i j : ι) :
    (A.gauge_transform U).curvature i j =
      (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((A.curvature i j).comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [curvature, gauge_transform]

/-- Conjugating a bounded operator by a linear isometry equivalence preserves its norm. -/
theorem norm_conjugate_eq (U : V ≃ₗᵢ[ℝ] V) (T : V →L[ℝ] V) :
    ‖(U.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (T.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))‖ = ‖T‖ := by
  let C : V →L[ℝ] V :=
    (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (T.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))
  have hle : ‖C‖ ≤ ‖T‖ := by
    refine ContinuousLinearMap.opNorm_le_bound C (norm_nonneg T) fun x => ?_
    calc
      ‖C x‖ = ‖T (U.symm x)‖ := by
        simp [C]
      _ ≤ ‖T‖ * ‖U.symm x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
  have hge : ‖T‖ ≤ ‖C‖ := by
    refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg C) fun x => ?_
    calc
      ‖T x‖ = ‖C (U x)‖ := by
        simp [C]
      _ ≤ ‖C‖ * ‖U x‖ := C.le_opNorm _
      _ = ‖C‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
  exact le_antisymm hle hge

/-- Gauge transformation preserves flatness in the matrix model. -/
theorem gauge_transform_flat {U : V ≃ₗᵢ[ℝ] V} {A : MatrixConnection ι V}
    (hflat : A.IsFlat) :
    (A.gauge_transform U).IsFlat := by
  intro i j
  rw [curvature_gauge_transform U A i j, hflat i j]
  simp

/-- Gauge transformation preserves and reflects flatness in the matrix model. -/
theorem gauge_transform_flat_iff (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).IsFlat ↔ A.IsFlat := by
  constructor
  · intro hflat
    have hback : ((A.gauge_transform U).gauge_transform U.symm).IsFlat :=
      gauge_transform_flat (U := U.symm) hflat
    simpa [gauge_transform_symm] using hback
  · exact gauge_transform_flat

variable [Fintype ι]

/-- Finite Yang--Mills action `Σᵢⱼ ‖Fᵢⱼ‖²` for the matrix model. -/
noncomputable def action (A : MatrixConnection ι V) : ℝ :=
  ∑ i : ι, ∑ j : ι, ‖A.curvature i j‖ ^ (2 : ℕ)

/-- Finite Yang--Mills action with the classical coupling factor `1 / (4 g^2)`. -/
noncomputable def coupled_action (g : YangMillsCoupling) (A : MatrixConnection ι V) : ℝ :=
  g.action_scale * A.action

/-- The finite Yang--Mills action is nonnegative. -/
theorem action_nonneg (A : MatrixConnection ι V) :
    0 ≤ A.action := by
  dsimp [action]
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖A.curvature i j‖

/-- The finite coupled Yang--Mills action is nonnegative. -/
theorem coupled_action_nonneg (g : YangMillsCoupling) (A : MatrixConnection ι V) :
    0 ≤ A.coupled_action g :=
  mul_nonneg (le_of_lt g.action_scale_pos) A.action_nonneg

/-- Flat connections have zero finite Yang--Mills action. -/
theorem flat_action_zero (A : MatrixConnection ι V) (hflat : A.IsFlat) :
    A.action = 0 := by
  dsimp [action]
  refine Finset.sum_eq_zero fun i _ => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hflat i j]
  simp

/--
The sum of two flat matrix connections with cross-commuting components has zero Yang--Mills
action.
-/
theorem action_add_zero_of_cross_commute
    {A B : MatrixConnection ι V} (hA : A.IsFlat) (hB : B.IsFlat)
    (hcomm : ∀ i j : ι, (A.potential i).comp (B.potential j) =
      (B.potential j).comp (A.potential i)) :
    (add A B).action = 0 :=
  flat_action_zero (add A B)
    (add_flat_of_cross_commute hA hB hcomm)

/-- The zero matrix connection has zero Yang--Mills action. -/
@[simp]
theorem action_zero :
    (zero : MatrixConnection ι V).action = 0 := by
  exact flat_action_zero zero zero_flat

/-- Scalar-multiple matrix connections have zero Yang--Mills action. -/
@[simp]
theorem action_scalar_multiple (weight : ι → ℝ) (T : V →L[ℝ] V) :
    (scalar_multiple weight T).action = 0 := by
  exact flat_action_zero (scalar_multiple weight T) (scalar_multiple_flat weight T)

/-- Zero finite Yang--Mills action forces the matrix connection to be flat. -/
theorem flat_of_zero_action (A : MatrixConnection ι V) (hA : A.action = 0) :
    A.IsFlat := by
  intro i j
  dsimp [action] at hA
  have houter :
      ∀ i ∈ (Finset.univ : Finset ι),
        (∑ j : ι, ‖A.curvature i j‖ ^ (2 : ℕ)) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A.curvature i j‖)).mp hA
  have hinner :
      ∀ j ∈ (Finset.univ : Finset ι), ‖A.curvature i j‖ ^ (2 : ℕ) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ‖A.curvature i j‖)).mp
        (houter i (Finset.mem_univ i))
  have hnorm : ‖A.curvature i j‖ = 0 := by
    exact sq_eq_zero_iff.mp (hinner j (Finset.mem_univ j))
  exact norm_eq_zero.mp hnorm

/-- Zero action is equivalent to flatness in the finite matrix model. -/
theorem action_eq_zero_iff_flat (A : MatrixConnection ι V) :
    A.action = 0 ↔ A.IsFlat :=
  ⟨A.flat_of_zero_action, A.flat_action_zero⟩

/-- Zero coupled finite action is equivalent to flatness for positive coupling. -/
theorem coupled_action_eq_zero_iff_flat (g : YangMillsCoupling) (A : MatrixConnection ι V) :
    A.coupled_action g = 0 ↔ A.IsFlat := by
  rw [coupled_action, mul_eq_zero, action_eq_zero_iff_flat]
  exact ⟨fun h => h.resolve_left (ne_of_gt g.action_scale_pos), fun h => Or.inr h⟩

/-- Nonzero scaling preserves and reflects zero finite Yang--Mills action. -/
theorem action_scale_eq_zero_iff {c : ℝ} (hc : c ≠ 0) (A : MatrixConnection ι V) :
    (A.scale c).action = 0 ↔ A.action = 0 := by
  rw [action_eq_zero_iff_flat, action_eq_zero_iff_flat, scale_flat_iff hc A]

/-- Negation preserves and reflects zero finite Yang--Mills action. -/
theorem action_neg_eq_zero_iff (A : MatrixConnection ι V) :
    A.neg.action = 0 ↔ A.action = 0 := by
  rw [neg_eq_scale, action_scale_eq_zero_iff (by norm_num : (-1 : ℝ) ≠ 0)]

/-- Zero action is equivalent to pairwise commutation of the connection components. -/
theorem action_eq_zero_iff_pairwise_commute (A : MatrixConnection ι V) :
    A.action = 0 ↔
      ∀ i j : ι, (A.potential i).comp (A.potential j) =
        (A.potential j).comp (A.potential i) := by
  rw [action_eq_zero_iff_flat, flat_iff_pairwise_commute]

/-- Positive finite Yang--Mills action is equivalent to non-flatness. -/
theorem action_pos_iff_not_flat (A : MatrixConnection ι V) :
    0 < A.action ↔ ¬ A.IsFlat := by
  constructor
  · intro hpos hflat
    exact (ne_of_gt hpos) (A.flat_action_zero hflat)
  · intro hnot
    have hne : A.action ≠ 0 := by
      intro hzero
      exact hnot ((action_eq_zero_iff_flat A).mp hzero)
    exact lt_of_le_of_ne (action_nonneg A) (fun hzero : 0 = A.action => hne hzero.symm)

/-- Positive finite Yang--Mills action is equivalent to some nonzero curvature component. -/
theorem action_pos_iff_exists_curvature_ne_zero (A : MatrixConnection ι V) :
    0 < A.action ↔ ∃ i j : ι, A.curvature i j ≠ 0 := by
  rw [action_pos_iff_not_flat]
  constructor
  · intro hnotFlat
    by_contra hnone
    apply hnotFlat
    intro i j
    by_contra hcurv
    exact hnone ⟨i, j, hcurv⟩
  · rintro ⟨i, j, hcurv⟩ hflat
    exact hcurv (hflat i j)

/-- Positive finite Yang--Mills action is equivalent to a failure of pairwise commutation. -/
theorem action_pos_iff_not_pairwise_commute (A : MatrixConnection ι V) :
    0 < A.action ↔
      ¬ ∀ i j : ι, (A.potential i).comp (A.potential j) =
        (A.potential j).comp (A.potential i) := by
  rw [action_pos_iff_not_flat, flat_iff_pairwise_commute]

/-- Gauge transformation preserves the finite Yang--Mills action in the matrix model. -/
theorem action_gauge_transform (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).action = A.action := by
  dsimp [action]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [curvature_gauge_transform U A i j, norm_conjugate_eq U (A.curvature i j)]

/-- Gauge transformation preserves the coupled finite Yang--Mills action. -/
theorem coupled_action_gauge_transform
    (g : YangMillsCoupling) (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).coupled_action g = A.coupled_action g := by
  simp [coupled_action, action_gauge_transform U A]

/-- Gauge transformation preserves and reflects zero finite Yang--Mills action. -/
theorem action_gauge_transform_eq_zero_iff (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).action = 0 ↔ A.action = 0 := by
  rw [action_gauge_transform U A]

end MatrixConnection

/-- Schwartz test functions on spacetime, used to smear operator-valued fields. -/
@[reducible]
def SchwartzSpace := SchwartzMap Spacetime ℝ

/-- A smeared classical curvature observable `∫ f(x) ‖F_A(x)‖² dx`. -/
noncomputable def classical_curvature_observable
    (G : Type) [CompactSimpleGaugeGroup G] (f : SchwartzSpace) (A : GaugeField G) : ℝ :=
  ∫ x : Spacetime, f x * curvature_norm_sq G A x

/-- Product of the classical curvature observables corresponding to a list of test functions. -/
noncomputable def classical_curvature_correlation
    (G : Type) [CompactSimpleGaugeGroup G] (fs : List SchwartzSpace) (A : GaugeField G) : ℝ :=
  (fs.map fun f => classical_curvature_observable G f A).prod

/-- Bounded linear operators on a real normed space, used as quantum observables. -/
@[reducible]
def LinearOperator (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type :=
  H →L[ℝ] H

/-- Operator-valued distributions: each test function gives a bounded linear operator. -/
@[reducible]
def OperatorValuedDistribution (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type :=
  SchwartzSpace → LinearOperator H

/-- The vacuum is a zero-energy vector for the Hamiltonian. -/
def IsVacuum {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Ω : H) (H₀ : LinearOperator H) : Prop :=
  H₀ Ω = 0

/-- Conjugation action of a unitary operator `U` on an operator `A`: `U A U⁻¹`. -/
noncomputable def conjugate_operator {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (U : H ≃ₗᵢ[ℝ] H) (A : LinearOperator H) : LinearOperator H :=
  (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (A.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- The linear span of vectors obtained by applying smeared fields to the vacuum. -/
def field_generated_submodule {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : OperatorValuedDistribution H) (Ω : H) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range fun f : SchwartzSpace => (Φ f) Ω)

/-- Wightman-style structural properties for a quantum field theory. -/
class WightmanQuantumFieldTheoryProperties (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
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
    ∀ g f, Φ (action_on_tests g f) = conjugate_operator (unitary_rep g) (Φ f)

  -- W2: Spectral condition
  hamiltonian : LinearOperator H
  is_hamiltonian_self_adjoint : IsSelfAdjoint hamiltonian
  is_hamiltonian_positive : hamiltonian.IsPositive

  /--
  The Clay writeup discusses clustering in terms of *spatial translations* generated by momentum
  operators `P⃗`; this is the corresponding unitary representation of spatial translations `ℝ³`.
  -/
  space_translation : Space → (H ≃ₗᵢ[ℝ] H)
  space_translation_zero : space_translation 0 = 1
  space_translation_add :
    ∀ x y : Space, space_translation (x + y) = space_translation x * space_translation y

  /--
  The Clay statement formulates the mass gap as: “`H` has no spectrum in `(0, Δ)`”.

  Here we use Mathlib's Banach-algebra spectrum `spectrum ℝ hamiltonian` of the (bounded) operator
  `hamiltonian`, together with two consequences explicitly referenced in the Clay
  text: non-negativity (positive energy) and vacuum energy `0`.
  -/
  spectrum_nonneg : ∀ E, E ∈ spectrum ℝ hamiltonian → 0 ≤ E
  vacuum_energy_zero : 0 ∈ spectrum ℝ hamiltonian

  -- W3: Existence of vacuum
  vacuum : H
  is_vacuum : IsVacuum vacuum hamiltonian
  vacuum_norm_one : ‖vacuum‖ = 1
  vacuum_invariant : ∀ g, unitary_rep g vacuum = vacuum  -- Vacuum is Poincaré invariant
  vacuum_spatial_invariant : ∀ x : Space, space_translation x vacuum = vacuum
  /--
  Uniqueness of the Poincaré-invariant vacuum, up to a scalar.

  Every Poincaré-invariant zero-energy vector is a real multiple of `vacuum`.  The earlier form
  `‖Ω'‖ = 1 → Ω' = vacuum` was contradictory: `-vacuum` is also a normalized invariant zero-energy
  vector, so it forced `vacuum = 0` and made this structure uninhabited.
  -/
  vacuum_unique :
    ∀ Ω' : H,
      IsVacuum Ω' hamiltonian →
        (∀ g, unitary_rep g Ω' = Ω') →
          ∃ c : ℝ, Ω' = c • vacuum

  -- W4: Cyclicity of the vacuum
  vacuum_cyclic : Dense (field_generated_submodule Φ vacuum : Set H)

  -- W5: Locality/causality
  locality : ∀ (f g : SchwartzMap Spacetime ℝ),
    (∀ (x y : Spacetime),
      f x ≠ 0 → g y ≠ 0 → minkowski_metric (x - y) (x - y) < 0) →
    Φ f ∘L Φ g = Φ g ∘L Φ f  -- Fields commute at spacelike separation

/-!
Extra structure appearing explicitly in the Clay statement (Section 4 of the PDF).

Local gauge-invariant polynomials in the curvature `F` and its covariant derivatives.
-/

/-- A syntactic language for (intended) gauge-invariant local polynomials in curvature and its derivatives. -/
inductive GaugeInvariantLocalPolynomial (G : Type) : Type
  | zero : GaugeInvariantLocalPolynomial G
  | one : GaugeInvariantLocalPolynomial G
  | curvature : GaugeInvariantLocalPolynomial G
  | curvature_component : Fin 4 → Fin 4 → GaugeInvariantLocalPolynomial G
  | cov_deriv : ℕ → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | covariant_derivative : Fin 4 → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | add : GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | mul : GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G
  | trace : GaugeInvariantLocalPolynomial G → GaugeInvariantLocalPolynomial G

/-- The syntactic polynomial language is inhabited by `0`. -/
instance {G : Type} : Inhabited (GaugeInvariantLocalPolynomial G) := ⟨.zero⟩

/--
The Clay example `Tr Fᵢⱼ Fₖₗ(x)`, represented as a local gauge-invariant curvature polynomial.
-/
def trace_curvature_product (G : Type) (i j k l : Fin 4) : GaugeInvariantLocalPolynomial G :=
  .trace (.mul (.curvature_component i j) (.curvature_component k l))

/--
Assignment of local quantum field operators to gauge-invariant local polynomials (Clay statement, §4).

The correspondence is an injective map into operator-valued distributions.
-/
structure LocalOperatorAssignment (G : Type) (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  op : GaugeInvariantLocalPolynomial G → OperatorValuedDistribution H
  injective : Function.Injective op

/-- Vacuum expectation value of an operator. -/
noncomputable def vacuum_expectation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (A : LinearOperator H) : ℝ :=
  inner ℝ Ω (A Ω)

/-- Ordered product of smeared field operators (as a continuous linear operator). -/
noncomputable def smeared_product {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : OperatorValuedDistribution H) : List SchwartzSpace → LinearOperator H
  | [] => ContinuousLinearMap.id ℝ H
  | f :: fs => (Φ f).comp (smeared_product Φ fs)

/-- Wightman-style correlation functional for a list of test functions. -/
noncomputable def correlation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : OperatorValuedDistribution H) (Ω : H) (fs : List SchwartzSpace) : ℝ :=
  vacuum_expectation Ω (smeared_product Φ fs)

/--
A stress-energy tensor with a distributional conservation law.

The Clay statement mentions the existence of a stress tensor among the expected short-distance
structures; here this is a symmetry condition and a conservation identity in terms of a chosen
“partial derivative” operator on test functions.
-/
structure StressEnergyTensor (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- A chosen derivative operator on test functions, representing `∂_μ`. -/
  test_deriv : Fin 4 → SchwartzSpace → SchwartzSpace
  /-- Components `T_{μν}` as operator-valued distributions. -/
  T : Fin 4 → Fin 4 → OperatorValuedDistribution H
  /-- Symmetry `T_{μν} = T_{νμ}`. -/
  symmetric : ∀ μ ν, T μ ν = T ν μ
  /-- Conservation `∑_μ T_{μν}(∂_μ f) = 0` (as an operator) for all `ν` and test functions `f`. -/
  conserved : ∀ ν f, (Finset.univ.sum fun μ : Fin 4 => T μ ν (test_deriv μ f)) = 0

/--
Osterwalder--Schrader-strength Euclidean data.

This records the Euclidean Green/Schwinger-function side of the Clay Wightman and
Osterwalder--Schrader axiom requirements.  The analytic axioms are explicit fields of the quantum
Yang--Mills package.
-/
structure OsterwalderSchraderStrength
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : OperatorValuedDistribution H) (Ω : H) where
  /-- Euclidean Schwinger functions indexed by lists of test functions. -/
  schwinger_function : List SchwartzSpace → ℝ
  /-- Time reflection on Euclidean test functions. -/
  time_reflection : SchwartzSpace → SchwartzSpace
  /-- Euclidean motions acting on test functions. -/
  euclidean_action : Spacetime → SchwartzSpace → SchwartzSpace
  /-- Euclidean invariance of the Schwinger functions under translations. -/
  euclidean_invariance :
    ∀ a fs, schwinger_function (fs.map (euclidean_action a)) = schwinger_function fs
  /-- Reflection positivity in the Osterwalder--Schrader sense. -/
  reflection_positivity :
    ∀ fs : List SchwartzSpace, 0 ≤ schwinger_function (fs.map time_reflection ++ fs)
  /-- Symmetry of Euclidean correlation functions under reversal. -/
  symmetry : ∀ fs : List SchwartzSpace, schwinger_function fs.reverse = schwinger_function fs
  /-- OS reconstruction agrees with the Wightman correlation functions used by `Φ` and `Ω`. -/
  reconstruction_agrees : ∀ fs : List SchwartzSpace, schwinger_function fs = correlation Φ Ω fs

/--
A quantum Yang--Mills theory for a compact simple gauge group.

The structure bundles the Hilbert space, operator-valued fields, Wightman-style properties, local
operator assignment, Osterwalder--Schrader-strength Euclidean data, a constructive link to the
classical Yang--Mills action, and a stress tensor.
-/
structure QuantumYangMillsTheory (G : Type) [CompactSimpleGaugeGroup G] where
  hilbert_space : Type  -- Physical state space
  [normed_add_comm_group : NormedAddCommGroup hilbert_space]
  [inner_product_space : InnerProductSpace ℝ hilbert_space]
  [complete_space : CompleteSpace hilbert_space]
  field_operators : OperatorValuedDistribution hilbert_space  -- Quantum fields
  wightman : WightmanQuantumFieldTheoryProperties hilbert_space field_operators
  local_operators : LocalOperatorAssignment G hilbert_space
  osterwalder_schrader : OsterwalderSchraderStrength field_operators wightman.vacuum

  /-- Positive coupling constant in the classical Yang--Mills action being quantized. -/
  coupling : YangMillsCoupling
  /-- Measurable structure on classical gauge fields used by the Euclidean construction. -/
  [gauge_field_measurable : MeasurableSpace (GaugeField G)]
  /-- Constructive Euclidean measure on classical gauge fields. -/
  euclidean_gauge_measure : Measure (GaugeField G)
  /-- The Yang--Mills Boltzmann weight has a finite, strictly positive partition function. -/
  partition_function_pos :
    0 < ∫ A : GaugeField G,
      Real.exp (-coupled_yang_mills_action G coupling A) ∂euclidean_gauge_measure
  /--
  The Euclidean Schwinger functions are normalized expectations with Boltzmann weight
  `exp (-S_YM(A))`. This ties the quantum theory to the classical Yang--Mills dynamics rather than
  permitting an arbitrary massive quantum field theory.
  -/
  schwinger_from_yang_mills_action :
    ∀ fs : List SchwartzSpace,
      osterwalder_schrader.schwinger_function fs =
        (∫ A : GaugeField G,
            Real.exp (-coupled_yang_mills_action G coupling A) *
              classical_curvature_correlation G fs A
              ∂euclidean_gauge_measure) /
          (∫ A : GaugeField G,
            Real.exp (-coupled_yang_mills_action G coupling A) ∂euclidean_gauge_measure)
  stress_tensor : StressEnergyTensor hilbert_space
  /--
  The curvature field content is non-trivial: some smearing of the local curvature operator is not
  the zero operator.
  -/
  curvature_local_operator_nonzero :
    ∃ f : SchwartzSpace,
      local_operators.op (GaugeInvariantLocalPolynomial.curvature : GaugeInvariantLocalPolynomial G)
        f ≠ 0

  /--
  The local operator assignment is compatible with Poincaré covariance (Clay statement, §4).
  -/
  local_operators_covariant :
    ∀ g p f,
      (local_operators.op p) (wightman.action_on_tests g f) =
        conjugate_operator (wightman.unitary_rep g) ((local_operators.op p) f)

  /--
  The assigned local operators satisfy locality/causality in the same smeared sense as in the
  Wightman-style properties.
  -/
  local_operators_locality :
    ∀ (p q : GaugeInvariantLocalPolynomial G) (f g : SchwartzMap Spacetime ℝ),
      (∀ (x y : Spacetime),
        f x ≠ 0 → g y ≠ 0 → minkowski_metric (x - y) (x - y) < 0) →
      (local_operators.op p f) ∘L (local_operators.op q g) =
        (local_operators.op q g) ∘L (local_operators.op p f)

attribute [instance] QuantumYangMillsTheory.normed_add_comm_group
attribute [instance] QuantumYangMillsTheory.inner_product_space
attribute [instance] QuantumYangMillsTheory.complete_space

/-! Helper definitions for writing statements close to the Clay text. -/

/-- A “local operator at a spatial point” obtained by conjugating by spatial translation. -/
noncomputable def local_operator_at {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (U : Space → (H ≃ₗᵢ[ℝ] H)) (x : Space) (O : LinearOperator H) : LinearOperator H :=
  conjugate_operator (U x) O

/-- “Centered” operator: its vacuum expectation value vanishes. -/
def IsCentered {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (O : LinearOperator H) : Prop :=
  vacuum_expectation Ω O = 0

/-- A “two-point function” on test functions, defined as a vacuum expectation of a product. -/
noncomputable def two_point_function (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) (f g : SchwartzSpace) : ℝ :=
  correlation theory.field_operators theory.wightman.vacuum [f, g]

/--
The local quantum field corresponding to the Clay example `Tr Fᵢⱼ Fₖₗ(x)`.
-/
noncomputable def trace_curvature_product_operator (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) (i j k l : Fin 4) :
    OperatorValuedDistribution theory.hilbert_space :=
  theory.local_operators.op (trace_curvature_product G i j k l)

end MillenniumYangMillsDefs
