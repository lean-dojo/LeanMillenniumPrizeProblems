import Problems.YangMills.Quantum

namespace MillenniumYangMills

open LieGroup MillenniumYangMillsDefs

/-!
# Yang-Mills Existence and Mass Gap Problem

Lean statement of the Clay Millennium problem “Yang–Mills existence and mass gap”.

For each compact simple gauge group `G`, the problem asks for a non-trivial quantum Yang–Mills
theory on `ℝ⁴` with a Hamiltonian spectral gap `Δ > 0` and finite Clay mass.

The statement below keeps the constructive quantum-field-theory ingredients explicit: Wightman and
Osterwalder--Schrader style axioms, gauge-invariant local curvature operators, physical
Hamiltonian spectral data, and a positive finite mass gap.  Companion modules connect this formulation
to unbounded self-adjoint Hamiltonians and Lorentz covariance.

The file also proves finite-dimensional matrix Yang--Mills theorems: curvature antisymmetry,
the Bianchi identity, gauge covariance, gauge invariance of the action, and the equivalence
between zero action and flatness.

## References
- Jaffe, A., & Witten, E. "Quantum Yang-Mills Theory"
- Streater & Wightman (1964): "PCT, Spin and Statistics, and All That"
- Osterwalder & Schrader (1973, 1975): Euclidean Green's function framework
-/

/-- Clay's four-dimensional spacetime `ℝ⁴`/`ℝ⁴`, represented by the local spacetime model. -/
@[reducible]
def ClayFourDimensionalSpacetime : Type :=
  Spacetime

/--
Clay's phrase “quantum Yang--Mills theory on `ℝ⁴`” for a compact simple gauge group.

The underlying theory already uses `ClayFourDimensionalSpacetime` through the test-function and local-operator
structures in `Problems.YangMills.Quantum`.
-/
@[reducible]
def ClayQuantumYangMillsTheoryOnFourDimensionalSpacetime (G : Type) [CompactSimpleGaugeGroup G] : Type 1 :=
  QuantumYangMillsTheory G

/--
For the matrix-connection model defined in `Problems.YangMills.Quantum`, the action
`Σᵢⱼ ‖Fᵢⱼ‖²` is genuinely constructed from the curvature commutators and is always nonnegative.
-/
theorem MatrixYangMills.action_nonneg
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    0 ≤ A.action :=
  MatrixConnection.action_nonneg A

/-- The classical coupling constant `g > 0` used in the Yang--Mills action. -/
@[reducible]
def ClayYangMillsCoupling : Type :=
  YangMillsCoupling

/-- The coupled classical Yang--Mills action factor `1 / (4 g^2)` is positive. -/
theorem ClayYangMillsCoupling.action_scale_positive (g : ClayYangMillsCoupling) :
    0 < g.action_scale :=
  g.action_scale_pos

/-- Finite matrix Yang--Mills action with explicit positive coupling. -/
noncomputable def MatrixYangMills.coupled_action
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ClayYangMillsCoupling) (A : MatrixConnection ι V) : ℝ :=
  A.coupled_action g

/-- The finite coupled Yang--Mills action is nonnegative. -/
theorem MatrixYangMills.coupled_action_nonneg
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ClayYangMillsCoupling) (A : MatrixConnection ι V) :
    0 ≤ MatrixYangMills.coupled_action g A :=
  MatrixConnection.coupled_action_nonneg g A

/-- The zero matrix connection has zero curvature. -/
theorem MatrixYangMills.zero_curvature
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (i j : ι) :
    (MatrixConnection.zero : MatrixConnection ι V).curvature i j = 0 :=
  MatrixConnection.curvature_zero i j

/-- Scalar-multiple matrix connections have zero curvature. -/
theorem MatrixYangMills.curvature_scalar_multiple
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (weight : ι → ℝ) (T : V →L[ℝ] V) (i j : ι) :
    (MatrixConnection.scalar_multiple weight T).curvature i j = 0 :=
  MatrixConnection.curvature_scalar_multiple weight T i j

/-- Scaling a matrix connection scales curvature quadratically. -/
theorem MatrixYangMills.curvature_scale
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ℝ) (A : MatrixConnection ι V) (i j : ι) :
    (A.scale c).curvature i j = (c * c) • A.curvature i j :=
  MatrixConnection.curvature_scale c A i j

/-- Curvature expansion for a sum of finite-matrix connections. -/
theorem MatrixYangMills.curvature_add
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : MatrixConnection ι V) (i j : ι) :
    (MatrixConnection.add A B).curvature i j =
      A.curvature i j + B.curvature i j + MatrixConnection.mixed_curvature A B i j :=
  MatrixConnection.curvature_add A B i j

/-- The mixed curvature term is symmetric in the two matrix connections. -/
theorem MatrixYangMills.mixed_curvature_comm
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : MatrixConnection ι V) (i j : ι) :
    MatrixConnection.mixed_curvature B A i j =
      MatrixConnection.mixed_curvature A B i j :=
  MatrixConnection.mixed_curvature_comm A B i j

/-- The mixed curvature term is antisymmetric in the two directions. -/
theorem MatrixYangMills.mixed_curvature_swap
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : MatrixConnection ι V) (i j : ι) :
    MatrixConnection.mixed_curvature A B j i =
      -MatrixConnection.mixed_curvature A B i j :=
  MatrixConnection.mixed_curvature_swap A B i j

/--
If every component of one matrix connection commutes with every component of another, the mixed
curvature term vanishes.
-/
theorem MatrixYangMills.mixed_curvature_zero_of_cross_commute
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : MatrixConnection ι V}
    (hcomm : ∀ i j : ι, (A.potential i).comp (B.potential j) =
      (B.potential j).comp (A.potential i)) (i j : ι) :
    MatrixConnection.mixed_curvature A B i j = 0 :=
  MatrixConnection.mixed_curvature_zero_of_cross_commute hcomm i j

/-- Additive curvature formula under a vanishing mixed-curvature hypothesis. -/
theorem MatrixYangMills.curvature_add_of_mixed_zero
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : MatrixConnection ι V}
    (hmix : ∀ i j : ι, MatrixConnection.mixed_curvature A B i j = 0) (i j : ι) :
    (MatrixConnection.add A B).curvature i j = A.curvature i j + B.curvature i j :=
  MatrixConnection.curvature_add_of_mixed_zero hmix i j

/-- Flatness is closed under sums when the mixed-curvature obstruction is zero. -/
theorem MatrixYangMills.add_flat_of_mixed_zero
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : MatrixConnection ι V} (hA : A.IsFlat) (hB : B.IsFlat)
    (hmix : ∀ i j : ι, MatrixConnection.mixed_curvature A B i j = 0) :
    (MatrixConnection.add A B).IsFlat :=
  MatrixConnection.add_flat_of_mixed_zero hA hB hmix

/--
The sum of two flat matrix connections is flat when all components commute across the two
connections.
-/
theorem MatrixYangMills.add_flat_of_cross_commute
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : MatrixConnection ι V} (hA : A.IsFlat) (hB : B.IsFlat)
    (hcomm : ∀ i j : ι, (A.potential i).comp (B.potential j) =
      (B.potential j).comp (A.potential i)) :
    (MatrixConnection.add A B).IsFlat :=
  MatrixConnection.add_flat_of_cross_commute hA hB hcomm

/-- Negating a matrix connection leaves curvature unchanged. -/
theorem MatrixYangMills.curvature_neg
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) (i j : ι) :
    A.neg.curvature i j = A.curvature i j :=
  MatrixConnection.curvature_neg A i j

/-- Scaling by `0` gives the zero matrix connection. -/
theorem MatrixYangMills.scale_zero
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.scale 0 = MatrixConnection.zero :=
  MatrixConnection.scale_zero A

/-- Scaling by `1` leaves a matrix connection unchanged. -/
theorem MatrixYangMills.scale_one
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.scale 1 = A :=
  MatrixConnection.scale_one A

/-- Successive scalings multiply their scale factors. -/
theorem MatrixYangMills.scale_scale
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c d : ℝ) (A : MatrixConnection ι V) :
    (A.scale c).scale d = A.scale (d * c) :=
  MatrixConnection.scale_scale c d A

/-- Negating a matrix connection is scaling by `-1`. -/
theorem MatrixYangMills.neg_eq_scale
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.neg = A.scale (-1) :=
  MatrixConnection.neg_eq_scale A

/-- Right identity law for the zero matrix connection, exposed with the finite Yang--Mills prefix. -/
theorem MatrixYangMills.add_zero
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    MatrixConnection.add A MatrixConnection.zero = A :=
  MatrixConnection.add_zero A

/-- Left identity law for the zero matrix connection, exposed with the finite Yang--Mills prefix. -/
theorem MatrixYangMills.zero_add
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    MatrixConnection.add MatrixConnection.zero A = A :=
  MatrixConnection.zero_add A

/-- Pointwise addition of matrix connections is commutative. -/
theorem MatrixYangMills.add_comm
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : MatrixConnection ι V) :
    MatrixConnection.add A B = MatrixConnection.add B A :=
  MatrixConnection.add_comm A B

/-- Pointwise addition of matrix connections is associative. -/
theorem MatrixYangMills.add_assoc
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B C : MatrixConnection ι V) :
    MatrixConnection.add (MatrixConnection.add A B) C =
      MatrixConnection.add A (MatrixConnection.add B C) :=
  MatrixConnection.add_assoc A B C

/-- Scaling distributes over pointwise addition of matrix connections. -/
theorem MatrixYangMills.scale_add
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ℝ) (A B : MatrixConnection ι V) :
    (MatrixConnection.add A B).scale c =
      MatrixConnection.add (A.scale c) (B.scale c) :=
  MatrixConnection.scale_add c A B

/-- Scaling is additive in the scalar variable. -/
theorem MatrixYangMills.scale_add_scalar
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c d : ℝ) (A : MatrixConnection ι V) :
    A.scale (c + d) = MatrixConnection.add (A.scale c) (A.scale d) :=
  MatrixConnection.scale_add_scalar c d A

/-- Adding a matrix connection to its negation gives the zero connection. -/
theorem MatrixYangMills.add_neg
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    MatrixConnection.add A A.neg = MatrixConnection.zero :=
  MatrixConnection.add_neg A

/-- Adding the negation of a matrix connection to it gives the zero connection. -/
theorem MatrixYangMills.neg_add
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    MatrixConnection.add A.neg A = MatrixConnection.zero :=
  MatrixConnection.neg_add A

/-- Double negation leaves a matrix connection unchanged. -/
theorem MatrixYangMills.neg_neg
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.neg.neg = A :=
  MatrixConnection.neg_neg A

/-- The zero matrix connection has zero covariant commutator. -/
theorem MatrixYangMills.covariant_commutator_zero
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : ι) (T : V →L[ℝ] V) :
    (MatrixConnection.zero : MatrixConnection ι V).covariant_commutator i T = 0 :=
  MatrixConnection.covariant_commutator_zero i T

/-- The zero matrix connection is flat. -/
theorem MatrixYangMills.zero_flat
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (MatrixConnection.zero : MatrixConnection ι V).IsFlat :=
  MatrixConnection.zero_flat

/-- Scalar-multiple matrix connections are flat. -/
theorem MatrixYangMills.scalar_multiple_flat
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (weight : ι → ℝ) (T : V →L[ℝ] V) :
    (MatrixConnection.scalar_multiple weight T).IsFlat :=
  MatrixConnection.scalar_multiple_flat weight T

/-- Scaling preserves flatness of matrix connections. -/
theorem MatrixYangMills.scale_flat
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {c : ℝ} {A : MatrixConnection ι V} (hflat : A.IsFlat) :
    (A.scale c).IsFlat :=
  MatrixConnection.scale_flat hflat

/-- Negation preserves flatness of matrix connections. -/
theorem MatrixYangMills.neg_flat
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : MatrixConnection ι V} (hflat : A.IsFlat) :
    A.neg.IsFlat :=
  MatrixConnection.neg_flat hflat

/-- Nonzero scaling preserves and reflects flatness of matrix connections. -/
theorem MatrixYangMills.scale_flat_iff
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {c : ℝ} (hc : c ≠ 0) (A : MatrixConnection ι V) :
    (A.scale c).IsFlat ↔ A.IsFlat :=
  MatrixConnection.scale_flat_iff hc A

/-- Negation preserves and reflects flatness of matrix connections. -/
theorem MatrixYangMills.neg_flat_iff
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.neg.IsFlat ↔ A.IsFlat :=
  MatrixConnection.neg_flat_iff A

/-- The components of a scalar-multiple matrix connection commute pairwise. -/
theorem MatrixYangMills.scalar_multiple_pairwise_commute
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (weight : ι → ℝ) (T : V →L[ℝ] V) :
    ∀ i j : ι, ((MatrixConnection.scalar_multiple weight T).potential i).comp
        ((MatrixConnection.scalar_multiple weight T).potential j) =
      ((MatrixConnection.scalar_multiple weight T).potential j).comp
        ((MatrixConnection.scalar_multiple weight T).potential i) :=
  MatrixConnection.scalar_multiple_pairwise_commute weight T

/-- The zero matrix connection has zero Yang--Mills action. -/
theorem MatrixYangMills.zero_action
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (MatrixConnection.zero : MatrixConnection ι V).action = 0 :=
  MatrixConnection.action_zero

/-- Scalar-multiple matrix connections have zero Yang--Mills action. -/
theorem MatrixYangMills.action_scalar_multiple
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (weight : ι → ℝ) (T : V →L[ℝ] V) :
    (MatrixConnection.scalar_multiple weight T).action = 0 :=
  MatrixConnection.action_scalar_multiple weight T

/-- Gauge transformations fix the zero matrix connection. -/
theorem MatrixYangMills.gauge_transform_zero
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) :
    (MatrixConnection.zero : MatrixConnection ι V).gauge_transform U = MatrixConnection.zero :=
  MatrixConnection.gauge_transform_zero U

/--
Gauge transformations preserve the scalar-multiple connection family, conjugating the fixed
operator.
-/
theorem MatrixYangMills.gauge_transform_scalar_multiple
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (weight : ι → ℝ) (T : V →L[ℝ] V) :
    (MatrixConnection.scalar_multiple weight T).gauge_transform U =
      MatrixConnection.scalar_multiple weight (MatrixConnection.conjugate_by_gauge U T) :=
  MatrixConnection.gauge_transform_scalar_multiple U weight T

/-- Gauge transformation distributes over pointwise addition of matrix connections. -/
theorem MatrixYangMills.gauge_transform_add
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A B : MatrixConnection ι V) :
    (MatrixConnection.add A B).gauge_transform U =
      MatrixConnection.add (A.gauge_transform U) (B.gauge_transform U) :=
  MatrixConnection.gauge_transform_add U A B

/-- Gauge transformation commutes with scaling a matrix connection. -/
theorem MatrixYangMills.gauge_transform_scale
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (c : ℝ) (A : MatrixConnection ι V) :
    (A.scale c).gauge_transform U = (A.gauge_transform U).scale c :=
  MatrixConnection.gauge_transform_scale U c A

/--
In the matrix-connection model, zero Yang--Mills action is equivalent to vanishing curvature.
-/
theorem MatrixYangMills.action_eq_zero_iff_flat
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.action = 0 ↔ A.IsFlat :=
  MatrixConnection.action_eq_zero_iff_flat A

/-- Zero coupled finite Yang--Mills action is equivalent to vanishing curvature. -/
theorem MatrixYangMills.coupled_action_eq_zero_iff_flat
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ClayYangMillsCoupling) (A : MatrixConnection ι V) :
    MatrixYangMills.coupled_action g A = 0 ↔ A.IsFlat :=
  MatrixConnection.coupled_action_eq_zero_iff_flat g A

/-- Nonzero scaling preserves and reflects zero Yang--Mills action. -/
theorem MatrixYangMills.action_scale_eq_zero_iff
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {c : ℝ} (hc : c ≠ 0) (A : MatrixConnection ι V) :
    (A.scale c).action = 0 ↔ A.action = 0 :=
  MatrixConnection.action_scale_eq_zero_iff hc A

/-- Negation preserves and reflects zero Yang--Mills action. -/
theorem MatrixYangMills.action_neg_eq_zero_iff
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.neg.action = 0 ↔ A.action = 0 :=
  MatrixConnection.action_neg_eq_zero_iff A

/-- Flat matrix connections have zero Yang--Mills action. -/
theorem MatrixYangMills.flat_action_zero
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) (hflat : A.IsFlat) :
    A.action = 0 :=
  MatrixConnection.flat_action_zero A hflat

/--
Finite-matrix Yang--Mills corollary: cross-commuting flat connections add to a zero-action
connection.
-/
theorem MatrixYangMills.action_add_zero_of_cross_commute
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : MatrixConnection ι V} (hA : A.IsFlat) (hB : B.IsFlat)
    (hcomm : ∀ i j : ι, (A.potential i).comp (B.potential j) =
      (B.potential j).comp (A.potential i)) :
    (MatrixConnection.add A B).action = 0 :=
  MatrixConnection.action_add_zero_of_cross_commute hA hB hcomm

/-- Zero Yang--Mills action forces a matrix connection to be flat. -/
theorem MatrixYangMills.flat_of_zero_action
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) (hA : A.action = 0) :
    A.IsFlat :=
  MatrixConnection.flat_of_zero_action A hA

/-- In the finite matrix model, curvature transforms by conjugation under gauge transformations. -/
theorem MatrixYangMills.curvature_gauge_transform
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) (i j : ι) :
    (A.gauge_transform U).curvature i j =
      (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((A.curvature i j).comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap)) :=
  MatrixConnection.curvature_gauge_transform U A i j

/-- In the finite matrix model, curvature is antisymmetric in its two directions. -/
theorem MatrixYangMills.curvature_swap
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) (i j : ι) :
    A.curvature j i = -A.curvature i j :=
  MatrixConnection.curvature_swap A i j

/-- In the finite matrix model, flatness is pairwise commutation of connection components. -/
theorem MatrixYangMills.flat_iff_pairwise_commute
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.IsFlat ↔
      ∀ i j : ι, (A.potential i).comp (A.potential j) =
        (A.potential j).comp (A.potential i) :=
  MatrixConnection.flat_iff_pairwise_commute A

/-- Zero action is equivalent to pairwise commutation of connection components. -/
theorem MatrixYangMills.action_eq_zero_iff_pairwise_commute
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.action = 0 ↔
      ∀ i j : ι, (A.potential i).comp (A.potential j) =
        (A.potential j).comp (A.potential i) :=
  MatrixConnection.action_eq_zero_iff_pairwise_commute A

/-- In the finite matrix model, positive Yang--Mills action is equivalent to non-flatness. -/
theorem MatrixYangMills.action_pos_iff_not_flat
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    0 < A.action ↔ ¬ A.IsFlat :=
  MatrixConnection.action_pos_iff_not_flat A

/-- In the finite matrix model, positive Yang--Mills action detects nonzero curvature. -/
theorem MatrixYangMills.action_pos_iff_exists_curvature_ne_zero
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    0 < A.action ↔ ∃ i j : ι, A.curvature i j ≠ 0 :=
  MatrixConnection.action_pos_iff_exists_curvature_ne_zero A

/--
In the finite matrix model, positive Yang--Mills action is equivalent to a failure of pairwise
commutation among connection components.
-/
theorem MatrixYangMills.action_pos_iff_not_pairwise_commute
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    0 < A.action ↔
      ¬ ∀ i j : ι, (A.potential i).comp (A.potential j) =
        (A.potential j).comp (A.potential i) :=
  MatrixConnection.action_pos_iff_not_pairwise_commute A

/--
In the finite matrix model, curvature satisfies the algebraic Bianchi identity
`[Aᵢ,Fⱼₖ] + [Aⱼ,Fₖᵢ] + [Aₖ,Fᵢⱼ] = 0`.
-/
theorem MatrixYangMills.bianchi_identity
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) (i j k : ι) :
    A.covariant_commutator i (A.curvature j k) +
      A.covariant_commutator j (A.curvature k i) +
      A.covariant_commutator k (A.curvature i j) = 0 :=
  MatrixConnection.bianchi_identity A i j k

/--
In the finite matrix model, the covariant commutator is gauge-covariant:
`[U Aᵢ U⁻¹, U T U⁻¹] = U [Aᵢ,T] U⁻¹`.
-/
theorem MatrixYangMills.covariant_commutator_gauge_transform
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) (i : ι) (T : V →L[ℝ] V) :
    (A.gauge_transform U).covariant_commutator i
        ((U.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (T.comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap))) =
      (U.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((A.covariant_commutator i T).comp
          (U.symm.toContinuousLinearEquiv.toContinuousLinearMap)) :=
  MatrixConnection.covariant_commutator_gauge_transform U A i T

/-- In the finite matrix model, gauge transformation preserves the Yang--Mills action. -/
theorem MatrixYangMills.action_gauge_transform
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).action = A.action :=
  MatrixConnection.action_gauge_transform U A

/-- Gauge transformation preserves the finite coupled Yang--Mills action. -/
theorem MatrixYangMills.coupled_action_gauge_transform
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ClayYangMillsCoupling) (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    MatrixYangMills.coupled_action g (A.gauge_transform U) =
      MatrixYangMills.coupled_action g A :=
  MatrixConnection.coupled_action_gauge_transform g U A

/-- Gauge transformation preserves flatness in the finite matrix model. -/
theorem MatrixYangMills.gauge_transform_flat
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) {A : MatrixConnection ι V} (hflat : A.IsFlat) :
    (A.gauge_transform U).IsFlat :=
  MatrixConnection.gauge_transform_flat (U := U) hflat

/-- Gauge transformation preserves and reflects flatness in the finite matrix model. -/
theorem MatrixYangMills.gauge_transform_flat_iff
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).IsFlat ↔ A.IsFlat :=
  MatrixConnection.gauge_transform_flat_iff U A

/-- Gauge transformation preserves and reflects zero Yang--Mills action. -/
theorem MatrixYangMills.action_gauge_transform_eq_zero_iff
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).action = 0 ↔ A.action = 0 :=
  MatrixConnection.action_gauge_transform_eq_zero_iff U A

/-- In the finite matrix model, the identity gauge transformation leaves a connection unchanged. -/
theorem MatrixYangMills.gauge_transform_refl
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : MatrixConnection ι V) :
    A.gauge_transform (LinearIsometryEquiv.refl ℝ V) = A :=
  MatrixConnection.gauge_transform_refl A

/-- In the finite matrix model, gauge transformations compose as conjugations. -/
theorem MatrixYangMills.gauge_transform_trans
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U V' : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).gauge_transform V' = A.gauge_transform (U.trans V') :=
  MatrixConnection.gauge_transform_trans U V' A

/-- In the finite matrix model, applying a gauge transformation and its inverse returns the connection. -/
theorem MatrixYangMills.gauge_transform_symm
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : V ≃ₗᵢ[ℝ] V) (A : MatrixConnection ι V) :
    (A.gauge_transform U).gauge_transform U.symm = A :=
  MatrixConnection.gauge_transform_symm U A

/-- A non-trivial theory: the Hilbert space has at least two distinct states. -/
def NontrivialTheory {G : Type} [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G) : Prop :=
  Nontrivial theory.hilbert_space

/--
Bounded-spectrum comparison predicate: the locally modeled Wightman Hamiltonian has no
spectrum in `(0, Δ)`.

This is useful for Mathlib-native spectral lemmas, but it is not the PDF statement's spectral
package.  The Clay PDF statement below uses `ClayHamiltonianSpectralData`, while
`Problems.YangMills.HamiltonianSpectrum` supplies the unbounded self-adjoint physical-Hamiltonian
formulation.
-/
def HasMassGapSpectrum (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ Disjoint (spectrum ℝ theory.wightman.hamiltonian) (Set.Ioo 0 Δ)

/--
Bounded-operator spectral data for the Mathlib-native comparison model.

The Clay Hamiltonian is physically an unbounded self-adjoint generator.  The current Lean model
uses a bounded operator because that is the available local API, so this structure is explicitly a
comparison datum: it packages Mathlib's bounded-operator spectrum and records where that
approximation agrees with the spectral set used by this bounded-spectrum formulation.
-/
structure HamiltonianSpectralData (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) where
  /-- The spectral set of the Hamiltonian. -/
  spectrum_set : Set ℝ
  /-- Agreement with Mathlib's spectrum for the bounded Hamiltonian. -/
  spectrum_eq : spectrum_set = spectrum ℝ theory.wightman.hamiltonian
  /-- Positive-energy condition. -/
  positive_energy : ∀ E : ℝ, E ∈ spectrum_set → 0 ≤ E
  /-- Vacuum energy is `0`. -/
  vacuum_energy_zero : 0 ∈ spectrum_set

/-- Mathlib-spectrum data induced by the Wightman-style properties of a Yang--Mills theory. -/
def HamiltonianSpectralData.of_quantum_theory (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) : HamiltonianSpectralData G theory :=
  { spectrum_set := spectrum ℝ theory.wightman.hamiltonian
    spectrum_eq := rfl
    positive_energy := theory.wightman.spectrum_nonneg
    vacuum_energy_zero := theory.wightman.vacuum_energy_zero }

/--
Hamiltonian spectral data used for the Clay PDF statement.

This is the primary spectral package for the Millennium statement in this file.  It does **not**
identify the physical Hamiltonian spectrum with Mathlib's bounded-operator spectrum.  Instead it
records the spectral set, positive energy, zero vacuum energy, and the Wightman Hamiltonian facts
used in the current formalization.
-/
structure ClayHamiltonianSpectralData (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) where
  /-- The spectral set of the physical Hamiltonian in the Clay statement. -/
  spectrum_set : Set ℝ
  /-- Positive-energy condition for the physical spectrum. -/
  positive_energy : ∀ E : ℝ, E ∈ spectrum_set → 0 ≤ E
  /-- The vacuum energy `0` belongs to the physical spectrum. -/
  vacuum_energy_zero : 0 ∈ spectrum_set
  /-- The Wightman Hamiltonian has the vacuum as a zero-energy vector. -/
  vacuum_zero_energy : IsVacuum theory.wightman.vacuum theory.wightman.hamiltonian
  /-- The Wightman Hamiltonian in the bounded-operator model is self-adjoint. -/
  wightman_hamiltonian_self_adjoint : IsSelfAdjoint theory.wightman.hamiltonian
  /-- The Wightman Hamiltonian in the bounded-operator model is positive. -/
  wightman_hamiltonian_positive : theory.wightman.hamiltonian.IsPositive

/--
The Hamiltonian spectral package determines the spectral datum used in the Clay statement.
-/
def HamiltonianSpectralData.spectral_data {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : HamiltonianSpectralData G theory) :
    ClayHamiltonianSpectralData G theory :=
  { spectrum_set := spectralData.spectrum_set
    positive_energy := spectralData.positive_energy
    vacuum_energy_zero := spectralData.vacuum_energy_zero
    vacuum_zero_energy := theory.wightman.is_vacuum
    wightman_hamiltonian_self_adjoint := theory.wightman.is_hamiltonian_self_adjoint
    wightman_hamiltonian_positive := theory.wightman.is_hamiltonian_positive }

/-- Mass gap stated using explicit Hamiltonian spectral data. -/
def HasMassGapSpectralData {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : HamiltonianSpectralData G theory) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ Disjoint spectralData.spectrum_set (Set.Ioo 0 Δ)

/-- Mass gap stated using the PDF Hamiltonian spectral data. -/
def HasClayMassGap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) (Δ : ℝ) :
    Prop :=
  Δ > 0 ∧ Disjoint spectralData.spectrum_set (Set.Ioo 0 Δ)

/-- Clay PDF positive-energy sentence: the Hamiltonian spectrum is contained in `[0, ∞)`. -/
def ClayEnergySpectrumNonnegative {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) : Prop :=
  ∀ E : ℝ, E ∈ spectralData.spectrum_set → 0 ≤ E

/-- Clay PDF vacuum sentence `HΩ = 0` for the Wightman Hamiltonian. -/
def ClayVacuumZeroEnergy {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (_spec : ClayHamiltonianSpectralData G theory) : Prop :=
  IsVacuum theory.wightman.vacuum theory.wightman.hamiltonian

/-- The vacuum energy `0` belongs to the physical spectrum. -/
def ClayVacuumEnergyInSpectrum {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) : Prop :=
  0 ∈ spectralData.spectrum_set

/-- Clay PDF spectral-gap sentence: the Hamiltonian has no spectrum in `(0, Δ)`. -/
def ClayNoSpectrumInGap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) (Δ : ℝ) :
    Prop :=
  Disjoint spectralData.spectrum_set (Set.Ioo 0 Δ)

/--
Bundled Clay PDF Hamiltonian spectral conditions: zero vacuum energy, positive spectrum, vacuum
energy in the spectrum, a positive gap, and no physical spectrum in `(0, Δ)`.
-/
def ClayHamiltonianGapConditions {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) (Δ : ℝ) :
    Prop :=
  ClayVacuumZeroEnergy spectralData ∧
    ClayEnergySpectrumNonnegative spectralData ∧
    ClayVacuumEnergyInSpectrum spectralData ∧
    Δ > 0 ∧ ClayNoSpectrumInGap spectralData Δ

/-- The PDF spectral data directly supplies the positive-energy spectrum sentence. -/
theorem ClayHamiltonianSpectralData.spectrum_nonnegative
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) :
    ClayEnergySpectrumNonnegative spectralData :=
  spectralData.positive_energy

/-- The PDF spectral data directly supplies the PDF's `HΩ = 0` sentence. -/
theorem ClayHamiltonianSpectralData.has_vacuum_zero_energy
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) :
    ClayVacuumZeroEnergy spectralData :=
  spectralData.vacuum_zero_energy

/-- The PDF spectral data records that the vacuum energy `0` lies in the physical spectrum. -/
theorem ClayHamiltonianSpectralData.vacuum_in_spectrum
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) :
    ClayVacuumEnergyInSpectrum spectralData :=
  spectralData.vacuum_energy_zero

/--
Vacuum-isolated form of the Clay mass gap: the vacuum energy `0` belongs to the physical
spectrum, and every nonzero physical spectral value is at least `Δ`.
-/
def ClayVacuumSpectralGap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) (Δ : ℝ) :
    Prop :=
  Δ > 0 ∧ 0 ∈ spectralData.spectrum_set ∧
    ∀ E : ℝ, E ∈ spectralData.spectrum_set → E ≠ 0 → Δ ≤ E

/--
Clay mass-gap wording in excitation-energy form: every excitation of the vacuum has energy at least
`Δ`.

The vacuum energy `0` is already part of `ClayHamiltonianSpectralData`; the nonzero spectral values
are the excitations.
-/
def ClayExcitationGap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) (Δ : ℝ) :
    Prop :=
  Δ > 0 ∧ ∀ E : ℝ, E ∈ spectralData.spectrum_set → E ≠ 0 → Δ ≤ E

/--
Vacuum-isolated form of a spectral mass gap: the vacuum energy `0` belongs to the spectrum, and
every nonzero spectral value is at least `Δ`.
-/
def VacuumSpectralGap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : HamiltonianSpectralData G theory) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ 0 ∈ spectralData.spectrum_set ∧
    ∀ E : ℝ, E ∈ spectralData.spectrum_set → E ≠ 0 → Δ ≤ E

/-- Finite mass stated using explicit Hamiltonian spectral data. -/
def FiniteMassSpectralData {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : HamiltonianSpectralData G theory) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, HasMassGapSpectralData spectralData Δ → Δ ≤ m

/-- Finite mass stated using the PDF Hamiltonian spectral data. -/
def FiniteClayMass {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, HasClayMassGap spectralData Δ → Δ ≤ m

/-- The Clay mass: the supremum of all admissible physical spectral gaps. -/
noncomputable def clay_mass {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : ClayHamiltonianSpectralData G theory) : ℝ :=
  sSup {Δ : ℝ | HasClayMassGap spectralData Δ}

/--
A gap for the bounded comparison spectrum gives a gap for the corresponding PDF spectral datum.
-/
theorem HasMassGapSpectralData.mass_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ} :
    HasMassGapSpectralData spectralData Δ → HasClayMassGap spectralData.spectral_data Δ := by
  intro hGap
  exact hGap

/--
A finite upper bound for all bounded-comparison gaps also bounds the corresponding PDF gaps.
-/
theorem FiniteMassSpectralData.finite_mass {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} :
    FiniteMassSpectralData spectralData → FiniteClayMass spectralData.spectral_data := by
  rintro ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGap => hm_bound Δ hGap⟩

/--
For the PDF spectral data, a mass gap implies every physical spectral value is either the
vacuum energy `0` or at least `Δ`.
-/
theorem HasClayMassGap.eq_zero_or_gap_le {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ E : ℝ}
    (hGap : HasClayMassGap spectralData Δ) (hE : E ∈ spectralData.spectrum_set) :
    E = 0 ∨ Δ ≤ E := by
  have hnonneg : 0 ≤ E := spectralData.positive_energy E hE
  rcases lt_or_eq_of_le hnonneg with hpos | hzero
  · rcases lt_or_ge E Δ with hlt | hge
    · exfalso
      exact Set.disjoint_left.mp hGap.2 hE ⟨hpos, hlt⟩
    · exact Or.inr hge
  · exact Or.inl hzero.symm

/-- `HasClayMassGap` includes strict positivity of the gap. -/
theorem HasClayMassGap.pos {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasClayMassGap spectralData Δ) :
    0 < Δ :=
  hGap.1

/-- Any non-vacuum physical spectral value of a PDF-gapped Hamiltonian is at least `Δ`. -/
theorem HasClayMassGap.nonzero_energy_ge_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ E : ℝ}
    (hGap : HasClayMassGap spectralData Δ) (hE : E ∈ spectralData.spectrum_set) (hE0 : E ≠ 0) :
    Δ ≤ E := by
  rcases hGap.eq_zero_or_gap_le hE with hzero | hle
  · exact False.elim (hE0 hzero)
  · exact hle

/-- A PDF mass gap has no physical Hamiltonian spectrum in the open interval `(0, Δ)`. -/
theorem HasClayMassGap.not_mem_open_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ E : ℝ}
    (hGap : HasClayMassGap spectralData Δ) (hE : E ∈ spectralData.spectrum_set) :
    E ∉ Set.Ioo 0 Δ :=
  fun hInterval => Set.disjoint_left.mp hGap.2 hE hInterval

/-- A PDF mass gap gives the no-spectrum-in-`(0, Δ)` condition from the Clay writeup. -/
theorem HasClayMassGap.no_spectrum_in_open_interval {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasClayMassGap spectralData Δ) :
    ClayNoSpectrumInGap spectralData Δ :=
  hGap.2

/-- A PDF mass gap supplies the Hamiltonian spectral conditions from the Clay writeup. -/
theorem HasClayMassGap.hamiltonian_gap_conditions
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasClayMassGap spectralData Δ) :
    ClayHamiltonianGapConditions spectralData Δ :=
  ⟨spectralData.vacuum_zero_energy, spectralData.positive_energy, spectralData.vacuum_energy_zero, hGap.1, hGap.2⟩

/-- The PDF Hamiltonian spectral conditions imply `HasClayMassGap`. -/
theorem ClayHamiltonianGapConditions.mass_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : ClayHamiltonianGapConditions spectralData Δ) :
    HasClayMassGap spectralData Δ := by
  rcases hGap with ⟨_hVac, _hPos, _hZero, hΔ, hNoSpectrum⟩
  exact ⟨hΔ, hNoSpectrum⟩

/-- `HasClayMassGap` is equivalent to the PDF Hamiltonian spectral conditions. -/
theorem HasClayMassGap.iff_hamiltonian_gap_conditions
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ} :
    HasClayMassGap spectralData Δ ↔ ClayHamiltonianGapConditions spectralData Δ :=
  ⟨HasClayMassGap.hamiltonian_gap_conditions,
    ClayHamiltonianGapConditions.mass_gap⟩

/-- A PDF mass gap gives the vacuum-isolated form of the physical spectral gap. -/
theorem HasClayMassGap.vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasClayMassGap spectralData Δ) :
    ClayVacuumSpectralGap spectralData Δ :=
  ⟨hGap.pos, spectralData.vacuum_energy_zero,
    fun _ hE hE0 => hGap.nonzero_energy_ge_gap hE hE0⟩

/-- A PDF mass gap gives the PDF's excitation-energy formulation. -/
theorem HasClayMassGap.excitation_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasClayMassGap spectralData Δ) :
    ClayExcitationGap spectralData Δ :=
  ⟨hGap.pos, fun _ hE hE0 => hGap.nonzero_energy_ge_gap hE hE0⟩

/-- The vacuum-isolated PDF form implies the “no spectrum in `(0, Δ)`” form. -/
theorem ClayVacuumSpectralGap.mass_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : ClayVacuumSpectralGap spectralData Δ) :
    HasClayMassGap spectralData Δ := by
  refine ⟨hGap.1, ?_⟩
  rw [Set.disjoint_left]
  intro E hE hInterval
  exact not_lt_of_ge (hGap.2.2 E hE (ne_of_gt hInterval.1)) hInterval.2

/-- The PDF no-spectrum and vacuum-isolated spectral-gap formulations are equivalent. -/
theorem HasClayMassGap.iff_vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ} :
    HasClayMassGap spectralData Δ ↔ ClayVacuumSpectralGap spectralData Δ :=
  ⟨HasClayMassGap.vacuum_gap, ClayVacuumSpectralGap.mass_gap⟩

/-- The PDF's excitation-energy formulation implies the “no spectrum in `(0, Δ)`” form. -/
theorem ClayExcitationGap.mass_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : ClayExcitationGap spectralData Δ) :
    HasClayMassGap spectralData Δ := by
  refine ⟨hGap.1, ?_⟩
  rw [Set.disjoint_left]
  intro E hE hInterval
  exact not_lt_of_ge (hGap.2 E hE (ne_of_gt hInterval.1)) hInterval.2

/-- The PDF no-spectrum and excitation-energy formulations are equivalent. -/
theorem HasClayMassGap.iff_excitation_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ} :
    HasClayMassGap spectralData Δ ↔ ClayExcitationGap spectralData Δ :=
  ⟨HasClayMassGap.excitation_gap,
    ClayExcitationGap.mass_gap⟩

/-- A witnessed finite Clay mass upper bound bounds `clay_mass`. -/
theorem clay_mass.le_finite_bound
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {spectralData : ClayHamiltonianSpectralData G theory} {Δ m : ℝ}
    (hGap : HasClayMassGap spectralData Δ)
    (hm : ∀ Δ' : ℝ, HasClayMassGap spectralData Δ' → Δ' ≤ m) :
    clay_mass spectralData ≤ m := by
  dsimp [clay_mass]
  exact csSup_le ⟨Δ, hGap⟩ hm

/-- Every witnessed PDF spectral gap is bounded above by `clay_mass` under a finite-mass bound. -/
theorem HasClayMassGap.le_clay_mass_bounded
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {spectralData : ClayHamiltonianSpectralData G theory} {Δ m : ℝ}
    (hGap : HasClayMassGap spectralData Δ)
    (hm : ∀ Δ' : ℝ, HasClayMassGap spectralData Δ' → Δ' ≤ m) :
    Δ ≤ clay_mass spectralData := by
  dsimp [clay_mass]
  exact le_csSup ⟨m, hm⟩ hGap

/-- A PDF spectral datum with a witnessed gap and finite mass has positive `clay_mass`. -/
theorem clay_mass.pos_of_finite_bound
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {spectralData : ClayHamiltonianSpectralData G theory} {Δ m : ℝ}
    (hGap : HasClayMassGap spectralData Δ)
    (hm : ∀ Δ' : ℝ, HasClayMassGap spectralData Δ' → Δ' ≤ m) :
    0 < clay_mass spectralData :=
  lt_of_lt_of_le hGap.pos (hGap.le_clay_mass_bounded hm)

/-- A finite Clay mass witness supplies an explicit upper bound for `clay_mass`. -/
theorem FiniteClayMass.clay_mass_le_bound
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hFinite : FiniteClayMass spectralData) (hGap : HasClayMassGap spectralData Δ) :
    ∃ m : ℝ, m > 0 ∧ clay_mass spectralData ≤ m := by
  rcases hFinite with ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, clay_mass.le_finite_bound hGap hm_bound⟩

/-- Every witnessed PDF spectral gap is bounded above by `clay_mass` from `FiniteClayMass` directly. -/
theorem HasClayMassGap.le_clay_mass_finite
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasClayMassGap spectralData Δ) (hFinite : FiniteClayMass spectralData) :
    Δ ≤ clay_mass spectralData := by
  rcases hFinite with ⟨m, _hm_pos, hm_bound⟩
  exact hGap.le_clay_mass_bounded hm_bound

/-- A finite Clay mass witness and one gap make `clay_mass` strictly positive. -/
theorem FiniteClayMass.clay_mass_pos
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {spectralData : ClayHamiltonianSpectralData G theory} {Δ : ℝ}
    (hFinite : FiniteClayMass spectralData) (hGap : HasClayMassGap spectralData Δ) :
    0 < clay_mass spectralData := by
  rcases hFinite with ⟨m, _hm_pos, hm_bound⟩
  exact clay_mass.pos_of_finite_bound (m := m) hGap hm_bound

/-- Explicit spectral data gives the Mathlib-spectrum mass-gap predicate. -/
theorem HasMassGapSpectralData.spectrum {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ} :
    HasMassGapSpectralData spectralData Δ → HasMassGapSpectrum G theory Δ := by
  intro hGap
  exact ⟨hGap.1, by simpa [spectralData.spectrum_eq] using hGap.2⟩

/-- A Mathlib-spectrum gap is the same gap for matching explicit spectral data. -/
theorem HasMassGapSpectrum.spectral_data {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ} :
    HasMassGapSpectrum G theory Δ → HasMassGapSpectralData spectralData Δ := by
  intro hGap
  exact ⟨hGap.1, by simpa [spectralData.spectrum_eq] using hGap.2⟩

/--
With explicit spectral data, a mass gap implies every spectral value is either the vacuum energy
`0` or at least `Δ`.
-/
theorem HasMassGapSpectralData.eq_zero_or_gap_le {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ E : ℝ}
    (hGap : HasMassGapSpectralData spectralData Δ) (hE : E ∈ spectralData.spectrum_set) :
    E = 0 ∨ Δ ≤ E := by
  have hnonneg : 0 ≤ E := spectralData.positive_energy E hE
  rcases lt_or_eq_of_le hnonneg with hpos | hzero
  · rcases lt_or_ge E Δ with hlt | hge
    · exfalso
      exact Set.disjoint_left.mp hGap.2 hE ⟨hpos, hlt⟩
    · exact Or.inr hge
  · exact Or.inl hzero.symm

/-- A spectral-data mass gap is strictly positive. -/
theorem HasMassGapSpectralData.pos {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasMassGapSpectralData spectralData Δ) :
    0 < Δ :=
  hGap.1

/-- Any non-vacuum spectral value of a gapped Hamiltonian is at least the gap. -/
theorem HasMassGapSpectralData.nonzero_energy_ge_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ E : ℝ}
    (hGap : HasMassGapSpectralData spectralData Δ) (hE : E ∈ spectralData.spectrum_set) (hE0 : E ≠ 0) :
    Δ ≤ E := by
  rcases hGap.eq_zero_or_gap_le hE with hzero | hle
  · exact False.elim (hE0 hzero)
  · exact hle

/-- A spectral-data mass gap gives the vacuum-isolated form of the gap. -/
theorem HasMassGapSpectralData.vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : HasMassGapSpectralData spectralData Δ) :
    VacuumSpectralGap spectralData Δ :=
  ⟨hGap.pos, spectralData.vacuum_energy_zero,
    fun _ hE hE0 => hGap.nonzero_energy_ge_gap hE hE0⟩

/-- The vacuum-isolated form implies the spectral-data mass-gap exclusion. -/
theorem VacuumSpectralGap.mass_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : VacuumSpectralGap spectralData Δ) :
    HasMassGapSpectralData spectralData Δ := by
  refine ⟨hGap.1, ?_⟩
  rw [Set.disjoint_left]
  intro E hE hInterval
  exact not_lt_of_ge (hGap.2.2 E hE (ne_of_gt hInterval.1)) hInterval.2

/-- The spectral-data and vacuum-isolated forms of a mass gap are equivalent. -/
theorem HasMassGapSpectralData.iff_vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ} :
    HasMassGapSpectralData spectralData Δ ↔ VacuumSpectralGap spectralData Δ :=
  ⟨HasMassGapSpectralData.vacuum_gap, VacuumSpectralGap.mass_gap⟩

/-- Finite mass using the vacuum-isolated spectral-gap formulation. -/
def FiniteMassVacuumSpectralData {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : HamiltonianSpectralData G theory) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, VacuumSpectralGap spectralData Δ → Δ ≤ m

/-- Finite mass for spectral gaps gives finite mass for vacuum-isolated gaps. -/
theorem FiniteMassSpectralData.vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} :
    FiniteMassSpectralData spectralData → FiniteMassVacuumSpectralData spectralData := by
  rintro ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGap => hm_bound Δ hGap.mass_gap⟩

/-- Finite mass for vacuum-isolated gaps gives finite mass for spectral gaps. -/
theorem FiniteMassVacuumSpectralData.spectral_data
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} :
    FiniteMassVacuumSpectralData spectralData → FiniteMassSpectralData spectralData := by
  rintro ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGap => hm_bound Δ hGap.vacuum_gap⟩

/-- The two finite-mass formulations agree for a fixed spectral datum. -/
theorem FiniteMassSpectralData.iff_vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} :
    FiniteMassSpectralData spectralData ↔ FiniteMassVacuumSpectralData spectralData :=
  ⟨FiniteMassSpectralData.vacuum_gap,
    FiniteMassVacuumSpectralData.spectral_data⟩

/-- The vacuum energy belongs to the spectrum in a vacuum-isolated spectral gap. -/
theorem VacuumSpectralGap.vacuum_mem {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ : ℝ}
    (hGap : VacuumSpectralGap spectralData Δ) :
    0 ∈ spectralData.spectrum_set :=
  hGap.2.1

/-- Any nonzero spectral value in a vacuum-isolated spectral gap is at least the gap. -/
theorem VacuumSpectralGap.nonzero_energy_ge_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : HamiltonianSpectralData G theory} {Δ E : ℝ}
    (hGap : VacuumSpectralGap spectralData Δ) (hE : E ∈ spectralData.spectrum_set) (hE0 : E ≠ 0) :
    Δ ≤ E :=
  hGap.2.2 E hE hE0

/-- The Mathlib-spectrum formulation has the same spectral consequence. -/
theorem HasMassGapSpectrum.eq_zero_or_gap_le {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {Δ E : ℝ}
    (hGap : HasMassGapSpectrum G theory Δ)
    (hE : E ∈ spectrum ℝ theory.wightman.hamiltonian) :
    E = 0 ∨ Δ ≤ E := by
  let spectralData := HamiltonianSpectralData.of_quantum_theory G theory
  have hE' : E ∈ spectralData.spectrum_set := by
    simpa [spectralData, HamiltonianSpectralData.of_quantum_theory] using hE
  exact HasMassGapSpectralData.eq_zero_or_gap_le
    (spectralData := spectralData) (hGap.spectral_data (spectralData := spectralData)) hE'

/-- A spectral mass gap is strictly positive. -/
theorem HasMassGapSpectrum.pos {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {Δ : ℝ}
    (hGap : HasMassGapSpectrum G theory Δ) :
    0 < Δ :=
  hGap.1

/-- Any nonzero spectral value in the Mathlib spectrum is at least the gap. -/
theorem HasMassGapSpectrum.nonzero_energy_ge_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {Δ E : ℝ}
    (hGap : HasMassGapSpectrum G theory Δ)
    (hE : E ∈ spectrum ℝ theory.wightman.hamiltonian) (hE0 : E ≠ 0) :
    Δ ≤ E := by
  rcases hGap.eq_zero_or_gap_le hE with hzero | hle
  · exact False.elim (hE0 hzero)
  · exact hle

/-- The Mathlib-spectrum statement gives the vacuum-isolated gap form. -/
theorem HasMassGapSpectrum.vacuum_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {Δ : ℝ}
    (hGap : HasMassGapSpectrum G theory Δ) :
    VacuumSpectralGap (HamiltonianSpectralData.of_quantum_theory G theory) Δ :=
  (hGap.spectral_data (spectralData := HamiltonianSpectralData.of_quantum_theory G theory)).vacuum_gap

/-- Spectral data extracted from a theory carries the same mass-gap predicate as the theory. -/
theorem HasMassGapSpectralData.iff_of_quantum_theory {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {Δ : ℝ} :
    HasMassGapSpectralData (HamiltonianSpectralData.of_quantum_theory G theory) Δ ↔
      HasMassGapSpectrum G theory Δ := by
  constructor
  · exact HasMassGapSpectralData.spectrum
  · exact HasMassGapSpectrum.spectral_data

/--
The “mass” `m` as described in the Clay writeup: the supremum of the admissible spectral gaps.
-/
noncomputable def spectral_mass (G : Type) [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G) : ℝ :=
  sSup {Δ : ℝ | HasMassGapSpectrum G theory Δ}

/-- A witnessed finite-mass upper bound bounds `spectral_mass`. -/
theorem spectral_mass.le_finite_bound
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {Δ m : ℝ} (hGap : HasMassGapSpectrum G theory Δ)
    (hm : ∀ Δ' : ℝ, HasMassGapSpectrum G theory Δ' → Δ' ≤ m) :
    spectral_mass G theory ≤ m := by
  dsimp [spectral_mass]
  exact csSup_le ⟨Δ, hGap⟩ hm

/-- Every witnessed spectral gap is bounded above by `spectral_mass` when the set of gaps is bounded. -/
theorem HasMassGapSpectrum.le_mass_bounded
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {Δ m : ℝ} (hGap : HasMassGapSpectrum G theory Δ)
    (hm : ∀ Δ' : ℝ, HasMassGapSpectrum G theory Δ' → Δ' ≤ m) :
    Δ ≤ spectral_mass G theory := by
  dsimp [spectral_mass]
  exact le_csSup ⟨m, hm⟩ hGap

/-- A theory with a witnessed spectral gap and finite mass has positive `spectral_mass`. -/
theorem spectral_mass.pos_of_finite_bound
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    {Δ m : ℝ} (hGap : HasMassGapSpectrum G theory Δ)
    (hm : ∀ Δ' : ℝ, HasMassGapSpectrum G theory Δ' → Δ' ≤ m) :
    0 < spectral_mass G theory :=
  lt_of_lt_of_le hGap.pos (hGap.le_mass_bounded hm)

/--
“Existence” requirements highlighted in the Clay statement.

In this development, these are fields and laws inside `QuantumYangMillsTheory`:
- Wightman-style properties (`theory.wightman`)
- Osterwalder--Schrader-strength Euclidean data (`theory.osterwalder_schrader`)
- Local-operator correspondence (`theory.local_operators`)
- Short-distance agreement (`theory.short_distance`)
- Stress tensor (`theory.stress_tensor`)
- Operator product expansion (`theory.operator_product_expansion`)

The `QuantumYangMillsTheory` data already stores these fields. The Clay existence predicate below
re-exposes the extra non-vacuity and vacuum requirements that are easy to lose if existence is
treated as a bare type.
-/
structure ClayQuantumFieldTheoryAxioms {G : Type} [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) : Prop where
  /-- Wightman covariance of the smeared quantum fields. -/
  field_covariance :
    ∀ g f, theory.field_operators (theory.wightman.action_on_tests g f) =
      conjugate_operator (theory.wightman.unitary_rep g) (theory.field_operators f)
  /-- Wightman locality/causality for spacelike separated test functions. -/
  field_locality :
    ∀ (f g : SchwartzMap Spacetime ℝ),
      (∀ (x y : Spacetime),
        (minkowski_metric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) →
      theory.field_operators f ∘L theory.field_operators g =
        theory.field_operators g ∘L theory.field_operators f
  /-- Positive-energy Hamiltonian. -/
  wightman_positive_energy : theory.wightman.hamiltonian.IsPositive
  /-- The Hamiltonian spectrum is supported in `[0, ∞)`. -/
  wightman_spectrum_nonnegative :
    ∀ E, E ∈ spectrum ℝ theory.wightman.hamiltonian → 0 ≤ E
  /-- The normalized Poincare-invariant vacuum is unique. -/
  wightman_vacuum_unique :
    ∀ Ω' : theory.hilbert_space,
      IsVacuum Ω' theory.wightman.hamiltonian →
        (∀ g, theory.wightman.unitary_rep g Ω' = Ω') →
          ‖Ω'‖ = 1 →
            Ω' = theory.wightman.vacuum
  /-- Osterwalder-Schrader reflection positivity. -/
  os_reflection_positivity :
    ∀ fs : List SchwartzSpace,
      0 ≤ theory.osterwalder_schrader.schwinger_function
        (fs.map theory.osterwalder_schrader.time_reflection ++ fs)
  /-- OS reconstruction agrees with the Wightman correlation functions. -/
  os_reconstruction_agrees :
    ∀ fs : List SchwartzSpace,
      theory.osterwalder_schrader.schwinger_function fs =
        correlation theory.field_operators theory.wightman.vacuum fs
  /-- The Clay local-polynomial correspondence is injective. -/
  local_operator_correspondence : Function.Injective theory.local_operators.op
  /-- Local gauge-invariant operators transform covariantly. -/
  local_operator_covariance :
    ∀ g p f,
      (theory.local_operators.op p) (theory.wightman.action_on_tests g f) =
        conjugate_operator (theory.wightman.unitary_rep g) ((theory.local_operators.op p) f)
  /-- Local gauge-invariant operators commute at spacelike separation. -/
  local_operator_locality :
    ∀ (p q : GaugeInvariantLocalPolynomial G) (f g : SchwartzMap Spacetime ℝ),
      (∀ (x y : Spacetime),
        (minkowski_metric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) →
      (theory.local_operators.op p f) ∘L (theory.local_operators.op q g) =
        (theory.local_operators.op q g) ∘L (theory.local_operators.op p f)
  /-- Short-distance agreement with perturbative/asymptotic-freedom predictions. -/
  short_distance_agreement :
    ∀ fs : List SchwartzSpace,
      Filter.Tendsto
        (fun ε : ℝ =>
          correlation theory.field_operators theory.wightman.vacuum
              (fs.map (theory.short_distance.scale ε)) -
            theory.short_distance.prediction ε fs)
        (nhdsWithin (0 : ℝ) {ε : ℝ | 0 < ε})
        (nhds 0)
  /-- Distributional conservation law for the stress-energy tensor. -/
  stress_tensor_conserved :
    ∀ ν f,
      (Finset.univ.sum fun μ : Fin 4 =>
        theory.stress_tensor.T μ ν (theory.stress_tensor.test_deriv μ f)) = 0
  /-- Local finiteness for the operator product expansion. -/
  operator_product_finite :
    ∀ A B,
      Set.Finite
        {C : GaugeInvariantLocalPolynomial G |
          theory.operator_product_expansion.coefficient A B C ≠ 0}

/--
The `QuantumYangMillsTheory` fields supply the Clay-required Wightman, OS, short-distance,
stress-tensor, local-operator, and OPE properties.
-/
theorem ClayQuantumFieldTheoryAxioms.of_quantum_theory
    {G : Type} [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G) :
    ClayQuantumFieldTheoryAxioms theory :=
  { field_covariance := theory.wightman.covariance
    field_locality := theory.wightman.locality
    wightman_positive_energy := theory.wightman.is_hamiltonian_positive
    wightman_spectrum_nonnegative := theory.wightman.spectrum_nonneg
    wightman_vacuum_unique := theory.wightman.vacuum_unique
    os_reflection_positivity := theory.osterwalder_schrader.reflection_positivity
    os_reconstruction_agrees := theory.osterwalder_schrader.reconstruction_agrees
    local_operator_correspondence := theory.local_operators.injective
    local_operator_covariance := theory.local_operators_covariant
    local_operator_locality := theory.local_operators_locality
    short_distance_agreement := theory.short_distance.agrees
    stress_tensor_conserved := theory.stress_tensor.conserved
    operator_product_finite := theory.operator_product_expansion.finite_support }

/--
Clay non-trivial existence package for a fixed Yang--Mills quantum field theory.

This bundles the Wightman and Osterwalder--Schrader axiom requirements, normalized unique
vacuum, and nonzero gauge-invariant local curvature operators such as the displayed
`Tr Fᵢⱼ Fₖₗ(x)` example.
-/
structure ClayExistence {G : Type} [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) : Prop where
  /-- Wightman and Osterwalder-Schrader axiom properties, as in the PDF. -/
  axioms : ClayQuantumFieldTheoryAxioms theory
  /-- The physical Hilbert space is non-trivial. -/
  nontrivial : NontrivialTheory theory
  /-- The vacuum vector is normalized. -/
  vacuum_norm_one : ‖theory.wightman.vacuum‖ = 1
  /-- The normalized Poincaré-invariant vacuum is unique. -/
  vacuum_unique :
    ∀ Ω' : theory.hilbert_space,
      IsVacuum Ω' theory.wightman.hamiltonian →
        (∀ g, theory.wightman.unitary_rep g Ω' = Ω') →
          ‖Ω'‖ = 1 →
            Ω' = theory.wightman.vacuum
  /-- The curvature local operator is not identically zero after smearing. -/
  curvature_local_operator_nonzero :
    ∃ f : SchwartzSpace,
      theory.local_operators.op (GaugeInvariantLocalPolynomial.curvature : GaugeInvariantLocalPolynomial G)
        f ≠ 0

/-- A non-trivial theory supplies the remaining Clay existence data already built into the model. -/
theorem ClayExistence.of_nontrivial_theory {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (h : NontrivialTheory theory) :
    ClayExistence theory :=
  { axioms := ClayQuantumFieldTheoryAxioms.of_quantum_theory theory
    nontrivial := h
    vacuum_norm_one := theory.wightman.vacuum_norm_one
    vacuum_unique := theory.wightman.vacuum_unique
    curvature_local_operator_nonzero := theory.curvature_local_operator_nonzero }

/--
Clay PDF local-operator correspondence:
gauge-invariant local polynomials in the curvature `F` and its covariant derivatives are assigned
local quantum field operators.
-/
def ClayLocalOperatorCorrespondence
    {G : Type} [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G) : Prop :=
  Function.Injective theory.local_operators.op

/-- The Clay example `Tr Fᵢⱼ Fₖₗ(x)` as a gauge-invariant local curvature polynomial. -/
def clay_trace_curvature_product
    (G : Type) (i j k l : Fin 4) : GaugeInvariantLocalPolynomial G :=
  trace_curvature_product G i j k l

/-- The local quantum field operator assigned to the Clay example `Tr Fᵢⱼ Fₖₗ(x)`. -/
def clay_trace_curvature_product_operator
    {G : Type} [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G)
    (i j k l : Fin 4) : OperatorValuedDistribution theory.hilbert_space :=
  theory.local_operators.op (clay_trace_curvature_product G i j k l)

/-- The Clay quantum-field-theory axioms include the local gauge-invariant operator correspondence. -/
theorem ClayQuantumFieldTheoryAxioms.has_local_operator_correspondence
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    (h : ClayQuantumFieldTheoryAxioms theory) :
    ClayLocalOperatorCorrespondence theory :=
  h.local_operator_correspondence

/-- Clay existence exposes the local gauge-invariant operator correspondence. -/
theorem ClayExistence.local_operator_correspondence
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    (h : ClayExistence theory) :
    ClayLocalOperatorCorrespondence theory :=
  h.axioms.has_local_operator_correspondence

/-- Clay existence includes a nonzero curvature local operator. -/
theorem ClayExistence.exists_nonzero_curvature_operator
    {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}
    (h : ClayExistence theory) :
    ∃ f : SchwartzSpace,
      theory.local_operators.op (GaugeInvariantLocalPolynomial.curvature : GaugeInvariantLocalPolynomial G)
        f ≠ 0 :=
  h.curvature_local_operator_nonzero

/-- The displayed Clay trace-curvature operator is assigned to `Tr Fᵢⱼ Fₖₗ(x)`. -/
theorem clay_trace_curvature_product_operator.eq_local_operator
    {G : Type} [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G)
    (i j k l : Fin 4) :
    clay_trace_curvature_product_operator theory i j k l =
      theory.local_operators.op (trace_curvature_product G i j k l) :=
  rfl

/--
Finite mass condition corresponding to the Clay definition of “mass” as the supremum of gaps.

This is the existence of an upper bound on all spectral gaps.
-/
def FiniteMassSpectrum (G : Type) [CompactSimpleGaugeGroup G] (theory : QuantumYangMillsTheory G) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, HasMassGapSpectrum G theory Δ → Δ ≤ m

/--
Clustering estimate from the Clay writeup (equation (2), stated as a `Prop`).

We model `O(⃗x) = U(⃗x) O U(⃗x)⁻¹` using the spatial translation representation
`U := theory.wightman.space_translation`.
-/
def ClusteringProperty (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → C < Δ →
    ∀ O : LinearOperator theory.hilbert_space,
      IsCentered theory.wightman.vacuum O →
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ x y : Space,
            R ≤ dist x y →
              |vacuum_expectation theory.wightman.vacuum
                    ((local_operator_at theory.wightman.space_translation x O).comp
                      (local_operator_at theory.wightman.space_translation y O))| ≤
                Real.exp (-C * dist x y)

/--
The Clay writeup notes that a mass gap implies clustering.
-/
def MassGapImpliesClustering (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) : Prop :=
  ∀ Δ : ℝ, HasMassGapSpectrum G theory Δ → ClusteringProperty G theory Δ

/--
Bounded-spectrum comparison version of Yang--Mills existence and mass gap.

This statement identifies the Hamiltonian spectrum with Mathlib's bounded-operator spectrum.
The Clay statement below instead uses `ClayHamiltonianSpectralData`, leaving the physical spectrum
as an explicit field of the Yang--Mills theory package.
-/
def ClayYangMills.Formulations.BoundedSpectrum (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence theory ∧ HasMassGapSpectrum G theory Δ ∧ FiniteMassSpectrum G theory

/--
Spectral-data version of the bounded-spectrum comparison statement.

The Hamiltonian spectral data is induced by the Wightman-style properties of the
theory: positive energy, vacuum energy `0`, and agreement with Mathlib's spectrum.
-/
def ClayYangMills.Formulations.BoundedSpectralData (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence theory ∧
      HasMassGapSpectralData (HamiltonianSpectralData.of_quantum_theory G theory) Δ ∧
        FiniteMassSpectralData (HamiltonianSpectralData.of_quantum_theory G theory)

/--
Clay Yang--Mills existence and mass gap for a fixed compact simple gauge group.

This formulation uses explicit Hamiltonian spectral data.  The bounded-spectrum comparison,
unbounded self-adjoint Hamiltonian, and Lorentz-covariant formulations are connected by explicit
implication theorems.
-/
def ClayYangMills.Formulations.FixedGroup (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
    (spectralData : ClayHamiltonianSpectralData G theory),
    ClayExistence theory ∧ HasClayMassGap spectralData Δ ∧ FiniteClayMass spectralData

/--
Vacuum-isolated form of Yang--Mills existence and mass gap for a fixed compact simple gauge group.
-/
def ClayYangMills.Formulations.VacuumGap
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
    (spectralData : ClayHamiltonianSpectralData G theory),
    ClayExistence theory ∧ ClayVacuumSpectralGap spectralData Δ ∧ FiniteClayMass spectralData

/--
Yang--Mills existence and mass gap in the official explicit “on `ℝ⁴`” wording.
-/
def ClayYangMills.Formulations.OnFourDimensionalSpacetime (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : ClayQuantumYangMillsTheoryOnFourDimensionalSpacetime G) (Δ : ℝ)
    (spectralData : ClayHamiltonianSpectralData G theory),
    ClayExistence theory ∧ HasClayMassGap spectralData Δ ∧ FiniteClayMass spectralData

/--
Fixed-group statement with the official “on `ℝ⁴`” and positive mass gap `Δ > 0` wording visible
in the proposition itself.
-/
def ClayYangMills.Formulations.PositiveGapOnFourDimensionalSpacetime
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : ClayQuantumYangMillsTheoryOnFourDimensionalSpacetime G) (Δ : ℝ)
    (spectralData : ClayHamiltonianSpectralData G theory),
    ClayExistence theory ∧ 0 < Δ ∧ HasClayMassGap spectralData Δ ∧ FiniteClayMass spectralData

/--
Yang--Mills existence and mass gap in excitation-energy wording: every
non-vacuum physical Hamiltonian spectral value has energy at least the positive gap `Δ`.
-/
def ClayYangMills.Formulations.ExcitationGap
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
    (spectralData : ClayHamiltonianSpectralData G theory),
    ClayExistence theory ∧ ClayExcitationGap spectralData Δ ∧ FiniteClayMass spectralData

/--
Yang--Mills existence and mass gap with the Hamiltonian spectral sentences recorded explicitly:
`HΩ = 0`, positive spectrum, vacuum energy `0`, and no spectrum in `(0, Δ)` for a positive `Δ`.
-/
def ClayYangMills.Formulations.HamiltonianGap
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
    (spectralData : ClayHamiltonianSpectralData G theory),
    ClayExistence theory ∧ ClayHamiltonianGapConditions spectralData Δ ∧ FiniteClayMass spectralData

/--
Fixed-group Clay statement unpacked with the PDF's positive gap `Δ > 0` visible explicitly.
-/
theorem ClayYangMills.Formulations.FixedGroup.exists_positive_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    (h : ClayYangMills.Formulations.FixedGroup G) :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ 0 < Δ ∧ HasClayMassGap spectralData Δ := by
  rcases h with ⟨theory, Δ, spectralData, hExist, hGap, _hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.pos, hGap⟩

/--
The explicit-on-`ℝ⁴` Clay statement unpacked with the positive gap `Δ > 0` visible explicitly.
-/
theorem ClayYangMills.Formulations.OnFourDimensionalSpacetime.exists_positive_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    (h : ClayYangMills.Formulations.OnFourDimensionalSpacetime G) :
    ∃ (theory : ClayQuantumYangMillsTheoryOnFourDimensionalSpacetime G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ 0 < Δ ∧ HasClayMassGap spectralData Δ ∧
          FiniteClayMass spectralData := by
  rcases h with ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.pos, hGap, hFinite⟩

/--
The fixed-group explicit-`ℝ⁴` statement is equivalent to the same statement with `Δ > 0`
displayed separately.
-/
theorem ClayYangMills.Formulations.OnFourDimensionalSpacetime.iff_positive_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.OnFourDimensionalSpacetime G ↔
      ClayYangMills.Formulations.PositiveGapOnFourDimensionalSpacetime G := by
  constructor
  · exact ClayYangMills.Formulations.OnFourDimensionalSpacetime.exists_positive_gap (G := G)
  · rintro ⟨theory, Δ, spectralData, hExist, _hΔ, hGap, hFinite⟩
    exact ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩

/-- Build the fixed-group Clay mass-gap statement from the spectral-data formulation. -/
theorem ClayYangMills.Formulations.FixedGroup.of_spectral_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectralData G → ClayYangMills.Formulations.FixedGroup G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, (HamiltonianSpectralData.of_quantum_theory G theory).spectral_data,
    hExist, hGap.mass_gap, hFinite.finite_mass⟩

/-- The no-spectrum-in-`(0, Δ)` Clay statement gives the excitation-energy statement. -/
theorem ClayYangMills.Formulations.FixedGroup.excitation_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.FixedGroup G →
      ClayYangMills.Formulations.ExcitationGap G := by
  rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.excitation_gap, hFinite⟩

/-- The excitation-energy Clay statement gives the no-spectrum-in-`(0, Δ)` statement. -/
theorem ClayYangMills.Formulations.ExcitationGap.mass_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.ExcitationGap G →
      ClayYangMills.Formulations.FixedGroup G := by
  rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.mass_gap, hFinite⟩

/-- The two PDF fixed-group Yang--Mills mass-gap wordings are equivalent. -/
theorem ClayYangMills.Formulations.FixedGroup.iff_excitation_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.FixedGroup G ↔
      ClayYangMills.Formulations.ExcitationGap G := by
  constructor
  · exact ClayYangMills.Formulations.FixedGroup.excitation_gap G
  · exact ClayYangMills.Formulations.ExcitationGap.mass_gap G

/-- The standard Clay statement gives the Hamiltonian-spectral PDF form. -/
theorem ClayYangMills.Formulations.FixedGroup.hamiltonian_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.FixedGroup G →
      ClayYangMills.Formulations.HamiltonianGap G := by
  rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.hamiltonian_gap_conditions, hFinite⟩

/-- The Hamiltonian-spectral PDF form gives the standard Clay statement. -/
theorem ClayYangMills.Formulations.HamiltonianGap.mass_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.HamiltonianGap G →
      ClayYangMills.Formulations.FixedGroup G := by
  rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.mass_gap, hFinite⟩

/-- The standard fixed-group Clay statement is equivalent to the Hamiltonian-spectral form. -/
theorem ClayYangMills.Formulations.FixedGroup.iff_hamiltonian_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.FixedGroup G ↔
      ClayYangMills.Formulations.HamiltonianGap G := by
  constructor
  · exact ClayYangMills.Formulations.FixedGroup.hamiltonian_gap G
  · exact ClayYangMills.Formulations.HamiltonianGap.mass_gap G

/-- The PDF mass-gap statement is equivalent to the vacuum-isolated spectral wording. -/
theorem ClayYangMills.Formulations.FixedGroup.iff_vacuum_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.FixedGroup G ↔
      ClayYangMills.Formulations.VacuumGap G := by
  constructor
  · rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
    exact ⟨theory, Δ, spectralData, hExist, hGap.vacuum_gap, hFinite⟩
  · rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
    exact ⟨theory, Δ, spectralData, hExist, hGap.mass_gap, hFinite⟩

/--
Vacuum-isolated version of Yang--Mills existence and mass gap: the vacuum energy `0` is present,
and every non-vacuum Hamiltonian spectral value is at least the positive gap `Δ`.
-/
def ClayYangMills.Formulations.BoundedVacuumGap
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence theory ∧
      VacuumSpectralGap (HamiltonianSpectralData.of_quantum_theory G theory) Δ ∧
        FiniteMassVacuumSpectralData (HamiltonianSpectralData.of_quantum_theory G theory)

/-- The explicit spectral-data statement implies the main mass-gap statement. -/
theorem ClayYangMills.Formulations.BoundedSpectralData.mass_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectralData G → ClayYangMills.Formulations.BoundedSpectrum G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite⟩
  refine ⟨theory, Δ, hExist, hGap.spectrum, ?_⟩
  rcases hFinite with ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGapSpectrum => hm_bound Δ hGapSpectrum.spectral_data⟩

/-- The bounded-spectrum statement determines the corresponding explicit spectral-data formulation. -/
theorem ClayYangMills.Formulations.BoundedSpectrum.spectral_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectrum G → ClayYangMills.Formulations.BoundedSpectralData G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite⟩
  let spectralData := HamiltonianSpectralData.of_quantum_theory G theory
  refine ⟨theory, Δ, hExist, hGap.spectral_data, ?_⟩
  rcases hFinite with ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGapData => hm_bound Δ hGapData.spectrum⟩

/-- The bounded-spectrum and spectral-data Yang--Mills statements are equivalent. -/
theorem ClayYangMills.Formulations.BoundedSpectrum.iff_spectral_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectrum G ↔ ClayYangMills.Formulations.BoundedSpectralData G := by
  constructor
  · exact ClayYangMills.Formulations.BoundedSpectrum.spectral_gap G
  · exact ClayYangMills.Formulations.BoundedSpectralData.mass_gap G

/-- The spectral-data statement gives the vacuum-isolated formulation. -/
theorem ClayYangMills.Formulations.BoundedSpectralData.vacuum_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectralData G →
      ClayYangMills.Formulations.BoundedVacuumGap G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, hExist, hGap.vacuum_gap, hFinite.vacuum_gap⟩

/-- The vacuum-isolated formulation gives the spectral-data statement. -/
theorem ClayYangMills.Formulations.BoundedVacuumGap.spectral_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedVacuumGap G →
      ClayYangMills.Formulations.BoundedSpectralData G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, hExist, hGap.mass_gap, hFinite.spectral_data⟩

/-- The spectral-data and vacuum-isolated Yang--Mills statements are equivalent. -/
theorem ClayYangMills.Formulations.BoundedSpectralData.iff_vacuum_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectralData G ↔
      ClayYangMills.Formulations.BoundedVacuumGap G := by
  constructor
  · exact ClayYangMills.Formulations.BoundedSpectralData.vacuum_gap G
  · exact ClayYangMills.Formulations.BoundedVacuumGap.spectral_gap G

/-- The bounded-spectrum Yang--Mills mass-gap statement is equivalent to the vacuum-isolated form. -/
theorem ClayYangMills.Formulations.BoundedSpectrum.iff_vacuum_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.BoundedSpectrum G ↔ ClayYangMills.Formulations.BoundedVacuumGap G :=
  (ClayYangMills.Formulations.BoundedSpectrum.iff_spectral_gap G).trans
    (ClayYangMills.Formulations.BoundedSpectralData.iff_vacuum_gap G)

/-- Clay-style statement adding the clustering consequence to existence and mass gap. -/
def ClayYangMills.Formulations.Clustering.MassGap (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence theory ∧
      HasMassGapSpectrum G theory Δ ∧
      FiniteMassSpectrum G theory ∧
      MassGapImpliesClustering G theory

/--
Spectral-data-and-clustering Yang--Mills statement: non-trivial existence, Mathlib-spectrum
spectral data, a mass gap, and the clustering consequence.
-/
def ClayYangMills.Formulations.Clustering.SpectralGap
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence theory ∧
      HasMassGapSpectralData (HamiltonianSpectralData.of_quantum_theory G theory) Δ ∧
      FiniteMassSpectralData (HamiltonianSpectralData.of_quantum_theory G theory) ∧
      MassGapImpliesClustering G theory

/-- The clustering-augmented statement implies the main mass-gap statement. -/
theorem ClayYangMills.Formulations.Clustering.MassGap.mass_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.Clustering.MassGap G → ClayYangMills.Formulations.BoundedSpectrum G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite, _hClustering⟩
  exact ⟨theory, Δ, hExist, hGap, hFinite⟩

/-- The spectral-data-and-clustering statement implies the clustering statement. -/
theorem ClayYangMills.Formulations.Clustering.SpectralGap.clustering
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.Clustering.SpectralGap G →
      ClayYangMills.Formulations.Clustering.MassGap G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite, hClustering⟩
  refine ⟨theory, Δ, hExist, hGap.spectrum, ?_, hClustering⟩
  rcases hFinite with ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGapSpectrum => hm_bound Δ hGapSpectrum.spectral_data⟩

/-- The clustering statement supplies the spectral-data-and-clustering formulation. -/
theorem ClayYangMills.Formulations.Clustering.MassGap.spectral_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.Clustering.MassGap G →
      ClayYangMills.Formulations.Clustering.SpectralGap G := by
  rintro ⟨theory, Δ, hExist, hGap, hFinite, hClustering⟩
  let spectralData := HamiltonianSpectralData.of_quantum_theory G theory
  refine ⟨theory, Δ, hExist, hGap.spectral_data, ?_, hClustering⟩
  rcases hFinite with ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGapData => hm_bound Δ hGapData.spectrum⟩

/-- The clustering and spectral-data clustering Yang--Mills statements are equivalent. -/
theorem ClayYangMills.Formulations.Clustering.MassGap.iff_spectral_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.Clustering.MassGap G ↔
      ClayYangMills.Formulations.Clustering.SpectralGap G := by
  constructor
  · exact ClayYangMills.Formulations.Clustering.MassGap.spectral_gap G
  · exact ClayYangMills.Formulations.Clustering.SpectralGap.clustering G

/--
The Clay Millennium problem in its global quantifier form: for every compact simple gauge group
`G`, there is a non-trivial four-dimensional quantum Yang--Mills theory with PDF Hamiltonian
spectral data, a positive gap, and finite Clay mass.
-/
def ClayYangMills.Formulations.Global.MassGap : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G], ClayYangMills.Formulations.FixedGroup G

/-- Global compact-simple-gauge-group form of the Mathlib-spectrum spectral-data statement. -/
def ClayYangMills.Formulations.Global.BoundedSpectralData : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G], ClayYangMills.Formulations.BoundedSpectralData G

/--
Global compact-simple-gauge-group form of the vacuum-isolated spectral-gap statement.
-/
def ClayYangMills.Formulations.Global.VacuumGap : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G],
    ClayYangMills.Formulations.VacuumGap G

/--
Global compact-simple-gauge-group form with the PDF's explicit “on `ℝ⁴`” wording.
-/
def ClayYangMills.Formulations.Global.OnFourDimensionalSpacetime : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G], ClayYangMills.Formulations.OnFourDimensionalSpacetime G

/--
Global compact-simple-gauge-group form with both the PDF's “on `ℝ⁴`” wording and the positive
mass gap `Δ > 0` visible explicitly.
-/
def ClayYangMills.Formulations.Global.PositiveGapOnFourDimensionalSpacetime : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G], ClayYangMills.Formulations.PositiveGapOnFourDimensionalSpacetime G

/--
Global compact-simple-gauge-group form in the PDF's excitation-energy wording.
-/
def ClayYangMills.Formulations.Global.ExcitationGap : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G], ClayYangMills.Formulations.ExcitationGap G

/--
Global compact-simple-gauge-group form with the Hamiltonian spectral sentences from the PDF
recorded explicitly.
-/
def ClayYangMills.Formulations.Global.HamiltonianGap : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G],
    ClayYangMills.Formulations.HamiltonianGap G

/--
`ClayYangMills`:
for any compact simple gauge group, construct a non-trivial quantum Yang--Mills theory on `ℝ⁴`
with a positive finite mass gap.

The repository registry uses the physical-Hamiltonian strengthening in
`Problems.YangMills.HamiltonianSpectrum`; that formulation includes this mass-gap statement.
-/
def ClayYangMills : Prop :=
  ClayYangMills.Formulations.Global.MassGap

/-- The Clay Yang--Mills statement is the global compact-simple-gauge-group statement. -/
theorem ClayYangMills.iff_global_mass_gap :
    ClayYangMills ↔
      ClayYangMills.Formulations.Global.MassGap :=
  Iff.rfl

/-- `ClayYangMills` is equivalent to the global statement with `on four-dimensional spacetime` visible. -/
theorem ClayYangMills.iff_on_r4 :
    ClayYangMills ↔
      ClayYangMills.Formulations.Global.OnFourDimensionalSpacetime :=
  Iff.rfl

/--
`ClayYangMills` is equivalent to the global “on `ℝ⁴` with `Δ > 0`” wording.
-/
theorem ClayYangMills.iff_positive_gap_on_r4 :
    ClayYangMills ↔
      ClayYangMills.Formulations.Global.PositiveGapOnFourDimensionalSpacetime := by
  rw [ClayYangMills.iff_on_r4]
  constructor
  · intro h G
    exact (ClayYangMills.Formulations.OnFourDimensionalSpacetime.iff_positive_gap G).1 (h G)
  · intro h G
    exact (ClayYangMills.Formulations.OnFourDimensionalSpacetime.iff_positive_gap G).2 (h G)

/--
For every compact simple gauge group, bounded comparison spectral data determines the
Clay Hamiltonian spectral mass gap.
-/
theorem ClayYangMills.Formulations.Global.BoundedSpectralData.mass_gap :
    ClayYangMills.Formulations.Global.BoundedSpectralData →
      ClayYangMills.Formulations.Global.MassGap := by
  intro h G
  exact (ClayYangMills.Formulations.FixedGroup.of_spectral_gap G) (h G)

/-- The global Clay statement is equivalent to the vacuum-isolated spectral-gap form. -/
theorem ClayYangMills.Formulations.Global.MassGap.iff_vacuum_gap :
    ClayYangMills.Formulations.Global.MassGap ↔
      ClayYangMills.Formulations.Global.VacuumGap := by
  constructor
  · intro h G
    exact (ClayYangMills.Formulations.FixedGroup.iff_vacuum_gap G).1 (h G)
  · intro h G
    exact (ClayYangMills.Formulations.FixedGroup.iff_vacuum_gap G).2 (h G)

/-- `ClayYangMills` is equivalent to the vacuum-isolated global form. -/
theorem ClayYangMills.iff_vacuum_gap :
    ClayYangMills ↔
      ClayYangMills.Formulations.Global.VacuumGap :=
  ClayYangMills.iff_global_mass_gap.trans
    ClayYangMills.Formulations.Global.MassGap.iff_vacuum_gap

/-- The global Clay statement is equivalent to the excitation-energy wording. -/
theorem ClayYangMills.Formulations.Global.MassGap.iff_excitation_gap :
    ClayYangMills.Formulations.Global.MassGap ↔
      ClayYangMills.Formulations.Global.ExcitationGap := by
  constructor
  · intro h G
    exact (ClayYangMills.Formulations.FixedGroup.iff_excitation_gap G).1 (h G)
  · intro h G
    exact (ClayYangMills.Formulations.FixedGroup.iff_excitation_gap G).2 (h G)

/-- `ClayYangMills` is equivalent to the PDF's excitation-energy global form. -/
theorem ClayYangMills.iff_excitation_gap :
    ClayYangMills ↔
      ClayYangMills.Formulations.Global.ExcitationGap :=
  ClayYangMills.iff_global_mass_gap.trans
    ClayYangMills.Formulations.Global.MassGap.iff_excitation_gap

/-- The global Clay statement is equivalent to the Hamiltonian-spectral formulation. -/
theorem ClayYangMills.Formulations.Global.MassGap.iff_hamiltonian_gap :
    ClayYangMills.Formulations.Global.MassGap ↔
      ClayYangMills.Formulations.Global.HamiltonianGap := by
  constructor
  · intro h G
    exact (ClayYangMills.Formulations.FixedGroup.iff_hamiltonian_gap G).1 (h G)
  · intro h G
    exact (ClayYangMills.Formulations.FixedGroup.iff_hamiltonian_gap G).2 (h G)

/-- `ClayYangMills` is equivalent to the Hamiltonian-spectral PDF form. -/
theorem ClayYangMills.iff_hamiltonian_gap :
    ClayYangMills ↔
      ClayYangMills.Formulations.Global.HamiltonianGap :=
  ClayYangMills.iff_global_mass_gap.trans
    ClayYangMills.Formulations.Global.MassGap.iff_hamiltonian_gap

/-- A solution of the Clay statement gives a mass-gap construction for every compact simple gauge group. -/
theorem ClayYangMills.global_mass_gap
    (h : ClayYangMills) :
    ClayYangMills.Formulations.Global.MassGap :=
  ClayYangMills.iff_global_mass_gap.1 h

/-- Build the Clay Yang--Mills statement from mass-gap data for every compact simple gauge group. -/
theorem ClayYangMills.of_global_mass_gap
    (h : ClayYangMills.Formulations.Global.MassGap) :
    ClayYangMills :=
  ClayYangMills.iff_global_mass_gap.2 h

/-- A Clay Yang--Mills solution gives the global explicit `ℝ⁴` formulation. -/
theorem ClayYangMills.on_four_dimensional_spacetime
    (h : ClayYangMills) :
    ClayYangMills.Formulations.Global.OnFourDimensionalSpacetime :=
  ClayYangMills.iff_on_r4.1 h

/-- Build the Clay Yang--Mills statement from the global explicit “on `ℝ⁴`” wording. -/
theorem ClayYangMills.of_on_r4
    (h : ClayYangMills.Formulations.Global.OnFourDimensionalSpacetime) :
    ClayYangMills :=
  ClayYangMills.iff_on_r4.2 h

/-- A Clay Yang--Mills solution gives the global explicit `ℝ⁴` formulation with `Δ > 0`. -/
theorem ClayYangMills.positive_gap_on_four_dimensional_spacetime
    (h : ClayYangMills) :
    ClayYangMills.Formulations.Global.PositiveGapOnFourDimensionalSpacetime :=
  ClayYangMills.iff_positive_gap_on_r4.1 h

/-- Build the Clay Yang--Mills statement from the explicit “on `ℝ⁴` with `Δ > 0`” wording. -/
theorem ClayYangMills.of_positive_gap_on_r4
    (h : ClayYangMills.Formulations.Global.PositiveGapOnFourDimensionalSpacetime) :
    ClayYangMills :=
  ClayYangMills.iff_positive_gap_on_r4.2 h

/-- Build the Clay Yang--Mills statement from bounded spectral data for all gauge groups. -/
theorem ClayYangMills.of_spectral_gap
    (h : ClayYangMills.Formulations.Global.BoundedSpectralData) :
    ClayYangMills :=
  ClayYangMills.iff_global_mass_gap.2
    (ClayYangMills.Formulations.Global.BoundedSpectralData.mass_gap h)

/-- A Clay Yang--Mills solution gives the vacuum-isolated spectral-gap formulation. -/
theorem ClayYangMills.vacuum_gap
    (h : ClayYangMills) :
    ClayYangMills.Formulations.Global.VacuumGap :=
  ClayYangMills.iff_vacuum_gap.1 h

/-- Build the Clay Yang--Mills statement from the vacuum-isolated global form. -/
theorem ClayYangMills.of_vacuum_gap
    (h : ClayYangMills.Formulations.Global.VacuumGap) :
    ClayYangMills :=
  ClayYangMills.iff_vacuum_gap.2 h

/-- A Clay Yang--Mills solution gives the excitation-energy formulation. -/
theorem ClayYangMills.excitation_gap
    (h : ClayYangMills) :
    ClayYangMills.Formulations.Global.ExcitationGap :=
  ClayYangMills.iff_excitation_gap.1 h

/-- Build the Clay Yang--Mills statement from the excitation-energy global wording. -/
theorem ClayYangMills.of_excitation_gap
    (h : ClayYangMills.Formulations.Global.ExcitationGap) :
    ClayYangMills :=
  ClayYangMills.iff_excitation_gap.2 h

/-- A Clay Yang--Mills solution gives the Hamiltonian-spectral gap formulation. -/
theorem ClayYangMills.hamiltonian_gap
    (h : ClayYangMills) :
    ClayYangMills.Formulations.Global.HamiltonianGap :=
  ClayYangMills.iff_hamiltonian_gap.1 h

/-- Build the Clay Yang--Mills statement from the Hamiltonian-spectral global wording. -/
theorem ClayYangMills.of_hamiltonian_gap
    (h : ClayYangMills.Formulations.Global.HamiltonianGap) :
    ClayYangMills :=
  ClayYangMills.iff_hamiltonian_gap.2 h

/--
Specialize `ClayYangMills` to one compact simple gauge group.
-/
theorem ClayYangMills.for_group
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.FixedGroup G :=
  h G

/--
Unpacked fixed-group witness form of `ClayYangMills`.
-/
theorem ClayYangMills.exists_mass_gap
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ HasClayMassGap spectralData Δ := by
  rcases h.for_group G with ⟨theory, Δ, spectralData, hExist, hGap, _hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap⟩

/--
Unpacked fixed-group witness form including the Clay finite-mass condition.
-/
theorem ClayYangMills.exists_finite_mass
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ HasClayMassGap spectralData Δ ∧ FiniteClayMass spectralData :=
  h.for_group G

/--
Unpacked fixed-group witness form with the positive gap `Δ > 0` visible explicitly.
-/
theorem ClayYangMills.exists_positive_gap
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ 0 < Δ ∧ HasClayMassGap spectralData Δ :=
  (h.for_group G).exists_positive_gap

/--
Unpacked fixed-group witness form with the PDF's explicit “on `ℝ⁴`” wording.
-/
theorem ClayYangMills.exists_on_r4
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : ClayQuantumYangMillsTheoryOnFourDimensionalSpacetime G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ HasClayMassGap spectralData Δ :=
  h.exists_mass_gap G

/--
Unpacked fixed-group witness form with both the PDF's explicit “on `ℝ⁴`” wording and the
positive gap `Δ > 0` visible explicitly.
-/
theorem ClayYangMills.exists_positive_gap_on_r4
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : ClayQuantumYangMillsTheoryOnFourDimensionalSpacetime G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ 0 < Δ ∧ HasClayMassGap spectralData Δ := by
  rcases h.exists_on_r4 G with ⟨theory, Δ, spectralData, hExist, hGap⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap.pos, hGap⟩

/--
Unpacked fixed-group witness form in the PDF's “every excitation has energy at least `Δ`”
wording.
-/
theorem ClayYangMills.exists_excitation_gap
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧
          ClayExcitationGap spectralData Δ := by
  rcases (ClayYangMills.Formulations.FixedGroup.iff_excitation_gap G).1 (h.for_group G) with
    ⟨theory, Δ, spectralData, hExist, hGap, _hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap⟩

/--
Unpacked fixed-group witness form with the Hamiltonian spectral sentences from the PDF recorded
explicitly.
-/
theorem ClayYangMills.exists_hamiltonian_gap
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayExistence theory ∧ ClayHamiltonianGapConditions spectralData Δ := by
  rcases (ClayYangMills.Formulations.FixedGroup.iff_hamiltonian_gap G).1 (h.for_group G) with
    ⟨theory, Δ, spectralData, hExist, hGap, _hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap⟩

/--
Unpacked fixed-group witness form including the PDF's Wightman/Osterwalder--Schrader axiom
requirements explicitly.
-/
theorem ClayYangMills.exists_axioms
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayQuantumFieldTheoryAxioms theory ∧
          ClayExistence theory ∧ HasClayMassGap spectralData Δ := by
  rcases h.exists_mass_gap G with ⟨theory, Δ, spectralData, hExist, hGap⟩
  exact ⟨theory, Δ, spectralData, hExist.axioms, hExist, hGap⟩

/--
Unpacked fixed-group witness form including the PDF's local curvature-operator correspondence,
with the displayed example `Tr Fᵢⱼ Fₖₗ(x)`.
-/
theorem ClayYangMills.exists_local_operators
    (h : ClayYangMills)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : ClayHamiltonianSpectralData G theory),
        ClayLocalOperatorCorrespondence theory ∧
          (∀ i j k l : Fin 4,
            clay_trace_curvature_product_operator theory i j k l =
              theory.local_operators.op (trace_curvature_product G i j k l)) ∧
          (∃ f : SchwartzSpace,
            theory.local_operators.op
              (GaugeInvariantLocalPolynomial.curvature : GaugeInvariantLocalPolynomial G) f ≠ 0) ∧
          ClayExistence theory ∧ HasClayMassGap spectralData Δ := by
  rcases h.exists_mass_gap G with ⟨theory, Δ, spectralData, hExist, hGap⟩
  exact ⟨theory, Δ, spectralData, hExist.local_operator_correspondence,
    (by intro i j k l; rfl), hExist.exists_nonzero_curvature_operator,
    hExist, hGap⟩

/-- A witnessed spectral mass gap has no Hamiltonian spectrum in the open interval `(0, Δ)`. -/
theorem HasMassGapSpectrum.not_mem_open_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {Δ E : ℝ}
    (hGap : HasMassGapSpectrum G theory Δ)
    (hE : E ∈ spectrum ℝ theory.wightman.hamiltonian) :
    E ∉ Set.Ioo 0 Δ := by
  exact fun hInterval => Set.disjoint_left.mp hGap.2 hE hInterval

end MillenniumYangMills
