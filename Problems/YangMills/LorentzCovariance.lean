import Problems.YangMills.HamiltonianSpectrum
import Physlib.SpaceAndTime.SpaceTime.LorentzAction

namespace MillenniumYangMills

open MillenniumYangMillsDefs

/-!
# Yang--Mills Lorentz Covariance Data

This module records a Lorentz-covariance strengthening of the Yang--Mills mass-gap statement.
The extra datum relates the concrete Lorentz action on Schwartz functions to the abstract
Poincare action stored in `QuantumYangMillsTheory`.

The final theorems record how the Lorentz-covariant strengthening implies the Hamiltonian and
Clay Yang--Mills mass-gap formulations.
-/

/-- Schwartz test functions on four-dimensional spacetime in the Lorentz-covariance data. -/
@[reducible]
def LorentzSchwartzSpace : Type :=
  SchwartzMap (SpaceTime 3) ℝ

/-- The Lorentz action on four-dimensional Schwartz test functions. -/
noncomputable def lorentz_schwartz_action (Λ : LorentzGroup 3) :
    LorentzSchwartzSpace → LorentzSchwartzSpace :=
  SpaceTime.schwartzAction Λ

/-- Pointwise form of the Lorentz action on Schwartz test functions. -/
theorem lorentz_schwartz_action_apply
    (Λ : LorentzGroup 3) (η : LorentzSchwartzSpace) (x : SpaceTime 3) :
    lorentz_schwartz_action Λ η x = η (Λ⁻¹ • x) :=
  SpaceTime.schwartzAction_apply Λ η x

/-- Composition law for the Lorentz action on Schwartz test functions. -/
theorem lorentz_schwartz_action_mul
    (Λ₁ Λ₂ : LorentzGroup 3) (η : LorentzSchwartzSpace) :
    lorentz_schwartz_action Λ₂ (lorentz_schwartz_action Λ₁ η) =
      lorentz_schwartz_action (Λ₂ * Λ₁) η :=
  SpaceTime.schwartzAction_mul_apply Λ₁ Λ₂ η

/-- The Lorentz action on Schwartz test functions is injective. -/
theorem lorentz_schwartz_action_injective (Λ : LorentzGroup 3) :
    Function.Injective (lorentz_schwartz_action Λ) :=
  SpaceTime.schwartzAction_injective Λ

/-- The Lorentz action on Schwartz test functions is surjective. -/
theorem lorentz_schwartz_action_surjective (Λ : LorentzGroup 3) :
    Function.Surjective (lorentz_schwartz_action Λ) :=
  SpaceTime.schwartzAction_surjective Λ

/--
Data relating the concrete Lorentz action on Schwartz functions to the abstract Poincare action
used in the Wightman-style Yang--Mills package.

The map `test_function_realization` is explicit because the two spacetime models are different
Lean types: the Lorentz-action library uses `SpaceTime 3`, while the existing Yang--Mills
quantum-field-theory package uses `EuclideanSpace ℝ (Fin 4)` as `Spacetime`.
-/
structure LorentzCovarianceData (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) where
  /-- Embedding of Lorentz transformations into the theory's Poincare group. -/
  lorentz_to_poincare : LorentzGroup 3 → theory.wightman.poincare_group
  /-- Translation from Lorentz-test functions to the theory's test-function model. -/
  test_function_realization : LorentzSchwartzSpace → SchwartzSpace
  /-- The Lorentz action intertwines with the theory's Poincare action on tests. -/
  action_intertwines :
    ∀ (Λ : LorentzGroup 3) (η : LorentzSchwartzSpace),
      test_function_realization (lorentz_schwartz_action Λ η) =
        theory.wightman.action_on_tests (lorentz_to_poincare Λ) (test_function_realization η)

namespace LorentzCovarianceData

variable {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}

/--
Lorentz covariance of smeared field operators, transported through `LorentzCovarianceData` to the
Wightman covariance field already stored in the quantum field theory data.
-/
theorem field_operators_covariant
    (covarianceData : LorentzCovarianceData G theory)
    (Λ : LorentzGroup 3) (η : LorentzSchwartzSpace) :
    theory.field_operators (covarianceData.test_function_realization (lorentz_schwartz_action Λ η)) =
      conjugate_operator (theory.wightman.unitary_rep (covarianceData.lorentz_to_poincare Λ))
        (theory.field_operators (covarianceData.test_function_realization η)) := by
  rw [covarianceData.action_intertwines]
  exact theory.wightman.covariance (covarianceData.lorentz_to_poincare Λ) (covarianceData.test_function_realization η)

/--
Lorentz covariance of gauge-invariant local operators, transported through `LorentzCovarianceData`
to the local-operator covariance field already stored in the quantum field theory data.
-/
theorem local_operators_covariant
    (covarianceData : LorentzCovarianceData G theory)
    (p : GaugeInvariantLocalPolynomial G)
    (Λ : LorentzGroup 3) (η : LorentzSchwartzSpace) :
    (theory.local_operators.op p) (covarianceData.test_function_realization (lorentz_schwartz_action Λ η)) =
      conjugate_operator (theory.wightman.unitary_rep (covarianceData.lorentz_to_poincare Λ))
        ((theory.local_operators.op p) (covarianceData.test_function_realization η)) := by
  rw [covarianceData.action_intertwines]
  exact theory.local_operators_covariant (covarianceData.lorentz_to_poincare Λ) p
    (covarianceData.test_function_realization η)

end LorentzCovarianceData

/--
Yang--Mills existence and mass gap using an unbounded self-adjoint physical Hamiltonian and
Lorentz-covariance data for test functions.
-/
def ClayYangMills.Formulations.LorentzCovariant.FixedGroup
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : PhysicalHamiltonianSpectralData G theory)
      (_cov : LorentzCovarianceData G theory),
    ClayExistence theory ∧ HasPhysicalMassGap spectralData Δ ∧ FinitePhysicalMass spectralData

/-- The Lorentz-covariant construction contains the physical-Hamiltonian mass-gap data. -/
theorem ClayYangMills.Formulations.LorentzCovariant.FixedGroup.physical_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.LorentzCovariant.FixedGroup G →
      ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup G := by
  rintro ⟨theory, Δ, spectralData, _cov, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩

/--
For a fixed compact simple gauge group, the Lorentz-covariant construction determines the
Clay Yang--Mills existence-and-mass-gap statement.
-/
theorem ClayYangMills.Formulations.LorentzCovariant.FixedGroup.mass_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.LorentzCovariant.FixedGroup G →
      ClayYangMills.Formulations.FixedGroup G := by
  rintro ⟨theory, Δ, spectralData, _cov, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData.spectral_data, hExist, hGap.mass_gap, hFinite.finite_mass⟩

/-- Global compact-simple-gauge-group form of the Lorentz-covariant Yang--Mills statement. -/
def ClayYangMills.Formulations.LorentzCovariant.Global : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G],
    ClayYangMills.Formulations.LorentzCovariant.FixedGroup G

/--
Lorentz-covariant global Yang--Mills statement.

This is stronger than the Clay mass-gap statement: it asks for the same theory and mass gap,
plus an unbounded self-adjoint physical Hamiltonian package and Lorentz-covariance data for
test functions.
-/
def ClayYangMills.Formulations.LorentzCovariant.Statement : Prop :=
  ClayYangMills.Formulations.LorentzCovariant.Global

/--
For all compact simple gauge groups, the Lorentz-covariant formulation implies the
Clay global mass-gap statement.
-/
theorem ClayYangMills.Formulations.LorentzCovariant.Global.mass_gap :
    ClayYangMills.Formulations.LorentzCovariant.Global →
      ClayYangMills.Formulations.Global.MassGap := by
  intro h G
  exact (ClayYangMills.Formulations.LorentzCovariant.FixedGroup.mass_gap G) (h G)

/-- The Lorentz-covariant statement includes the physical-Hamiltonian global statement. -/
theorem ClayYangMills.Formulations.LorentzCovariant.Statement.hamiltonian :
    ClayYangMills.Formulations.LorentzCovariant.Statement →
      ClayYangMills.Formulations.PhysicalHamiltonian.Statement := by
  intro h G
  exact (ClayYangMills.Formulations.LorentzCovariant.FixedGroup.physical_gap G) (h G)

/--
The Lorentz-covariant statement gives the explicit `ℝ⁴` formulation with a positive gap `Δ > 0`.
-/
theorem ClayYangMills.Formulations.LorentzCovariant.Statement.positive_gap_on_four_dimensional_spacetime :
    ClayYangMills.Formulations.LorentzCovariant.Statement →
      ClayYangMills.Formulations.Global.PositiveGapOnFourDimensionalSpacetime :=
  fun h =>
    ClayYangMills.positive_gap_on_four_dimensional_spacetime
      (ClayYangMills.Formulations.LorentzCovariant.Global.mass_gap h)

/--
The Lorentz-covariant statement gives the Hamiltonian spectral conditions from the Clay statement:
zero vacuum energy, positive spectrum, and no spectrum in `(0, Δ)`.
-/
theorem ClayYangMills.Formulations.LorentzCovariant.Statement.hamiltonian_gap :
    ClayYangMills.Formulations.LorentzCovariant.Statement →
      ClayYangMills.Formulations.Global.HamiltonianGap :=
  fun h =>
    ClayYangMills.hamiltonian_gap
      (ClayYangMills.Formulations.LorentzCovariant.Global.mass_gap h)

/-- Specialize the global Lorentz-covariant statement to one compact simple gauge group. -/
theorem ClayYangMills.Formulations.LorentzCovariant.Statement.for_group
    (h : ClayYangMills.Formulations.LorentzCovariant.Statement)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.LorentzCovariant.FixedGroup G :=
  h G

/--
Unpacked fixed-group witness form exposing both extra pieces of structure: the self-adjoint
physical Hamiltonian package and the Lorentz-covariance data.
-/
theorem ClayYangMills.Formulations.LorentzCovariant.Statement.exists_gap
    (h : ClayYangMills.Formulations.LorentzCovariant.Statement)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : PhysicalHamiltonianSpectralData G theory)
      (covarianceData : LorentzCovarianceData G theory),
        ClayExistence theory ∧
          IsSelfAdjoint spectralData.hamiltonian ∧
          spectralData.spectrum_set = {E : ℝ | (E : ℂ) ∈ LinearPMap.spectrum spectralData.hamiltonian} ∧
          LinearPMap.spectrum spectralData.hamiltonian ⊆ Set.range Complex.ofReal ∧
          (∀ (Λ : LorentzGroup 3) (η : LorentzSchwartzSpace),
            covarianceData.test_function_realization (lorentz_schwartz_action Λ η) =
              theory.wightman.action_on_tests (covarianceData.lorentz_to_poincare Λ)
                (covarianceData.test_function_realization η)) ∧
          HasPhysicalMassGap spectralData Δ ∧
          FinitePhysicalMass spectralData := by
  rcases h.for_group G with ⟨theory, Δ, spectralData, covarianceData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, covarianceData, hExist, spectralData.hamiltonian_self_adjoint,
    spectralData.spectrum_eq_operator, spectralData.complex_spectrum_real, covarianceData.action_intertwines, hGap, hFinite⟩

end MillenniumYangMills
