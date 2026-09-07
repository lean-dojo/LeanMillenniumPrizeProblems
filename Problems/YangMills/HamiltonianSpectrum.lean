import Problems.YangMills.Millennium
import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SelfAdjoint

namespace MillenniumYangMills

open MillenniumYangMillsDefs

/-!
# Yang--Mills Physical Hamiltonian Spectrum

This module adds an unbounded self-adjoint physical-Hamiltonian strengthening of the Yang--Mills
mass-gap statement.  The imported Physlib operator theory supplies the `LinearPMap` spectrum used
to connect the physical Hamiltonian with a real spectral set.

The final theorems record how this strengthened Hamiltonian formulation implies the
Clay Yang--Mills mass-gap statements.
-/

/--
Physical Hamiltonian spectral data for a Yang--Mills quantum field theory.

The Hamiltonian is modeled as a partially-defined complex-linear operator on a complex Hilbert
space, matching the usual unbounded self-adjoint operator setting.  The real spectral set used in
the Clay mass-gap statement is tied to the complex operator spectrum by `spectrum_eq_operator`.
-/
structure PhysicalHamiltonianSpectralData (G : Type) [CompactSimpleGaugeGroup G]
    (theory : QuantumYangMillsTheory G) where
  /-- The physical Hilbert space used for the unbounded Hamiltonian model. -/
  physical_hilbert_space : Type
  /-- Additive normed group structure on the physical Hilbert space. -/
  [normed_add_comm_group : NormedAddCommGroup physical_hilbert_space]
  /-- Complex Hilbert-space structure. -/
  [inner_product_space : InnerProductSpace ℂ physical_hilbert_space]
  /-- Completeness of the physical Hilbert space. -/
  [complete_space : CompleteSpace physical_hilbert_space]
  /-- The physical Hamiltonian as an unbounded complex-linear operator. -/
  hamiltonian : physical_hilbert_space →ₗ.[ℂ] physical_hilbert_space
  /-- The physical Hamiltonian is self-adjoint. -/
  hamiltonian_self_adjoint : IsSelfAdjoint hamiltonian
  /-- Realization of the Wightman real Hilbert space inside the physical complex Hilbert space. -/
  state_realization : theory.hilbert_space → physical_hilbert_space
  /-- The state realization preserves norms. -/
  state_realization_norm : ∀ ψ : theory.hilbert_space, ‖state_realization ψ‖ = ‖ψ‖
  /-- The physical vacuum vector in the complex Hilbert-space model. -/
  physical_vacuum : physical_hilbert_space
  /-- The Wightman vacuum is realized as the physical vacuum. -/
  state_realization_vacuum : state_realization theory.wightman.vacuum = physical_vacuum
  /-- The physical vacuum lies in the domain of the unbounded Hamiltonian. -/
  physical_vacuum_mem_domain : physical_vacuum ∈ hamiltonian.domain
  /-- The physical vacuum is a zero-energy vector for the unbounded Hamiltonian. -/
  physical_vacuum_zero_energy : hamiltonian ⟨physical_vacuum, physical_vacuum_mem_domain⟩ = 0
  /-- The real physical spectrum used in the Clay mass-gap statement. -/
  spectrum_set : Set ℝ
  /-- Agreement between the real physical spectrum and the complex operator spectrum. -/
  spectrum_eq_operator :
    spectrum_set = {E : ℝ | (E : ℂ) ∈ LinearPMap.spectrum hamiltonian}
  /-- Agreement with the Hamiltonian spectrum carried by the Wightman realization.

  This compatibility prevents the physical spectrum from being an unrelated set chosen only to
  satisfy a gap predicate. -/
  spectrum_eq_wightman : spectrum_set = spectrum ℝ theory.wightman.hamiltonian
  /-- Positive-energy condition for the physical spectrum. -/
  positive_energy : ∀ E : ℝ, E ∈ spectrum_set → 0 ≤ E
  /-- The vacuum energy `0` belongs to the physical spectrum. -/
  vacuum_energy_zero : 0 ∈ spectrum_set

attribute [instance] PhysicalHamiltonianSpectralData.normed_add_comm_group
attribute [instance] PhysicalHamiltonianSpectralData.inner_product_space
attribute [instance] PhysicalHamiltonianSpectralData.complete_space

namespace PhysicalHamiltonianSpectralData

variable {G : Type} [CompactSimpleGaugeGroup G] {theory : QuantumYangMillsTheory G}

/-- Membership in the real physical spectrum is membership in the complex operator spectrum. -/
theorem mem_spectrum_set_iff (spectralData : PhysicalHamiltonianSpectralData G theory) (E : ℝ) :
    E ∈ spectralData.spectrum_set ↔ (E : ℂ) ∈ LinearPMap.spectrum spectralData.hamiltonian := by
  rw [spectralData.spectrum_eq_operator]
  rfl

/-- The spectrum of the unbounded self-adjoint Hamiltonian is real. -/
theorem complex_spectrum_real (spectralData : PhysicalHamiltonianSpectralData G theory) :
    LinearPMap.spectrum spectralData.hamiltonian ⊆ Set.range Complex.ofReal :=
  LinearPMap.IsSelfAdjoint.spectrum_real spectralData.hamiltonian_self_adjoint

/-- The physical vacuum has the same unit norm as the Wightman vacuum. -/
theorem physical_vacuum_norm_one (spectralData : PhysicalHamiltonianSpectralData G theory) :
    ‖spectralData.physical_vacuum‖ = 1 := by
  rw [← spectralData.state_realization_vacuum]
  exact (spectralData.state_realization_norm theory.wightman.vacuum).trans theory.wightman.vacuum_norm_one

/-- The physical vacuum is a zero-energy vector for the unbounded Hamiltonian. -/
theorem physical_vacuum_has_zero_energy (spectralData : PhysicalHamiltonianSpectralData G theory) :
    spectralData.hamiltonian ⟨spectralData.physical_vacuum, spectralData.physical_vacuum_mem_domain⟩ = 0 :=
  spectralData.physical_vacuum_zero_energy

/-- The real physical spectrum is nonnegative. -/
theorem spectrum_set_nonnegative (spectralData : PhysicalHamiltonianSpectralData G theory) :
    spectralData.spectrum_set ⊆ Set.Ici 0 := by
  intro E hE
  exact spectralData.positive_energy E hE

/--
The unbounded physical-Hamiltonian package supplies the PDF spectral data used by the main
Yang--Mills statement in `Problems.YangMills.Millennium`.
-/
def spectral_data (spectralData : PhysicalHamiltonianSpectralData G theory) :
    ClayHamiltonianSpectralData G theory :=
  { spectrum_set := spectralData.spectrum_set
    spectrum_eq_hamiltonian := spectralData.spectrum_eq_wightman
    positive_energy := spectralData.positive_energy
    vacuum_energy_zero := spectralData.vacuum_energy_zero
    vacuum_zero_energy := theory.wightman.is_vacuum
    wightman_hamiltonian_self_adjoint := theory.wightman.is_hamiltonian_self_adjoint
    wightman_hamiltonian_positive := theory.wightman.is_hamiltonian_positive }

end PhysicalHamiltonianSpectralData

/-- Mass gap stated using unbounded physical-Hamiltonian spectral data. -/
def HasPhysicalMassGap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : PhysicalHamiltonianSpectralData G theory)
    (Δ : ℝ) : Prop :=
  Δ > 0 ∧ Disjoint spectralData.spectrum_set (Set.Ioo 0 Δ)

/-- Finite mass stated using unbounded physical-Hamiltonian spectral data. -/
def FinitePhysicalMass {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : PhysicalHamiltonianSpectralData G theory) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, HasPhysicalMassGap spectralData Δ → Δ ≤ m

/--
Hamiltonian spectral conditions read directly from the unbounded physical Hamiltonian:
self-adjointness, real spectrum, positive energy, zero vacuum energy, and a positive open
spectral gap.
-/
def PhysicalHamiltonianGapConditions {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} (spectralData : PhysicalHamiltonianSpectralData G theory)
    (Δ : ℝ) : Prop :=
  IsSelfAdjoint spectralData.hamiltonian ∧
    LinearPMap.spectrum spectralData.hamiltonian ⊆ Set.range Complex.ofReal ∧
    spectralData.physical_vacuum ∈ spectralData.hamiltonian.domain ∧
    spectralData.hamiltonian ⟨spectralData.physical_vacuum, spectralData.physical_vacuum_mem_domain⟩ = 0 ∧
    (∀ E : ℝ, E ∈ spectralData.spectrum_set → 0 ≤ E) ∧
    0 ∈ spectralData.spectrum_set ∧
    Δ > 0 ∧ Disjoint spectralData.spectrum_set (Set.Ioo 0 Δ)

/-- The physical-Hamiltonian gap is a Clay spectral mass gap for the same real spectrum. -/
theorem HasPhysicalMassGap.mass_gap {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : PhysicalHamiltonianSpectralData G theory}
    {Δ : ℝ} :
    HasPhysicalMassGap spectralData Δ → HasClayMassGap spectralData.spectral_data Δ := by
  intro hGap
  exact hGap

/-- A physical-Hamiltonian mass gap supplies the unbounded-Hamiltonian spectral conditions. -/
theorem HasPhysicalMassGap.hamiltonian_conditions
    {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : PhysicalHamiltonianSpectralData G theory}
    {Δ : ℝ} (hGap : HasPhysicalMassGap spectralData Δ) :
    PhysicalHamiltonianGapConditions spectralData Δ :=
  ⟨spectralData.hamiltonian_self_adjoint, spectralData.complex_spectrum_real, spectralData.physical_vacuum_mem_domain,
    spectralData.physical_vacuum_zero_energy, spectralData.positive_energy, spectralData.vacuum_energy_zero,
    hGap.1, hGap.2⟩

/-- The physical-Hamiltonian finite-mass bound is the corresponding Clay finite-mass bound. -/
theorem FinitePhysicalMass.finite_mass {G : Type} [CompactSimpleGaugeGroup G]
    {theory : QuantumYangMillsTheory G} {spectralData : PhysicalHamiltonianSpectralData G theory} :
    FinitePhysicalMass spectralData → FiniteClayMass spectralData.spectral_data := by
  rintro ⟨m, hm_pos, hm_bound⟩
  exact ⟨m, hm_pos, fun Δ hGap => hm_bound Δ hGap⟩

/--
Yang--Mills existence and mass gap using an unbounded self-adjoint physical Hamiltonian.
-/
def ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup
    (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : PhysicalHamiltonianSpectralData G theory),
    ClayExistence theory ∧ HasPhysicalMassGap spectralData Δ ∧ FinitePhysicalMass spectralData

/--
For a fixed compact simple gauge group, the physical-Hamiltonian construction determines the
Clay Yang--Mills existence-and-mass-gap statement.
-/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup.mass_gap
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup G →
      ClayYangMills.Formulations.FixedGroup G := by
  rintro ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData.spectral_data, hExist, hGap.mass_gap, hFinite.finite_mass⟩

/--
Unpacked fixed-group witness form exposing the self-adjoint physical Hamiltonian and its real
spectrum.
-/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup.exists_gap
    {G : Type} [CompactSimpleGaugeGroup G]
    (h : ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup G) :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : PhysicalHamiltonianSpectralData G theory),
        ClayExistence theory ∧
          IsSelfAdjoint spectralData.hamiltonian ∧
          spectralData.spectrum_set = {E : ℝ | (E : ℂ) ∈ LinearPMap.spectrum spectralData.hamiltonian} ∧
          LinearPMap.spectrum spectralData.hamiltonian ⊆ Set.range Complex.ofReal ∧
          HasPhysicalMassGap spectralData Δ ∧
          FinitePhysicalMass spectralData := by
  rcases h with ⟨theory, Δ, spectralData, hExist, hGap, hFinite⟩
  exact ⟨theory, Δ, spectralData, hExist, spectralData.hamiltonian_self_adjoint, spectralData.spectrum_eq_operator,
    spectralData.complex_spectrum_real, hGap, hFinite⟩

/-- Global compact-simple-gauge-group form of the physical-Hamiltonian Yang--Mills statement. -/
def ClayYangMills.Formulations.PhysicalHamiltonian.Global : Prop :=
  ∀ (G : Type) [CompactSimpleGaugeGroup G], ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup G

/--
Physical-Hamiltonian global Yang--Mills statement: for every compact simple gauge group, construct a
Yang--Mills theory whose physical Hamiltonian is an unbounded self-adjoint operator with a positive
spectral mass gap.
-/
def ClayYangMills.Formulations.PhysicalHamiltonian.Statement : Prop :=
  ClayYangMills.Formulations.PhysicalHamiltonian.Global

/--
For all compact simple gauge groups, the physical-Hamiltonian formulation implies the
Clay global mass-gap statement.
-/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.Global.mass_gap :
    ClayYangMills.Formulations.PhysicalHamiltonian.Global →
      ClayYangMills.Formulations.Global.MassGap := by
  intro h G
  exact (ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup.mass_gap G) (h G)

/--
The physical-Hamiltonian statement gives the explicit `ℝ⁴` formulation with a positive
gap `Δ > 0`.
-/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.Statement.positive_gap_on_four_dimensional_spacetime :
    ClayYangMills.Formulations.PhysicalHamiltonian.Statement →
      ClayYangMills.Formulations.Global.PositiveGapOnFourDimensionalSpacetime :=
  fun h =>
    ClayYangMills.positive_gap_on_four_dimensional_spacetime
      (ClayYangMills.Formulations.PhysicalHamiltonian.Global.mass_gap h)

/--
The physical-Hamiltonian statement gives the Hamiltonian spectral conditions from the Clay statement:
zero vacuum energy, positive spectrum, and no spectrum in `(0, Δ)`.
-/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.Statement.hamiltonian_gap :
    ClayYangMills.Formulations.PhysicalHamiltonian.Statement →
      ClayYangMills.Formulations.Global.HamiltonianGap :=
  fun h =>
    ClayYangMills.hamiltonian_gap
      (ClayYangMills.Formulations.PhysicalHamiltonian.Global.mass_gap h)

/-- Specialize the global physical-Hamiltonian statement to one compact simple gauge group. -/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.Statement.for_group
    (h : ClayYangMills.Formulations.PhysicalHamiltonian.Statement)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ClayYangMills.Formulations.PhysicalHamiltonian.FixedGroup G :=
  h G

/--
Unpacked fixed-group witness form exposing the self-adjoint physical Hamiltonian and its real
spectrum.
-/
theorem ClayYangMills.Formulations.PhysicalHamiltonian.Statement.exists_gap
    (h : ClayYangMills.Formulations.PhysicalHamiltonian.Statement)
    (G : Type) [CompactSimpleGaugeGroup G] :
    ∃ (theory : QuantumYangMillsTheory G) (Δ : ℝ)
      (spectralData : PhysicalHamiltonianSpectralData G theory),
        ClayExistence theory ∧
          IsSelfAdjoint spectralData.hamiltonian ∧
          spectralData.spectrum_set = {E : ℝ | (E : ℂ) ∈ LinearPMap.spectrum spectralData.hamiltonian} ∧
          LinearPMap.spectrum spectralData.hamiltonian ⊆ Set.range Complex.ofReal ∧
          HasPhysicalMassGap spectralData Δ ∧
          FinitePhysicalMass spectralData :=
  (h.for_group G).exists_gap

/-!
## No placeholder theorem

Earlier versions of this file ended with `theorem clay_prize_yang_mills : ClayYangMills := by
sorry`.  It has been removed: `ClayYangMills` is not a faithful statement of the Clay problem (see
the warning at the top of `Problems.YangMills.Quantum`), so a proof of it would not represent
progress on Yang–Mills existence and mass gap.  The registry records the problem as
`statement_incomplete`.
-/

end MillenniumYangMills
