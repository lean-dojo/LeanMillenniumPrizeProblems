import Problems.YangMills.FullBVGaugeFermion

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem parity_gaugeGhostProduct (mu : Fin 4) (b c : Fin G.dimension) :
    parity (jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c) =
      -(jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c) := by
  rw [parity_mul, parity_jet, parity_jet]
  simp only [ExternalLeg.parity, BasicField.fermionic, Bool.false_eq_true, if_false, if_true]
  exact mul_neg (jet ⟨.inl (.gauge mu b), 0⟩) (ghostJet G c)

theorem parity_gaugeQuadratic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (a : Fin G.dimension) :
    parity (gaugeQuadratic e g mu a) = -(gaugeQuadratic e g mu a) := by
  unfold gaugeQuadratic
  simp only [map_sum, map_smul, parity_gaugeGhostProduct]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  exact smul_neg ((structureConstant e a b c : ℂ) * (g : ℂ))
    (jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c)

theorem parity_gaugeCharacteristic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (a : Fin G.dimension) :
    parity (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) =
      -(stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) := by
  rw [master_characteristic_gauge]
  change parity (jet ⟨.inl (.ghost a), Pi.single mu 1⟩ + gaugeQuadratic e g mu a) =
    -(jet ⟨.inl (.ghost a), Pi.single mu 1⟩ + gaugeQuadratic e g mu a)
  rw [map_add, parity_gaugeQuadratic, parity_jet]
  simp [ExternalLeg.parity, BasicField.fermionic, neg_add, add_comm]

/-- The fixed current whose divergence changes the gauge-fermion ghost
term into the actual physical ghost density. -/
def gaugeFermionCurrent {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) (mu : Fin 4) : JetAlgebra G :=
  stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) * antighostJet G a

theorem physicalGhost_current_point {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) (mu : Fin 4) :
    jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
        stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) +
      totalDerivative mu (gaugeFermionCurrent e g a mu) =
        totalDerivative mu (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) *
          antighostJet G a := by
  have hc := oddJet_mul_polynomial (G := G)
    ⟨⟨.inl (.antighost a), Pi.single mu 1⟩, by rfl⟩
    (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))
  rw [parity_gaugeCharacteristic] at hc
  have hc' : jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) =
      -(stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) *
        jet ⟨.inl (.antighost a), Pi.single mu 1⟩) := by
    change jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) =
      (-stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) *
        jet ⟨.inl (.antighost a), Pi.single mu 1⟩ at hc
    exact hc.trans (neg_mul
      (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))
      (jet ⟨.inl (.antighost a), Pi.single mu 1⟩))
  unfold gaugeFermionCurrent antighostJet
  rw [totalDerivative_mul_jet_ordinary, totalDerivative_jet]
  simp only [Jet.shift, zero_add]
  rw [hc']
  abel

def gaugeFixedGhostAuxiliaryDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    JetAlgebra G :=
  ∑ a : Fin G.dimension,
    ((1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a) +
      (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a) +
      ∑ mu : Fin 4, jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
        stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))

/-- Exact fixed-current decomposition of the full gauge-fixing, B and
physical-ghost sector as the actual ST variation of the fixed fermion.
No divergence class or action-invariance hypothesis is assumed. -/
theorem gaugeFixedSector_gaugeFermion {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    gaugeFixedGhostAuxiliaryDensity e g +
      (∑ a : Fin G.dimension, ∑ mu : Fin 4, totalDerivative mu (gaugeFermionCurrent e g a mu)) =
      classicalLocalSTDensity e g (gaugeFermionDensity G) := by
  rw [classicalLocalST_gaugeFermion]
  unfold gaugeFixedGhostAuxiliaryDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hp : (∑ mu : Fin 4, jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) +
      (∑ mu : Fin 4, totalDerivative mu (gaugeFermionCurrent e g a mu)) =
      ghostDivergence e g a * antighostJet G a := by
    rw [← Finset.sum_add_distrib]
    simp only [physicalGhost_current_point]
    exact (Finset.sum_mul _ _ _).symm
  convert congrArg (fun Z : JetAlgebra G =>
    (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a) +
      (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a) + Z) hp using 1; abel

/-- This ghost sector is exactly the engine's free ghost kinetic density
plus its actual physical ghost interaction vertices, with the same f and g. -/
theorem physicalGhost_sector_same_vertices {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    (∑ mu : Fin 4, ∑ a : Fin G.dimension,
      jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
        stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) =
      (∑ mu : Fin 4, ∑ a : Fin G.dimension,
        jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.ghost a), Pi.single mu 1⟩) +
      densityOfVertices g (physicalGhostVertices e) := by
  rw [physicalGhostDensity_expansion]
  simp only [master_characteristic_gauge, mul_add, Finset.mul_sum, mul_smul_comm,
    Finset.sum_add_distrib, mul_assoc]

end YangMills.FullBV
