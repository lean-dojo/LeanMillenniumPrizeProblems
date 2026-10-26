import Problems.YangMills.FullBVGaugeLinearCancellation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def gaugeQuadratic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (a : Fin G.dimension) : JetAlgebra G :=
  ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    ((structureConstant e a b c : ℂ) * (g : ℂ)) •
      (jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c)

theorem classicalLocalST_gaugeQuadratic {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g (gaugeQuadratic e g mu a) =
    ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((jet ⟨.inl (.ghost b), Pi.single mu 1⟩ + gaugeQuadratic e g mu b) * ghostJet G c -
          ghostQuadratic e g c * jet ⟨.inl (.gauge mu b), 0⟩) := by
  have hA (b : Fin G.dimension) :
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu b)) =
        jet ⟨.inl (.ghost b), Pi.single mu 1⟩ + gaugeQuadratic e g mu b :=
    master_characteristic_gauge e g mu b
  have hc (c : Fin G.dimension) :
      stCharacteristic (masterActionDensity e g) (.inl (.ghost c)) =
        -(ghostQuadratic e g c) := master_characteristic_ghost e g c
  unfold classicalLocalSTDensity
  conv_lhs => arg 2; unfold gaugeQuadratic
  simp only [localST_sum, localST_smul, localST_mul_jet, localST_jet,
    prolongedST, hA, hc, totalDerivatives_zero, parity_jet, ExternalLeg.parity,
    BasicField.fermionic, if_true, if_false]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hmem
  congr 1
  change (_ + (-(ghostQuadratic e g c)) * jet ⟨.inl (.gauge mu b), 0⟩) = _
  have hn : (-(ghostQuadratic e g c)) * jet ⟨.inl (.gauge mu b), 0⟩ =
      -(ghostQuadratic e g c * jet ⟨.inl (.gauge mu b), 0⟩) :=
    neg_mul (ghostQuadratic e g c) (jet ⟨.inl (.gauge mu b), 0⟩)
  rw [hn, sub_eq_add_neg]

/-- Actual same-action second gauge variation after cancellation of its
entire derivative (linear g) sector. Only the fixed quadratic-g Jacobi
residual remains; this theorem assumes no nilpotency. -/
theorem classicalLocalST_square_gauge_residual {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inl (.gauge mu a), 0⟩)) =
    ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((structureConstant e a b c : ℂ) * (g : ℂ)) •
        (gaugeQuadratic e g mu b * ghostJet G c -
          ghostQuadratic e g c * jet ⟨.inl (.gauge mu b), 0⟩) := by
  have hA : stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) =
      jet ⟨.inl (.ghost a), Pi.single mu 1⟩ + gaugeQuadratic e g mu a :=
    master_characteristic_gauge e g mu a
  have hc : stCharacteristic (masterActionDensity e g) (.inl (.ghost a)) =
      -(ghostQuadratic e g a) := master_characteristic_ghost e g a
  simp only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero, hA, localST_add]
  rw [← classicalLocalSTDensity, classicalLocalST_gaugeQuadratic]
  rw [hc, totalDerivatives_single_one]
  have hn : totalDerivative mu (-(ghostQuadratic e g a)) =
      -(totalDerivative mu (ghostQuadratic e g a)) := map_neg (totalDerivativeLinear mu) _
  rw [hn]
  rw [totalDerivative_ghostQuadratic]
  have hs : (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((jet ⟨.inl (.ghost b), Pi.single mu 1⟩ + gaugeQuadratic e g mu b) * ghostJet G c -
          ghostQuadratic e g c * jet ⟨.inl (.gauge mu b), 0⟩)) =
      (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a b c : ℂ) * (g : ℂ)) •
          (jet ⟨.inl (.ghost b), Pi.single mu 1⟩ * ghostJet G c)) +
      (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a b c : ℂ) * (g : ℂ)) •
          (gaugeQuadratic e g mu b * ghostJet G c -
            ghostQuadratic e g c * jet ⟨.inl (.gauge mu b), 0⟩)) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc'
    simp only [add_mul, sub_eq_add_neg, smul_add]
    abel
  rw [hs]
  abel

end YangMills.FullBV
