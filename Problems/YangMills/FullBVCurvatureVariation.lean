import Problems.YangMills.FullBVCurvatureJacobi
import Problems.YangMills.FullBVEvolutionaryDerivation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem classicalLocalST_gaugeFirst {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g (gaugeFirstJet G mu nu a) =
      totalDerivative mu (stCharacteristic (masterActionDensity e g) (.inl (.gauge nu a))) := by
  change localST (masterActionDensity e g) (jet ⟨.inl (.gauge nu a), Pi.single mu 1⟩) = _
  rw [localST_jet, totalDerivatives_single_one]

theorem classicalLocalST_gaugePotential {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g (gaugePotentialJet G mu a) =
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) := by
  exact localST_jet _ _ |>.trans (totalDerivatives_zero _)

/-- Actual evolutionary variation of the same gauge bracket polynomial. -/
theorem classicalLocalST_gluonBracket {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g (gluonBracketJet e mu nu a) =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (structureConstant e a b c : ℂ) •
          (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu b)) *
              gaugePotentialJet G nu c +
            gaugePotentialJet G mu b *
              stCharacteristic (masterActionDensity e g) (.inl (.gauge nu c))) := by
  simp only [gluonBracketJet, classicalLocalSTDensity, localST_sum, localST_smul]
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  congr 1
  change localST (masterActionDensity e g)
    (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.gauge nu c), 0⟩) = _
  rw [localST_mul_jet, localST_jet]
  simp only [ExternalLeg.parity, BasicField.fermionic, Bool.false_eq_true, if_false,
    prolongedST, totalDerivatives_zero]
  unfold gaugePotentialJet
  rw [← gaugeJet_commute mu b 0]

/-- The curvature varies by the SAME master-action characteristics and
ordinary descendant derivatives, without an independently specified gauge law. -/
theorem classicalLocalST_curvature_expansion {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g (nonabelianCurvatureJet e g mu nu a) =
      totalDerivative mu (stCharacteristic (masterActionDensity e g) (.inl (.gauge nu a))) -
      totalDerivative nu (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) +
      (g : ℂ) • ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (structureConstant e a b c : ℂ) •
          (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu b)) * gaugePotentialJet G nu c +
            gaugePotentialJet G mu b * stCharacteristic (masterActionDensity e g) (.inl (.gauge nu c))) := by
  unfold nonabelianCurvatureJet abelianCurvatureJet
  change localST (masterActionDensity e g) _ = _
  have hd (X Y : JetAlgebra G) : localST (masterActionDensity e g) (X - Y) =
      localST (masterActionDensity e g) X - localST (masterActionDensity e g) Y :=
    map_sub (localSTLinear _) X Y
  rw [localST_add, localST_smul, hd]
  rw [← classicalLocalSTDensity, ← classicalLocalSTDensity, ← classicalLocalSTDensity,
    classicalLocalST_gaugeFirst, classicalLocalST_gaugeFirst, classicalLocalST_gluonBracket]

/-- Fixed color skew and actual even gauge-jet commutation give the
linear ghost-derivative cancellation in the covariant curvature law. -/
theorem gauge_ghostDerivative_skew {B : InvariantForm G} (e : ColorFrame B)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      (structureConstant e a b c : ℂ) •
        (jet ⟨.inl (.ghost b), Pi.single mu 1⟩ * gaugePotentialJet G nu c)) =
      -(∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (structureConstant e a b c : ℂ) •
          (gaugePotentialJet G nu b * jet ⟨.inl (.ghost c), Pi.single mu 1⟩)) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro b hb
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro c hc
  rw [color_skew_complex e a c b]
  change (-(structureConstant e a b c : ℂ)) •
    (jet ⟨.inl (.ghost c), Pi.single mu 1⟩ * jet ⟨.inl (.gauge nu b), 0⟩) = _
  rw [← gaugeJet_commute nu b 0]
  change (-(structureConstant e a b c : ℂ)) •
      (jet ⟨.inl (.gauge nu b), 0⟩ * jet ⟨.inl (.ghost c), Pi.single mu 1⟩) =
    -((structureConstant e a b c : ℂ) •
      (jet ⟨.inl (.gauge nu b), 0⟩ * jet ⟨.inl (.ghost c), Pi.single mu 1⟩))
  exact neg_smul (structureConstant e a b c : ℂ)
    (jet ⟨.inl (.gauge nu b), 0⟩ * jet ⟨.inl (.ghost c), Pi.single mu 1⟩)

end YangMills.FullBV
