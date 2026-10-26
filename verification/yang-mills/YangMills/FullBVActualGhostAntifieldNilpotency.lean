import YangMills.FullBVOddCovariantEvolution
noncomputable section
set_option maxHeartbeats 2600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Actual compact c† image, using the SAME covariant derivative and K. -/
theorem localSTColor_ghostAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    localSTColor (masterActionDensity e g) (ghostAntifieldFamily G) =
      -(∑ mu : Fin 4, covariantColorDerivative e g mu (shiftedGaugeAntifieldFamily G mu)) +
        (g : ℂ) • colorPolynomialBracket e (ghostAntifieldFamily G) (ghostColorFamily G) := by
  funext a
  change localST (masterActionDensity e g) (jet ⟨.inr (.ghost a),0⟩) = _
  rw [localST_jet,totalDerivatives_zero,master_characteristic_ghostAntifield_covariant]
  simp only [Pi.add_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,
    covariantColorDerivative,Finset.sum_add_distrib,← Finset.smul_sum]
  module

/-- Actual full interacting ghost-antifield nilpotency. Covariant divergence
terms cancel by the proved SAME-action Noether identity, and the remaining
source/ghost terms cancel by actual G two-ghost Jacobi. -/
theorem localSTColor_square_ghostAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    localSTColor (masterActionDensity e g)
      (localSTColor (masterActionDensity e g) (ghostAntifieldFamily G)) = 0 := by
  have hA (a : Fin G.dimension) : parity (ghostAntifieldFamily G a) = ghostAntifieldFamily G a := by
    simpa only [ghostAntifieldFamily,ExternalLeg.parity,BasicField.fermionic,
      Bool.not_true,Bool.false_eq_true,if_false] using
      parity_jet (G := G) ⟨.inr (.ghost a),0⟩
  have hd (mu : Fin 4) := localSTColor_covariantDerivative_odd e g mu
    (shiftedGaugeAntifieldFamily G mu) (curvatureEulerFamily e g mu)
    (parity_shiftedGaugeAntifield mu) (localSTColor_shiftedGaugeAntifield e g mu)
  rw [localSTColor_ghostAntifield,localSTColor_add,localSTColor_neg,localSTColor_sum,
    localSTColor_smul,localSTColor_bracket_even e _ (parity_masterActionDensity e g) _ _ hA,
    localSTColor_ghostAntifield,localSTColor_ghost]
  simp only [hd,Finset.sum_add_distrib,← Finset.smul_sum,curvatureEuler_Noether,zero_add,
    colorPolynomialBracket_add_left,colorPolynomialBracket_neg_left,
    colorPolynomialBracket_sum_left]
  funext a
  simp only [Pi.neg_apply,Pi.add_apply,Pi.smul_apply,Pi.zero_apply,
    colorPolynomialBracket_add_left,colorPolynomialBracket_neg_left,
    colorPolynomialBracket_sum_left,colorPolynomialBracket_smul_left,
    colorPolynomialBracket_smul_right,Finset.sum_apply]
  rw [colorPolynomialBracket_twoGhost_Jacobi e (ghostAntifieldFamily G)]
  simp only [Pi.smul_apply]
  module

theorem classicalLocalST_square_ghostAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inr (.ghost a),0⟩)) = 0 :=
  congrFun (localSTColor_square_ghostAntifield e g) a

end YangMills.FullBV
