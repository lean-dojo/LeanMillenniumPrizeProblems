import Problems.YangMills.FullBVCurvatureEulerChannels

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem curvatureEuler_derivative_channels {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (gluonCurvatureDensity e g) =
      -(∑ mu : Fin 4, totalDerivative mu (nonabelianCurvatureJet e g mu rho d)) +
      (1 / 2 : ℂ) • (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
        nonabelianCurvatureJet e g mu nu a * curvatureGaugeZeroPartial e g mu nu rho a d) := by
  have hp (mu nu : Fin 4) (a : Fin G.dimension) :
      (1 / 4 : ℂ) • rightEuler (.inl (.gauge rho d))
        (nonabelianCurvatureJet e g mu nu a * nonabelianCurvatureJet e g mu nu a) =
      (-1 / 2 : ℂ) • (if nu = rho ∧ a = d then
        totalDerivative mu (nonabelianCurvatureJet e g mu nu a) else 0) +
      (1 / 2 : ℂ) • (if mu = rho ∧ a = d then
        totalDerivative nu (nonabelianCurvatureJet e g mu nu a) else 0) +
      (1 / 2 : ℂ) • (nonabelianCurvatureJet e g mu nu a *
        curvatureGaugeZeroPartial e g mu nu rho a d) := by
    rw [rightEuler_curvatureSquare_gauge]
    module
  unfold gluonCurvatureDensity
  simp only [rightEuler_sum, rightEuler_smul, hp, Finset.sum_add_distrib,
    smul_ite, smul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hs : (∑ nu : Fin 4, (1 / 2 : ℂ) •
      totalDerivative nu (nonabelianCurvatureJet e g rho nu d)) =
      ∑ nu : Fin 4, (-1 / 2 : ℂ) •
        totalDerivative nu (nonabelianCurvatureJet e g nu rho d) := by
    apply Finset.sum_congr rfl; intro nu hnu
    rw [nonabelianCurvature_skew e g rho nu d, totalDerivative_neg]
    module
  rw [hs]
  simp only [← Finset.smul_sum]
  module

/-- The actual algebraic curvature-partial channels assemble to the
connection commutator term with the SAME color tensor and coupling. -/
theorem curvatureZeroPartial_metric {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
      nonabelianCurvatureJet e g mu nu a * curvatureGaugeZeroPartial e g mu nu rho a d) =
      ((-2 : ℂ) * (g : ℂ)) • (∑ mu : Fin 4,
        colorPolynomialBracket e (gaugeColorFamily G mu)
          (fun a => nonabelianCurvatureJet e g mu rho a) d) := by
  have hex : (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
      nonabelianCurvatureJet e g mu nu a * curvatureGaugeZeroPartial e g mu nu rho a d) =
      (∑ nu : Fin 4, ∑ a : Fin G.dimension, ∑ c : Fin G.dimension,
        ((g : ℂ) * (structureConstant e a d c : ℂ)) •
          (nonabelianCurvatureJet e g rho nu a * gaugeColorFamily G nu c)) +
      (∑ mu : Fin 4, ∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
        ((g : ℂ) * (structureConstant e a b d : ℂ)) •
          (nonabelianCurvatureJet e g mu rho a * gaugeColorFamily G mu b)) := by
    unfold curvatureGaugeZeroPartial
    simp only [Finset.mul_sum, mul_smul_comm, mul_add, smul_add, smul_smul, Finset.smul_sum,
      mul_ite, mul_zero, smul_ite, smul_zero, Finset.sum_add_distrib, ite_and,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have hfirst (nu : Fin 4) :
      (∑ a : Fin G.dimension, ∑ c : Fin G.dimension,
        ((g : ℂ) * (structureConstant e a d c : ℂ)) •
          (nonabelianCurvatureJet e g rho nu a * gaugeColorFamily G nu c)) =
      (-(g : ℂ)) • colorPolynomialBracket e (gaugeColorFamily G nu)
        (fun a => nonabelianCurvatureJet e g nu rho a) d := by
    calc
      _ = ∑ a : Fin G.dimension, ∑ c : Fin G.dimension,
          ((structureConstant e a c d : ℂ) * (g : ℂ)) •
            (nonabelianCurvatureJet e g nu rho a * gaugeColorFamily G nu c) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro c hc
        rw [nonabelianCurvature_skew e g rho nu a, color_skew_complex e a d c]
        have hn (X Y : JetAlgebra G) : (-X)*Y = -(X*Y) := neg_mul X Y
        rw [hn]
        module
      _ = _ := rotatedGaugeColorContraction e g nu _ d
  have hsecond (mu : Fin 4) :
      (∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
        ((g : ℂ) * (structureConstant e a b d : ℂ)) •
          (nonabelianCurvatureJet e g mu rho a * gaugeColorFamily G mu b)) =
      (-(g : ℂ)) • colorPolynomialBracket e (gaugeColorFamily G mu)
        (fun a => nonabelianCurvatureJet e g mu rho a) d := by
    convert rotatedGaugeColorContraction e g mu (fun a => nonabelianCurvatureJet e g mu rho a) d using 1
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro b hb
    rw [mul_comm (g : ℂ)]
  rw [hex]
  simp only [hfirst,hsecond, ← Finset.smul_sum]
  module

/-- The complete actual curvature Euler equation, derived from its fixed
jet partials and all interaction channels, with no independent EOM witness. -/
theorem rightEuler_curvature_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (gluonCurvatureDensity e g) =
      -(∑ mu : Fin 4,
        (totalDerivative mu (nonabelianCurvatureJet e g mu rho d) +
          (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G mu)
            (fun a => nonabelianCurvatureJet e g mu rho a) d)) := by
  rw [curvatureEuler_derivative_channels, curvatureZeroPartial_metric]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  module

end YangMills.FullBV
