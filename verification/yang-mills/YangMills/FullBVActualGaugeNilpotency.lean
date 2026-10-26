import YangMills.FullBVGaugeSquareExpansion
import YangMills.FullBVMixedJacobiContraction
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private theorem sum_three_left {I M : Type*} [Fintype I] [AddCommMonoid M]
    (F : I → I → I → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ j, ∑ k, ∑ i, F i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, F i j k := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

private theorem sum_four_left {I M : Type*} [Fintype I] [AddCommMonoid M]
    (F : I → I → I → I → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ j, ∑ k, ∑ l, ∑ i, F i j k l := by
  calc
    _ = ∑ j, ∑ i, ∑ k, ∑ l, F i j k l := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_three_left _

def iteratedGaugeCoefficient {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) : ℂ :=
  ∑ r : Fin G.dimension,
    (structureConstant e a r d : ℂ) * (structureConstant e r b c : ℂ)

theorem iteratedGaugeCoefficient_eq {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) :
    iteratedGaugeCoefficient e a b c d = -(colorJacobiCoefficient e a d b c) := by
  unfold iteratedGaugeCoefficient colorJacobiCoefficient
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [color_skew_complex e a r d]
  ring

theorem gaugeQuadratic_first_contraction {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    (∑ r : Fin G.dimension, ∑ d : Fin G.dimension,
      ((structureConstant e a r d : ℂ) * (g : ℂ)) •
        (gaugeQuadratic e g mu r * ghostJet G d)) =
      ((g : ℂ)^2) • (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
        iteratedGaugeCoefficient e a b c d • mixedGhostWord G mu b c d) := by
  simp only [gaugeQuadratic, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  rw [sum_four_left, sum_three_left]
  simp only [iteratedGaugeCoefficient, mixedGhostWord, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  ring

theorem gaugeQuadratic_second_contraction {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ r : Fin G.dimension,
      ((structureConstant e a b r : ℂ) * (g : ℂ)) •
        (ghostQuadratic e g r * jet ⟨.inl (.gauge mu b), 0⟩)) =
      ((g : ℂ)^2 / 2) • (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
        colorJacobiCoefficient e a b c d • mixedGhostWord G mu b c d) := by
  simp only [ghostQuadratic, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [sum_three_left]
  simp only [colorJacobiCoefficient, mixedGhostWord, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← gaugeJet_commute mu b 0 (ghostJet G c * ghostJet G d)]
  rw [← mul_assoc]
  congr 1
  ring
  exact (mul_assoc _ _ _).symm

/-- Full nonlinear gauge nilpotency for the actual master action. Its
linear-g cancellation and quadratic-g Jacobi contraction are both proved
on the same jet polynomials and actual G color tensors. -/
theorem classicalLocalST_square_gauge {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inl (.gauge mu a), 0⟩)) = 0 := by
  rw [classicalLocalST_square_gauge_residual]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [gaugeQuadratic_first_contraction, gaugeQuadratic_second_contraction,
    colorJacobi_mixed_contraction]
  simp only [iteratedGaugeCoefficient_eq, smul_smul]
  module

end YangMills.FullBV
