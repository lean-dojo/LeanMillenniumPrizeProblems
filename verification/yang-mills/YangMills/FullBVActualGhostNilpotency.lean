import YangMills.FullBVColorJacobiContraction
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private theorem sum_four_rotate {I M : Type*} [Fintype I] [AddCommMonoid M]
    (F : I → I → I → I → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ j, ∑ k, ∑ l, ∑ i, F i j k l := by
  calc
    _ = ∑ j, ∑ i, ∑ k, ∑ l, F i j k l := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm

/-- Actual structure constants are skew in their two bracket inputs. -/
theorem color_skew_complex {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) :
    (structureConstant e a b c : ℂ) = -(structureConstant e a c b : ℂ) := by
  exact_mod_cast threeColor_antisymmetric B (e.basis a) (e.basis b) (e.basis c)

/-- The fixed first cubic term in the square of the actual ghost image is
zero by actual tensor Jacobi, after a cyclic ghost permutation. -/
theorem ghostQuadratic_contraction_zero {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        (ghostQuadratic e g b * ghostJet G c)) = 0 := by
  have he : (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        (ghostQuadratic e g b * ghostJet G c)) =
      (-((g : ℂ)^2 / 4)) •
        (∑ c : Fin G.dimension, ∑ d : Fin G.dimension, ∑ f : Fin G.dimension,
          colorJacobiCoefficient e a c d f •
            ((ghostJet G c * ghostJet G d) * ghostJet G f)) := by
    simp only [ghostQuadratic, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
    rw [sum_four_rotate]
    simp only [colorJacobiCoefficient, Finset.smul_sum, Finset.sum_smul, smul_smul]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.mul_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← ghostJet_cyclic c d f, color_skew_complex e a b c]
    congr 1
    ring
  rw [he, colorJacobi_ghost_contraction_zero, smul_zero]

/-- Full nonlinear ghost nilpotency for the same master action, with no
independent CE differential or nilpotency assumption. -/
theorem classicalLocalST_square_ghost {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (ghostJet G a)) = 0 := by
  rw [classicalLocalST_square_ghost_expansion]
  simp only [sub_eq_add_neg, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  rw [ghostQuadratic_contraction_zero, zero_add]
  have hs : (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        (ghostQuadratic e g c * ghostJet G b)) = 0 := by
    rw [Finset.sum_comm]
    have hn : (∑ c : Fin G.dimension, ∑ b : Fin G.dimension,
        ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          (ghostQuadratic e g c * ghostJet G b)) =
        -(∑ c : Fin G.dimension, ∑ b : Fin G.dimension,
          ((1 / 2 : ℂ) * (structureConstant e a c b : ℂ) * (g : ℂ)) •
            (ghostQuadratic e g c * ghostJet G b)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      rw [color_skew_complex e a b c]
      simp only [mul_neg, neg_mul]
      exact neg_smul ((1 / 2 : ℂ) * (structureConstant e a c b : ℂ) * (g : ℂ))
        (ghostQuadratic e g c * ghostJet G b)
    rw [hn, ghostQuadratic_contraction_zero, neg_zero]

  rw [hs, neg_zero]

end YangMills.FullBV
