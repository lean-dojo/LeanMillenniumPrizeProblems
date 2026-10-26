import Problems.YangMills.FullBVCurvatureVariation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

abbrev ColorPolynomial (G : CompactSimpleGaugeGroup) := Fin G.dimension → JetAlgebra G

def colorPolynomialBracket {B : InvariantForm G} (e : ColorFrame B)
    (X Y : ColorPolynomial G) (a : Fin G.dimension) : JetAlgebra G :=
  ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    (structureConstant e a b c : ℂ) • (X b * Y c)

theorem colorPolynomialBracket_add_left {B : InvariantForm G} (e : ColorFrame B)
    (X Y Z : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e (X+Y) Z a =
      colorPolynomialBracket e X Z a + colorPolynomialBracket e Y Z a := by
  simp only [colorPolynomialBracket, Pi.add_apply, add_mul, smul_add, Finset.sum_add_distrib]
theorem colorPolynomialBracket_add_right {B : InvariantForm G} (e : ColorFrame B)
    (X Y Z : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e X (Y+Z) a =
      colorPolynomialBracket e X Y a + colorPolynomialBracket e X Z a := by
  simp only [colorPolynomialBracket, Pi.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
theorem colorPolynomialBracket_smul_left {B : InvariantForm G} (e : ColorFrame B)
    (z : ℂ) (X Y : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e (z • X) Y a = z • colorPolynomialBracket e X Y a := by
  simp only [colorPolynomialBracket, Pi.smul_apply, smul_mul_assoc,
    smul_comm (_ : ℂ) z, Finset.smul_sum]
theorem colorPolynomialBracket_smul_right {B : InvariantForm G} (e : ColorFrame B)
    (z : ℂ) (X Y : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e X (z • Y) a = z • colorPolynomialBracket e X Y a := by
  simp only [colorPolynomialBracket, Pi.smul_apply, mul_smul_comm,
    smul_comm (_ : ℂ) z, Finset.smul_sum]

/-- Ordinary total differentiation of the actual coefficient bracket. -/
theorem totalDerivative_colorPolynomialBracket {B : InvariantForm G} (e : ColorFrame B)
    (mu : Fin 4) (X Y : ColorPolynomial G) (a : Fin G.dimension) :
    totalDerivative mu (colorPolynomialBracket e X Y a) =
      colorPolynomialBracket e (fun b => totalDerivative mu (X b)) Y a +
      colorPolynomialBracket e X (fun c => totalDerivative mu (Y c)) a := by
  simp only [colorPolynomialBracket, totalDerivative_sum, totalDerivative_smul,
    totalDerivative_mul, smul_add, Finset.sum_add_distrib]

theorem colorPolynomialBracket_skew_of_commute {B : InvariantForm G} (e : ColorFrame B)
    (X Y : ColorPolynomial G) (commute : ∀ b c, X b * Y c = Y c * X b)
    (a : Fin G.dimension) :
    colorPolynomialBracket e X Y a = -colorPolynomialBracket e Y X a := by
  unfold colorPolynomialBracket
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro b hb
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro c hc
  rw [color_skew_complex e a c b, commute c b]
  exact neg_smul (structureConstant e a b c : ℂ) (Y b * X c)

private theorem sum4_left {I M : Type*} [Fintype I] [AddCommMonoid M]
    (f : I → I → I → I → M) :
    (∑ r, ∑ c, ∑ b, ∑ d, f b c d r) = ∑ b, ∑ c, ∑ d, ∑ r, f b c d r := by
  calc
    _ = ∑ r, ∑ b, ∑ c, ∑ d, f b c d r := by
      apply Finset.sum_congr rfl; intro r hr
      exact Finset.sum_comm
    _ = ∑ b, ∑ r, ∑ c, ∑ d, f b c d r := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ r, ∑ d, f b c d r := by
      apply Finset.sum_congr rfl; intro b hb
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro b hb
      apply Finset.sum_congr rfl; intro c hc
      exact Finset.sum_comm

private theorem sum4_middle {I M : Type*} [Fintype I] [AddCommMonoid M]
    (f : I → I → I → I → M) :
    (∑ b, ∑ r, ∑ c, ∑ d, f b c d r) = ∑ b, ∑ c, ∑ d, ∑ r, f b c d r := by
  apply Finset.sum_congr rfl; intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c hc
  exact Finset.sum_comm

private theorem sum4_right {I M : Type*} [Fintype I] [AddCommMonoid M]
    (f : I → I → I → I → M) :
    (∑ r, ∑ d, ∑ b, ∑ c, f b c d r) = ∑ b, ∑ c, ∑ d, ∑ r, f b c d r := by
  calc
    _ = ∑ r, ∑ b, ∑ c, ∑ d, f b c d r := by
      apply Finset.sum_congr rfl; intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b hb
      exact Finset.sum_comm
    _ = ∑ b, ∑ r, ∑ c, ∑ d, f b c d r := Finset.sum_comm
    _ = _ := sum4_middle f

/-- Actual Lie Jacobi extended to central even polynomial coefficients.
It applies in particular to all gauge jets and the full odd ghost family. -/
theorem colorPolynomialBracket_jacobi_central {B : InvariantForm G} (e : ColorFrame B)
    (X Y Z : ColorPolynomial G)
    (centralY : ∀ c P, Y c * P = P * Y c) (a : Fin G.dimension) :
    colorPolynomialBracket e (colorPolynomialBracket e X Z) Y a +
      colorPolynomialBracket e X (colorPolynomialBracket e Y Z) a =
      colorPolynomialBracket e (colorPolynomialBracket e X Y) Z a := by
  have hw (b c d : Fin G.dimension) : (X b * Z d) * Y c = (X b * Y c) * Z d := by
    rw [mul_assoc, ← centralY, ← mul_assoc]
  unfold colorPolynomialBracket
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul, hw]
  conv_lhs =>
    lhs
    rw [sum4_left]
  conv_lhs =>
    rhs
    rw [sum4_middle]
  conv_rhs => rw [sum4_right]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro d hd
  have hc := curvatureJacobiCoefficient e a b c d
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hc
  have hs : (∑ r : Fin G.dimension,
      ((structureConstant e a r c : ℂ) * (structureConstant e r b d : ℂ))) +
      (∑ r : Fin G.dimension,
        ((structureConstant e a b r : ℂ) * (structureConstant e r c d : ℂ))) =
      ∑ r : Fin G.dimension,
        ((structureConstant e a r d : ℂ) * (structureConstant e r b c : ℂ)) := by
    linear_combination hc
  simp only [mul_assoc]
  simp only [← add_smul, ← Finset.sum_smul]
  rw [Finset.sum_add_distrib, hs]

end YangMills.FullBV
