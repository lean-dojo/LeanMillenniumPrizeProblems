import Problems.YangMills.FullBVActualNoetherIdentity

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def genericMixedGhostWord (X : ColorPolynomial G)
    (b c d : Fin G.dimension) : JetAlgebra G :=
  (X b * ghostJet G c) * ghostJet G d

theorem genericMixedGhostWord_skew (X : ColorPolynomial G) (b c d : Fin G.dimension) :
    genericMixedGhostWord X b c d = -(genericMixedGhostWord X b d c) := by
  unfold genericMixedGhostWord
  rw [mul_assoc, ghostJetDeriv_anticommute c d 0 0]
  have hn (P Q : JetAlgebra G) : P*(-Q) = -(P*Q) := mul_neg P Q
  rw [hn, ← mul_assoc]

/-- Actual two-ghost Jacobi contraction: twice [[A,c],c] is [A,[c,c]].
The iterated-bracket coefficient is -J(a,d,b,c); all tensors and word signs
come from the same G and the same superjet algebra as the action. -/
theorem generic_colorJacobi_mixed_contraction {B : InvariantForm G} (e : ColorFrame B)
    (X : ColorPolynomial G) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
      colorJacobiCoefficient e a b c d • genericMixedGhostWord X b c d) =
    (2 : ℂ) • (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
      (-colorJacobiCoefficient e a d b c) • genericMixedGhostWord X b c d) := by
  let F (b c d : Fin G.dimension) :=
    colorJacobiCoefficient e a b c d • genericMixedGhostWord X b c d
  let H (b c d : Fin G.dimension) :=
    colorJacobiCoefficient e a c d b • genericMixedGhostWord X b c d
  let K (b c d : Fin G.dimension) :=
    colorJacobiCoefficient e a d b c • genericMixedGhostWord X b c d
  have hp (b c d : Fin G.dimension) : F b c d + H b c d + K b c d = 0 := by
    dsimp [F, H, K]
    rw [← add_smul, ← add_smul, colorJacobiCoefficient_cyclic, zero_smul]
  have hh : (∑ b, ∑ c, ∑ d, H b c d) = ∑ b, ∑ c, ∑ d, K b c d := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [H, K]
    rw [colorJacobiCoefficient_skew_last e a d c b, genericMixedGhostWord_skew X b d c]
    exact neg_smul_neg _ _
  have ht : (∑ b, ∑ c, ∑ d, F b c d) +
      (∑ b, ∑ c, ∑ d, H b c d) + (∑ b, ∑ c, ∑ d, K b c d) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    simp only [hp, Finset.sum_const_zero]
  rw [hh] at ht
  have hn : (∑ b, ∑ c, ∑ d,
      (-colorJacobiCoefficient e a d b c) • genericMixedGhostWord X b c d) =
      -(∑ b, ∑ c, ∑ d, K b c d) := by
    simp only [K]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact neg_smul (colorJacobiCoefficient e a d b c) (genericMixedGhostWord X b c d)
  rw [hn]
  change (∑ b, ∑ c, ∑ d, F b c d) = _
  have ht' : (∑ b, ∑ c, ∑ d, F b c d) +
      ((∑ b, ∑ c, ∑ d, K b c d) + (∑ b, ∑ c, ∑ d, K b c d)) = 0 := by
    simpa only [add_assoc] using ht
  have he := eq_neg_of_add_eq_zero_left ht' 
  simpa only [two_smul, smul_neg, neg_add_rev] using he

private theorem sum_three_to_left {I M : Type*} [Fintype I] [AddCommMonoid M]
    (F : I → I → I → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ j, ∑ k, ∑ i, F i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact Finset.sum_comm
private theorem sum_four_to_left {I M : Type*} [Fintype I] [AddCommMonoid M]
    (F : I → I → I → I → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ j, ∑ k, ∑ l, ∑ i, F i j k l := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact sum_three_to_left _

theorem colorPolynomialBracket_twoGhost_first {B : InvariantForm G} (e : ColorFrame B)
    (X : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e (colorPolynomialBracket e X (ghostColorFamily G)) (ghostColorFamily G) a =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
        iteratedGaugeCoefficient e a b c d • genericMixedGhostWord X b c d := by
  simp only [colorPolynomialBracket, ghostColorFamily, Finset.sum_mul,
    smul_mul_assoc, Finset.smul_sum, smul_smul]
  rw [sum_four_to_left, sum_three_to_left]
  simp only [iteratedGaugeCoefficient, genericMixedGhostWord]
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro d hd
  rw [Finset.sum_smul]

theorem colorPolynomialBracket_twoGhost_second {B : InvariantForm G} (e : ColorFrame B)
    (X : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e X (colorPolynomialBracket e (ghostColorFamily G) (ghostColorFamily G)) a =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
        colorJacobiCoefficient e a b c d • genericMixedGhostWord X b c d := by
  simp only [colorPolynomialBracket, ghostColorFamily, Finset.mul_sum,
    mul_smul_comm, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl; intro b hb
  rw [sum_three_to_left]
  simp only [colorJacobiCoefficient, genericMixedGhostWord]
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro d hd
  rw [Finset.sum_smul]
  simp only [mul_assoc]

/-- The exact two-ghost Jacobi identity holds for ANY preceding full color
polynomial family, including odd shifted antifields and even c†. -/
theorem colorPolynomialBracket_twoGhost_Jacobi {B : InvariantForm G} (e : ColorFrame B)
    (X : ColorPolynomial G) :
    colorPolynomialBracket e X (colorPolynomialBracket e (ghostColorFamily G) (ghostColorFamily G)) =
      (2 : ℂ) • colorPolynomialBracket e (colorPolynomialBracket e X (ghostColorFamily G)) (ghostColorFamily G) := by
  funext a
  simp only [Pi.smul_apply]
  rw [colorPolynomialBracket_twoGhost_first, colorPolynomialBracket_twoGhost_second,
    generic_colorJacobi_mixed_contraction]
  simp only [iteratedGaugeCoefficient_eq, Pi.smul_apply]

end YangMills.FullBV
