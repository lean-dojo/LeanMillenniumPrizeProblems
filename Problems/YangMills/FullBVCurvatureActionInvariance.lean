import Problems.YangMills.FullBVActualCurvatureCovariance
import Problems.YangMills.FullBVNilpotencyPromotion

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Actual invariant-metric antisymmetry in the first two color slots. -/
theorem color_skew_first_complex {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) :
    (structureConstant e a b c : ℂ) = -(structureConstant e b a c : ℂ) := by
  have h := B.invariant (e.basis b) (e.basis a) (e.basis c)
  rw [← lie_skew (e.basis b) (e.basis a), map_neg, LinearMap.neg_apply,
    B.symmetric ⁅e.basis a, e.basis b⁆ (e.basis c)] at h
  have hc : structureConstant e a b c = structureConstant e c a b := by
    dsimp [structureConstant, threeColor]
    linarith
  have h' := B.invariant (e.basis a) (e.basis c) (e.basis b)
  rw [B.symmetric ⁅e.basis a, e.basis c⁆ (e.basis b)] at h'
  have hr : structureConstant e b a c = -structureConstant e c a b := by
    dsimp [structureConstant, threeColor]
    linarith
  rw [hr, hc]
  simp only [Complex.ofReal_neg, neg_neg]

/-- Every actual curvature component is even in the full jet algebra. -/
theorem parity_nonabelianCurvature {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    parity (nonabelianCurvatureJet e g mu nu a) = nonabelianCurvatureJet e g mu nu a := by
  simp only [nonabelianCurvatureJet, abelianCurvatureJet, gluonBracketJet,
    gaugeFirstJet, gaugePotentialJet, map_add, map_sub, map_smul, map_sum,
    parity_mul, parity_jet, ExternalLeg.parity, BasicField.fermionic,
    Bool.false_eq_true, if_false]

/-- Invariance of the actual metric contraction under the actual color
bracket, for any actually even polynomial family. -/
theorem colorPolynomial_metric_invariant {B : InvariantForm G} (e : ColorFrame B)
    (F : ColorPolynomial G) (hF : ∀ a, parity (F a) = F a)
    (C : ColorPolynomial G) :
    (∑ a : Fin G.dimension, F a * colorPolynomialBracket e F C a) = 0 := by
  let S : JetAlgebra G := ∑ a : Fin G.dimension, F a * colorPolynomialBracket e F C a
  have hs : S = -S := by
    dsimp [S]
    unfold colorPolynomialBracket
    simp only [Finset.mul_sum, mul_smul_comm]
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro a ha
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro b hb
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro c hc
    conv_lhs => rw [color_skew_first_complex e b a c]
    have hw : F b * (F a * C c) = F a * (F b * C c) := by
      rw [← mul_assoc, evenPolynomial_commute (F b) (F a) (hF b), mul_assoc]
    rw [hw]
    exact neg_smul (structureConstant e a b c : ℂ) (F a * (F b * C c))
  have ht : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    calc
      S + S = -S + S := congrArg (fun X : JetAlgebra G => X + S) hs
      _ = 0 := neg_add_cancel S
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The actual same-action curvature-square density is pointwise ST closed,
including its full nonlinear interactions and all actual color coefficients. -/
theorem classicalLocalST_curvatureDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    classicalLocalSTDensity e g (gluonCurvatureDensity e g) = 0 := by
  have hp (mu nu : Fin 4) (a : Fin G.dimension) :
      localST (masterActionDensity e g)
        (nonabelianCurvatureJet e g mu nu a * nonabelianCurvatureJet e g mu nu a) =
        ((2 : ℂ) * (g : ℂ)) •
          (nonabelianCurvatureJet e g mu nu a * colorPolynomialBracket e
            (fun b => nonabelianCurvatureJet e g mu nu b) (ghostColorFamily G) a) := by
    rw [localST_mul_even _ (parity_masterActionDensity e g), parity_nonabelianCurvature]
    change classicalLocalSTDensity e g (nonabelianCurvatureJet e g mu nu a) *
      nonabelianCurvatureJet e g mu nu a + nonabelianCurvatureJet e g mu nu a *
        classicalLocalSTDensity e g (nonabelianCurvatureJet e g mu nu a) = _
    rw [classicalLocalST_curvature_covariant]
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [← evenPolynomial_commute (nonabelianCurvatureJet e g mu nu a)
      (colorPolynomialBracket e (fun b => nonabelianCurvatureJet e g mu nu b)
        (ghostColorFamily G) a) (parity_nonabelianCurvature e g mu nu a)]
    module
  unfold gluonCurvatureDensity classicalLocalSTDensity
  simp only [localST_sum, localST_smul, hp, smul_smul]
  apply Finset.sum_eq_zero; intro mu hmu
  apply Finset.sum_eq_zero; intro nu hnu
  rw [← Finset.smul_sum, colorPolynomial_metric_invariant e
    (fun a => nonabelianCurvatureJet e g mu nu a)
    (parity_nonabelianCurvature e g mu nu), smul_zero]

end YangMills.FullBV
