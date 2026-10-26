import YangMills.FullBVGaugeFixedAction
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The ordinary (two even gauges, one odd ghost) Jacobi coefficient of the
actual Lie algebra in precisely the order needed by the curvature variation. -/
theorem curvatureJacobiCoefficient {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) :
    (∑ r : Fin G.dimension,
      ((structureConstant e a r c : ℂ) * (structureConstant e r b d : ℂ) +
       (structureConstant e a b r : ℂ) * (structureConstant e r c d : ℂ) -
       (structureConstant e a r d : ℂ) * (structureConstant e r b c : ℂ))) = 0 := by
  have h := colorJacobiCoefficient_cyclic e a b c d
  unfold colorJacobiCoefficient at h
  simp only [color_skew_complex e a c _, color_skew_complex e _ d b,
    color_skew_complex e a d _, neg_mul, mul_neg, neg_neg] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_neg_distrib] at h
  linear_combination h

def gaugeGaugeGhostWord (G : CompactSimpleGaugeGroup) (mu nu : Fin 4)
    (b c d : Fin G.dimension) : JetAlgebra G :=
  (gaugePotentialJet G mu b * gaugePotentialJet G nu c) * ghostJet G d

/-- The actual polynomial curvature Jacobi cancellation. No independent
color representation, Lie action or BRST differential is supplied. -/
theorem curvatureJacobi_contraction {B : InvariantForm G} (e : ColorFrame B)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
      (∑ r : Fin G.dimension,
        ((structureConstant e a r c : ℂ) * (structureConstant e r b d : ℂ) +
         (structureConstant e a b r : ℂ) * (structureConstant e r c d : ℂ) -
         (structureConstant e a r d : ℂ) * (structureConstant e r b c : ℂ))) •
        gaugeGaugeGhostWord G mu nu b c d) = 0 := by
  simp only [curvatureJacobiCoefficient, zero_smul, Finset.sum_const_zero]

end YangMills.FullBV
