import Problems.YangMills.FlowBoundaryUniqueness
import Problems.YangMills.FlowNormalizationDilation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Uniqueness of the actual fixed, massless coefficient flow on its
physical positive-cutoff domain. This is a theorem about the concrete
nonlinear equation and mixed boundary conditions, not a uniqueness axiom. -/
theorem CoefficientFlowConditions.unique {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A C : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A) (hC : CoefficientFlowConditions e scheme C)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (hΛUV : Λ ≤ UV)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    A μ g loop Λ UV legs q = C μ g loop Λ UV legs q := by
  have uvpos : 0 < UV := hμ.trans_le hUV
  have main : ∀ loop n, ∀ legs : List (ExternalLeg G), legs.length = n →
      ∀ Λ, 0 < Λ → Λ ≤ UV → ∀ q,
      A μ g loop Λ UV legs q = C μ g loop Λ UV legs q := by
    intro loop
    induction loop using Nat.strong_induction_on with
    | h loop ihloop =>
      intro n
      induction n using Nat.strong_induction_on with
      | h n iharity =>
        intro legs hlen Λ hp hle q
        by_cases empty : legs = []
        · subst legs
          rw [hA.vacuum_subtraction, hC.vacuum_subtraction]
        · have rhs : ∀ t p, 0 < t → t < UV → BalancedMomenta legs p →
              backgroundFlowRHS (A μ g) loop t UV legs p =
                backgroundFlowRHS (C μ g) loop t UV legs p := by
            intro t p ht htUV _
            apply backgroundFlowRHS_congr_lower
            · intro l ls p' hl
              rcases hl with hl | ⟨hl, hls⟩
              · exact ihloop l hl ls.length ls rfl t ht htUV.le p'
              · subst l
                exact iharity ls.length (by omega) ls rfl t ht htUV.le p'
            · intro ls p' hls
              exact hA.no_free_interaction μ g t UV ls p' hls
            · intro ls p' hls
              exact hC.no_free_interaction μ g t UV ls p' hls
          have constant : ∀ t, 0 < t → t ≤ UV →
              (fun p => A μ g loop UV UV legs p - C μ g loop UV UV legs p) =
                (fun p => A μ g loop t UV legs p - C μ g loop t UV legs p) := by
            intro t ht htUV
            exact flowDifference_scaleConstant_all hA hC μ g UV loop legs hμ hUV empty
              rhs uvpos le_rfl ht htUV
          have hz := flowDifference_eq_zero_of_constant hA hC μ g UV loop legs hμ hUV constant
          have hvalue := congrFun ((constant Λ hp hle).symm.trans hz) q
          exact sub_eq_zero.mp hvalue
  exact main loop legs.length legs rfl Λ hΛ hΛUV q

/-- Dimensional covariance of the CHOSEN actual background flow follows
from transformed equations/boundaries and their proved uniqueness. -/
theorem CoefficientFlowConditions.dimensional_covariance {B : InvariantForm G}
    {e : ColorFrame B} {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A) (a : ℝ) (ha : 0 < a)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (hΛUV : Λ ≤ UV)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    A μ g loop Λ UV legs q = rescaleFlow a (A (a*μ) g) loop Λ UV legs q := by
  exact hA.unique (hA.rescale a ha) μ g UV hμ hUV loop Λ hΛ hΛUV legs q

end YangMills.PerturbativeFlow
