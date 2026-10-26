import Problems.YangMills.PointwiseNormalizationFlow
import Problems.YangMills.ConservingNormalizationRegularity
import Problems.YangMills.ConservingFlowRestriction
import Problems.YangMills.ReducedLinearInsertionUniqueness

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The computed comparison response has all actual analytic hypotheses of
the balanced integrated linear insertion problem, including vacuum
subtraction and genuine positive-scale jet continuity. -/
def conservingPointwiseNormalizationResponse_reducedRegularity
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    {background : FlowFamily G} {F : OversubtractedFamily G}
    (D : ℕ) (μ g UV : ℝ)
    (h : InsertionFlowConditions background (L μ g) F μ) :
    ReducedLinearInsertionRegularity background
      (conservingPointwiseNormalizationResponse L I D μ g) UV where
  smooth loop Λ labels hp hle :=
    conservingPointwiseNormalizationResponse_smooth L I D μ g Λ UV loop h.single_boundary hp hle labels
  continuous loop labels d q :=
    conservingPointwiseNormalizationResponse_jet_continuous L I D μ g UV loop h.single_boundary labels d q
  extension loop Λ labels q := by
    change subtractVacuum (pointwiseNormalizationResponse L I D μ g) loop Λ UV labels
      (conservingMomenta labels q) =
      subtractVacuum (pointwiseNormalizationResponse L I D μ g) loop Λ UV labels
        (conservingMomenta labels (conservingMomenta labels q))
    rw [conservingMomenta_idempotent]
  vacuum loop Λ q := subtractVacuum_empty (pointwiseNormalizationResponse L I D μ g)
    loop Λ UV (conservingMomenta [] q)
  flow loop Λ labels q hp hlt nonempty balanced := by
    have hrhs : insertionHomogeneousRHS background
        (conservingPointwiseNormalizationResponse L I D μ g) loop Λ UV labels q =
        insertionHomogeneousRHS background (pointwiseNormalizationResponse L I D μ g)
          loop Λ UV labels q := by
      change insertionHomogeneousRHS background
        (conservingFlowExtension (subtractVacuum (pointwiseNormalizationResponse L I D μ g)))
          loop Λ UV labels q = _
      rw [insertionHomogeneousRHS_conserving _ _ loop Λ UV labels q balanced,
        insertionHomogeneousRHS_subtractVacuum]
    have hfun : (fun scale => conservingPointwiseNormalizationResponse L I D μ g loop scale UV labels q) =
        fun scale => pointwiseNormalizationResponse L I D μ g loop scale UV labels q := by
      funext scale
      rw [conservingPointwiseNormalizationResponse_nonempty L I D μ g scale UV loop labels nonempty]
      dsimp only
      rw [conservingMomenta_of_balanced labels q balanced]
    rw [hfun, hrhs]
    exact pointwiseNormalizationResponse_flow L I D μ g UV Λ loop h hp hlt labels q

end YangMills.IntegratedNormalization
