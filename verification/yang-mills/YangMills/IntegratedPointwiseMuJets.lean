import YangMills.PointwiseNormalizationJetComparison
import YangMills.ConservingJetTransport

noncomputable section
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The actual finite triangular pointwise normalization has the SAME
integrated amplitude's actual mu-jets. Canonical projector equations imply
independent jets first; only then is conserving momentum imposed. -/
theorem pointwiseNormalizationResponse_mu_jets
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (singleSymmetry : ∀ m r labels q (e : Equiv.Perm (Fin labels.length)),
      L μ g [⟨m, 0⟩] r μ UV (permutedLegs labels e) (permutedMomenta labels e q) =
        permutationSign labels e * L μ g [⟨m, 0⟩] r μ UV labels q)
    (smooth : ∀ labels, ContDiff ℝ ∞ (I μ g loop μ UV labels))
    (extension : ∀ labels p, I μ g loop μ UV labels p =
      I μ g loop μ UV labels (conservingMomenta labels p))
    (labels : List (ExternalLeg G)) (hne : labels.length ≠ 0)
    (graded : ∀ π p, BalancedMomenta labels p →
      I μ g loop μ UV (permutedLegs labels π) (permutedMomenta labels π p) =
        permutationSign labels π * I μ g loop μ UV labels p)
    (directions : List (Fin labels.length × Fin 4))
    (degree : totalDimension labels + directions.length ≤ D) :
    momentumJet directions (fun q => pointwiseNormalizationResponse L I D μ g loop μ UV
      labels (conservingMomenta labels q)) 0 =
        momentumJet directions (I μ g loop μ UV labels) 0 := by
  have hraw := momentumJet_compCLM_of_equal_jets labels
    (pointwiseNormalizationResponse L I D μ g loop μ UV labels)
    (FullBV.densityAmplitude (integratedTaylorDensity D I μ g loop UV) labels)
    (pointwiseNormalizationResponse_smooth L I D μ g μ UV loop labels h h.scale_positive hUV)
    (densityAmplitude_smooth _ labels) (conservingMomentumMap labels) directions (by
      intro p
      apply pointwiseNormalizationResponse_raw_jets L I D μ g UV loop h hUV singleSymmetry
      simpa only [List.length_ofFn] using degree)
  simp only [Function.comp_def, conservingMomentumMap_apply] at hraw
  exact hraw.trans (integratedTaylorDensity_mu_jets D I μ g loop UV smooth extension
    labels hne graded directions degree)

end YangMills.IntegratedNormalization
