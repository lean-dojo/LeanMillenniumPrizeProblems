import Problems.YangMills.ConservingNormalizationFlow
import Problems.YangMills.IntegratedPointwiseMuJets
import Problems.YangMills.PointwiseNormalizationUVJets

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Source Eq123's finite pointwise normalization bridge, with the finite
mixing coefficients COMPUTED from SAME I and SAME pointwise L. The hypotheses
are the actual linear flow/regularity, balanced covariance and irrelevant UV
normalization of the integrated response; no comparison identity is assumed. -/
theorem integrated_eq_computed_pointwise_normalization
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    {background : FlowFamily G} {F : OversubtractedFamily G}
    (D : ℕ) (μ g UV : ℝ)
    (hL : InsertionFlowConditions background (L μ g) F μ)
    (hUV : μ ≤ UV)
    (hI : ReducedLinearInsertionRegularity background (I μ g) UV)
    (gradedI : ∀ loop labels q (π : Equiv.Perm (Fin labels.length)),
      BalancedMomenta labels q →
      I μ g loop μ UV (permutedLegs labels π) (permutedMomenta labels π q) =
        permutationSign labels π * I μ g loop μ UV labels q)
    (highI : ∀ loop labels (d : List (Fin labels.length × Fin 4)),
      ReducedDirections labels d → D < totalDimension labels + d.length → ∀ q,
        momentumJet d (I μ g loop UV UV labels) q = 0)
    (free : ∀ Λ labels q, 0 < Λ → Λ < UV → labels.length ≤ 2 →
      background 0 Λ UV labels q = 0)
    (loop : ℕ) (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) :
    I μ g loop Λ UV labels q =
      conservingPointwiseNormalizationResponse L I D μ g loop Λ UV labels q := by
  have hμ := hL.single_boundary.scale_positive
  let R := conservingPointwiseNormalizationResponse L I D μ g
  have hR : ReducedLinearInsertionRegularity background R UV :=
    conservingPointwiseNormalizationResponse_reducedRegularity L I D μ g UV hL
  apply ReducedLinearInsertionRegularity.unique_of_reduced_jets hI hR hμ hUV D free
  · intro l ls d hred hd
    by_cases hempty : ls = []
    · subst ls
      have hi : I μ g l μ UV [] = (fun _ => 0) := funext (hI.vacuum l μ)
      have hr : R l μ UV [] = (fun _ => 0) := funext (hR.vacuum l μ)
      rw [hi, hr]
    · have hn : ls.length ≠ 0 := by
        intro he
        apply hempty
        simpa using he
      change momentumJet d (I μ g l μ UV ls) 0 =
        momentumJet d (conservingPointwiseNormalizationResponse L I D μ g l μ UV ls) 0
      rw [conservingPointwiseNormalizationResponse_nonempty L I D μ g μ UV l ls hempty]
      exact (pointwiseNormalizationResponse_mu_jets L I D μ g UV l hL.single_boundary hUV
        (fun m r labels q e => hL.single_graded_symmetry m 0 r μ UV labels q e)
        (fun labels => hI.smooth l μ labels hμ hUV)
        (hI.extension l μ) ls hn (fun e p hb => gradedI l ls p e hb) d hd).symm
  · intro l ls d hred hd p
    rw [highI l ls d hred hd p]
    by_cases hempty : ls = []
    · subst ls
      have hr : R l UV UV [] = (fun _ => 0) := funext (hR.vacuum l UV)
      rw [hr]
      unfold momentumJet
      rw [iteratedFDeriv_fun_zero]
      rfl
    · change 0 = momentumJet d
        (conservingPointwiseNormalizationResponse L I D μ g l UV UV ls) p
      rw [conservingPointwiseNormalizationResponse_nonempty L I D μ g UV UV l ls hempty]
      exact (pointwiseNormalizationResponse_uv_jets L I D μ g UV l hL.single_boundary hUV
        (fun m r labels q e => hL.single_graded_symmetry m 0 r UV UV labels q e)
        ls d hd p).symm
  · exact hp
  · exact hle

end YangMills.IntegratedNormalization
