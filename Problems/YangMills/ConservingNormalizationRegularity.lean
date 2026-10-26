import Problems.YangMills.PointwiseNormalizationRegularity
import Problems.YangMills.ConservingJetTransport
import Problems.YangMills.IntegratedVacuumSubtraction

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}
attribute [local irreducible] pointwiseNormalizationResponse

/-- Actual finite coordinate expansion of the derivative of a fixed linear
pullback, useful also when the momentum argument has been made conserving. -/
theorem momentumJet_compCLM_expansion (labels : List (ExternalLeg G))
    (f : (Fin labels.length → Spacetime) → ℂ) (smooth : ContDiff ℝ ∞ f)
    (C : (Fin labels.length → Spacetime) →L[ℝ] (Fin labels.length → Spacetime))
    (d : List (Fin labels.length × Fin 4)) (q : Fin labels.length → Spacetime) :
    momentumJet d (f ∘ C) q =
      ∑ p : Fin d.length → Fin labels.length × Fin 4,
        (∏ i : Fin d.length,
          C (Pi.single (d.get i).1 (Pi.single (d.get i).2 1)) (p i).1 (p i).2) •
          momentumJet (List.ofFn p) f (C q) := by
  change iteratedFDeriv ℝ d.length (f ∘ C) q
    (fun i => Pi.single (d.get i).1 (Pi.single (d.get i).2 1)) = _
  rw [C.iteratedFDeriv_comp_right smooth q
    (by exact_mod_cast (show (d.length : ℕ∞) ≤ ⊤ from le_top))]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [doublePi_multilinear_expansion]
  apply Finset.sum_congr rfl
  intro p hp
  rw [momentumJet_ofFn]

/-- The actual comparison family: finite same-pointwise normalization,
explicit vacuum subtraction, then conserving momentum extension. -/
def conservingPointwiseNormalizationResponse (L : ℝ → ℝ → InsertedFlowFamily G)
    (I : ScaleCouplingFamily G) (D : ℕ) : ScaleCouplingFamily G :=
  fun μ g loop Λ UV labels q =>
    reducedPointwiseNormalizationResponse L I D μ g loop Λ UV labels
      (conservingMomenta labels q)

theorem conservingPointwiseNormalizationResponse_nonempty
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g Λ UV : ℝ) (loop : ℕ)
    (labels : List (ExternalLeg G)) (hn : labels ≠ []) :
    conservingPointwiseNormalizationResponse L I D μ g loop Λ UV labels =
      fun q => pointwiseNormalizationResponse L I D μ g loop Λ UV labels
        (conservingMomenta labels q) := by
  funext q
  exact subtractVacuum_nonempty _ loop Λ UV labels (conservingMomenta labels q) hn

theorem conservingPointwiseNormalizationResponse_smooth
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g Λ UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hΛ : 0 < Λ) (hUV : Λ ≤ UV)
    (labels : List (ExternalLeg G)) :
    ContDiff ℝ ∞ (conservingPointwiseNormalizationResponse L I D μ g loop Λ UV labels) := by
  classical
  by_cases he : labels = []
  · subst labels
    exact contDiff_const
  · rw [conservingPointwiseNormalizationResponse_nonempty L I D μ g Λ UV loop labels he]
    have hs := (pointwiseNormalizationResponse_smooth L I D μ g Λ UV loop labels h hΛ hUV).comp (conservingMomentumMap labels).contDiff
    simpa only [Function.comp_def, conservingMomentumMap_apply] using hs

/-- Positive-cutoff jet continuity of the actual conserving comparison
family follows by a finite expansion of the actual linear pullback. -/
theorem conservingPointwiseNormalizationResponse_jet_continuous
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ)
    (labels : List (ExternalLeg G)) (d : List (Fin labels.length × Fin 4))
    (q : Fin labels.length → Spacetime) :
    ContinuousOn (fun Λ => momentumJet d
      (conservingPointwiseNormalizationResponse L I D μ g loop Λ UV labels) q) (Set.Ioc 0 UV) := by
  classical
  by_cases he : labels = []
  · subst labels
    change ContinuousOn (fun _ => momentumJet d (fun _ => 0) q) _
    exact continuousOn_const
  · have hc : ContinuousOn (fun Λ =>
        ∑ p : Fin d.length → Fin labels.length × Fin 4,
          (∏ i : Fin d.length,
            conservingMomentumMap labels (Pi.single (d.get i).1 (Pi.single (d.get i).2 1))
              (p i).1 (p i).2) •
            momentumJet (List.ofFn p)
              (pointwiseNormalizationResponse L I D μ g loop Λ UV labels)
              (conservingMomentumMap labels q)) (Set.Ioc 0 UV) := by
      apply continuousOn_finsetSum _
      intro p hp
      exact (pointwiseNormalizationResponse_jet_continuous L I D μ g UV loop h labels
        (List.ofFn p) (conservingMomentumMap labels q)).const_smul _
    apply hc.congr
    intro Λ hΛ
    dsimp only
    rw [conservingPointwiseNormalizationResponse_nonempty L I D μ g Λ UV loop labels he]
    have ht := momentumJet_compCLM_expansion labels
      (pointwiseNormalizationResponse L I D μ g loop Λ UV labels)
      (pointwiseNormalizationResponse_smooth L I D μ g Λ UV loop labels h hΛ.1 hΛ.2)
      (conservingMomentumMap labels) d q
    simpa only [Function.comp_def, conservingMomentumMap_apply] using ht

end YangMills.IntegratedNormalization
