import YangMills.PointwiseNormalizationJetComparison
import YangMills.ConservingJetTransport
import YangMills.CanonicalHighJetAdequacy

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}
attribute [local irreducible] monomialsBelow

/-- All source-allowed canonical irrelevant UV rows of the actual finite
normalization response vanish, from the SAME pointwise insertion boundary. -/
theorem pointwiseNormalizationResponse_uv_projectors
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (output : LocalMonomial G) (ho : output.Admissible) (hd : D < output.dimension)
    (q : Fin output.legs.length → Spacetime) :
    extractCoefficient output (pointwiseNormalizationResponse L I D μ g loop UV UV) q = 0 := by
  classical
  have hp : 0 < UV := h.scale_positive.trans_le hUV
  have hs (m : LocalMonomial G) (r : ℕ) :
      ContDiff ℝ output.momentumDirections.length (L μ g [⟨m, 0⟩] (loop-r) UV UV output.legs) :=
    (h.smooth _ _ _ _ hp le_rfl _).of_le
      (by exact_mod_cast (show (output.momentumDirections.length : ℕ∞) ≤ ⊤ from le_top))
  unfold pointwiseNormalizationResponse
  rw [extractCoefficient_sum_regular]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [extractCoefficient_sum_regular]
    · apply Finset.sum_eq_zero
      intro r hr
      rw [extractCoefficient_const_mul_regular _ _ _ _ (hs m r)]
      have hm' := (mem_monomialsBelow_iff (D+1) m).mp hm
      rw [h.irrelevant m output hm'.1 ho (by omega) (loop-r) UV hUV q, mul_zero]
    · intro r hr
      exact contDiff_const.mul (hs m r)
  · intro m hm
    exact ContDiff.sum (fun r hr => contDiff_const.mul (hs m r))

/-- Canonical exterior-algebra UV projectors imply EVERY actual high
coordinate jet of this finite response vanishes, including inadmissible
repeated-odd directions away from the origin. -/
theorem pointwiseNormalizationResponse_uv_raw_jets
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (symmetry : ∀ m r labels q (e : Equiv.Perm (Fin labels.length)),
      L μ g [⟨m, 0⟩] r UV UV (permutedLegs labels e) (permutedMomenta labels e q) =
        permutationSign labels e * L μ g [⟨m, 0⟩] r UV UV labels q)
    (labels : List (ExternalLeg G)) (directions : List (Fin labels.length × Fin 4))
    (degree : D < totalDimension labels + directions.length)
    (q : Fin labels.length → Spacetime) :
    momentumJet directions (pointwiseNormalizationResponse L I D μ g loop UV UV labels) q = 0 := by
  apply canonicalHighProjectorAdequacy
    (pointwiseNormalizationResponse L I D μ g loop UV UV)
    (fun labels => pointwiseNormalizationResponse_smooth L I D μ g UV UV loop labels h
      (h.scale_positive.trans_le hUV) le_rfl)
    (pointwiseNormalizationResponse_graded L I D μ g UV UV loop symmetry) D
    (fun m hm hd q => pointwiseNormalizationResponse_uv_projectors L I D μ g UV loop h hUV m hm hd q)
    labels directions degree q

/-- Global high-jet vanishing is preserved by an arbitrary fixed linear
momentum pullback; the derivative tensor is recovered from actual coordinates. -/
theorem momentumJet_compCLM_zero (labels : List (ExternalLeg G))
    (f : (Fin labels.length → Spacetime) → ℂ) (smooth : ContDiff ℝ ∞ f)
    (C : (Fin labels.length → Spacetime) →L[ℝ] (Fin labels.length → Spacetime))
    (directions : List (Fin labels.length × Fin 4))
    (jets : ∀ p : Fin directions.length → Fin labels.length × Fin 4, ∀ q,
      momentumJet (List.ofFn p) f q = 0) (q : Fin labels.length → Spacetime) :
    momentumJet directions (f ∘ C) q = 0 := by
  have hd : iteratedFDeriv ℝ directions.length f (C q) = 0 := by
    apply doublePi_multilinear_zero
    intro p
    rw [← momentumJet_ofFn]
    exact jets p (C q)
  unfold momentumJet
  rw [C.iteratedFDeriv_comp_right smooth q
    (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top)), hd]
  simp

/-- The actual conserving-momentum finite response has precisely the UV
irrelevant coordinate normalization required by the integrated linear flow. -/
theorem pointwiseNormalizationResponse_uv_jets
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (symmetry : ∀ m r labels q (e : Equiv.Perm (Fin labels.length)),
      L μ g [⟨m, 0⟩] r UV UV (permutedLegs labels e) (permutedMomenta labels e q) =
        permutationSign labels e * L μ g [⟨m, 0⟩] r UV UV labels q)
    (labels : List (ExternalLeg G)) (directions : List (Fin labels.length × Fin 4))
    (degree : D < totalDimension labels + directions.length)
    (q : Fin labels.length → Spacetime) :
    momentumJet directions (fun p => pointwiseNormalizationResponse L I D μ g loop UV UV labels
      (conservingMomenta labels p)) q = 0 := by
  have hh := momentumJet_compCLM_zero labels
    (pointwiseNormalizationResponse L I D μ g loop UV UV labels)
    (pointwiseNormalizationResponse_smooth L I D μ g UV UV loop labels h
      (h.scale_positive.trans_le hUV) le_rfl) (conservingMomentumMap labels) directions (by
      intro p q
      apply pointwiseNormalizationResponse_uv_raw_jets L I D μ g UV loop h hUV symmetry
      simpa only [List.length_ofFn] using degree) q
  simpa only [Function.comp_def, conservingMomentumMap_apply] using hh

end YangMills.IntegratedNormalization
