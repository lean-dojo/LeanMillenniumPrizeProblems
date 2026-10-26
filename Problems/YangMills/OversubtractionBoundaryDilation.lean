import Problems.YangMills.InsertionBoundaryDilation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def positionedInsertionDegreeSum (input : List (PositionedInsertion G)) : ℕ :=
  (input.map (fun A => A.monomial.dimension)).sum

def rescaleOversubtractions (a : ℝ) (F : OversubtractedFamily G) : OversubtractedFamily G :=
  fun D input => rescaleDegree a (positionedInsertionDegreeSum input) (F D (dilateInsertionPoints a input))

def dilateInsertionCluster (a : ℝ) (input : InsertionCluster G) : InsertionCluster G :=
  ⟨dilateInsertionPoints a input.initial, ⟨input.last.monomial,a⁻¹ • input.last.position⟩⟩

lemma positionedInsertionDegreeSum_shift (input : List (PositionedInsertion G)) (y : Spacetime) :
    positionedInsertionDegreeSum (shiftInsertions input y) = positionedInsertionDegreeSum input := by
  simp [positionedInsertionDegreeSum,shiftInsertions,List.map_map,Function.comp_def]

lemma positionedInsertionDegreeSum_dilate (a : ℝ) (input : List (PositionedInsertion G)) :
    positionedInsertionDegreeSum (dilateInsertionPoints a input) = positionedInsertionDegreeSum input := by
  simp [positionedInsertionDegreeSum,dilateInsertionPoints,List.map_map,Function.comp_def]

lemma dilateInsertionPoints_shift (a : ℝ) (input : List (PositionedInsertion G)) (y : Spacetime) :
    dilateInsertionPoints a (shiftInsertions input y) =
      shiftInsertions (dilateInsertionPoints a input) (a⁻¹ • y) := by
  simp [dilateInsertionPoints,shiftInsertions,List.map_map,smul_sub]

lemma dilateInsertionCluster_atOrigin (a : ℝ) (input : InsertionCluster G) :
    (dilateInsertionCluster a input).atOrigin = dilateInsertionPoints a input.atOrigin := by
  simp [InsertionCluster.atOrigin,InsertionCluster.insertions,dilateInsertionCluster,
    dilateInsertionPoints,shiftInsertions,List.map_map,Function.comp_def,smul_sub]

lemma euclideanPair_inverse_scale (a : ℝ) (nonzero : a ≠ 0) (x p : Spacetime) :
    euclideanPair (a⁻¹ • x) (a • p) = euclideanPair x p := by
  unfold euclideanPair
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp

/-- All actual oversubtraction boundary projectors and their translation
phase are preserved. The subtraction index D does not replace the actual
sum of input engineering degrees in the canonical scaling factor. -/
theorem OversubtractionBoundaryConditions.rescale {F : OversubtractedFamily G}
    {mu : ℝ} (h : OversubtractionBoundaryConditions F mu) (a : ℝ) (positive : 0 < a) :
    OversubtractionBoundaryConditions (rescaleOversubtractions a F) (a⁻¹*mu) := by
  have nonzero := ne_of_gt positive
  refine {
    scale_positive := mul_pos (inv_pos.mpr positive) h.scale_positive
    smooth := ?_
    scale_jet_continuous := ?_
    low := ?_
    high := ?_
    translation := ?_ }
  · intro D input loop Λ UV hΛ hΛUV legs
    have smooth := h.smooth D (dilateInsertionPoints a input) loop (a*Λ) (a*UV)
      (mul_pos positive hΛ) (mul_le_mul_of_nonneg_left hΛUV positive.le) legs
    simpa only [rescaleOversubtractions,rescaleDegree,Function.comp_def,smul_eq_mul] using!
      (smooth.comp (contDiff_id.const_smul a)).const_smul
        (((a ^ ((totalDimension legs : ℤ)-positionedInsertionDegreeSum input) : ℝ)) : ℂ)
  · intro D input loop UV legs directions q
    have continuous := h.scale_jet_continuous D (dilateInsertionPoints a input) loop (a*UV) legs directions (a • q)
    have composed := continuous.comp (continuous_const.mul continuous_id).continuousOn
      (fun x (hx : x ∈ Set.Ioc 0 UV) =>
        (show a*x ∈ Set.Ioc 0 (a*UV) from
          ⟨mul_pos positive hx.1,mul_le_mul_of_nonneg_left hx.2 positive.le⟩))
    apply (composed.const_smul ((a : ℂ)^((totalDimension legs : ℤ)+directions.length-positionedInsertionDegreeSum input))).congr
    intro x _
    simpa only [rescaleOversubtractions,Function.comp_def,id_eq,smul_eq_mul] using!
      momentumJet_rescaleDegree a positive (positionedInsertionDegreeSum input)
        (F D (dilateInsertionPoints a input)) loop x UV legs directions q
  · intro D input B admissible low loop UV scale_le
    unfold rescaleOversubtractions
    rw [extractCoefficient_rescaleDegree a positive,smul_zero,mul_inv_cancel_left₀ nonzero]
    have ordered : mu ≤ a*UV := by
      have := mul_le_mul_of_nonneg_left scale_le positive.le
      simpa only [mul_inv_cancel_left₀ nonzero] using! this
    rw [← dilateInsertionCluster_atOrigin]
    rw [h.low D (dilateInsertionCluster a input) B admissible low loop (a*UV) ordered,mul_zero]
  · intro D input B admissible high loop UV scale_le q
    unfold rescaleOversubtractions
    rw [extractCoefficient_rescaleDegree a positive]
    have ordered : mu ≤ a*UV := by
      have := mul_le_mul_of_nonneg_left scale_le positive.le
      simpa only [mul_inv_cancel_left₀ nonzero] using! this
    rw [← dilateInsertionCluster_atOrigin]
    rw [h.high D (dilateInsertionCluster a input) B admissible high loop (a*UV) ordered,mul_zero]
  · intro D input y loop Λ UV legs q
    unfold rescaleOversubtractions rescaleDegree
    rw [h.translation D (dilateInsertionPoints a input) (a⁻¹ • y) loop (a*Λ) (a*UV) legs (a • q)]
    simp only [Pi.smul_apply,← Finset.smul_sum,euclideanPair_inverse_scale a nonzero,
      positionedInsertionDegreeSum_shift,dilateInsertionPoints_shift]
    ring

end YangMills.PerturbativeFlow
