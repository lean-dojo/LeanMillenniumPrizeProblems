import YangMills.InsertionSourceDilation

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

lemma linearFlowIntegrand_rescaleDegree (a : ℝ) (positive : 0 < a) (degree : ℕ)
    (F : FlowFamily G) (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand (rescaleDegree a degree F) loop Λ UV legs q p =
      (a : ℂ)^((totalDimension legs : ℤ)-degree+5) *
        linearFlowIntegrand F loop (a*Λ) (a*UV) legs (a • q) (a • p) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  rw [rescaleDegree_eq_scaleFlow a positive,linearFlowIntegrand_scaleFlow,
    linearFlowIntegrand_rescale a positive,← mul_assoc,← zpow_add₀ nonzero]
  congr 2
  ring

lemma linearFlowIntegrand_rescaled_integrable (a : ℝ) (positive : 0 < a) (degree : ℕ)
    (F : FlowFamily G) (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime)
    (h : Integrable (linearFlowIntegrand F loop (a*Λ) (a*UV) legs (a • q))) :
    Integrable (linearFlowIntegrand (rescaleDegree a degree F) loop Λ UV legs q) := by
  apply Integrable.congr ((h.comp_smul (ne_of_gt positive)).const_mul
    ((a : ℂ)^((totalDimension legs : ℤ)-degree+5)))
  filter_upwards [] with p
  exact (linearFlowIntegrand_rescaleDegree a positive degree F loop Λ UV legs q p).symm

lemma dilateInsertionCluster_insertions (a : ℝ) (input : InsertionCluster G) :
    (dilateInsertionCluster a input).insertions = dilateInsertionPoints a input.insertions := by
  simp [InsertionCluster.insertions,dilateInsertionCluster,dilateInsertionPoints]

lemma inputOddMultiplicity_dilate (a : ℝ) (input : List (PositionedInsertion G)) :
    inputOddMultiplicity (dilateInsertionPoints a input) = inputOddMultiplicity input := by
  simp [inputOddMultiplicity,dilateInsertionPoints,List.map_map,Function.comp_def]

lemma inputGhostNumber_dilate (a : ℝ) (input : List (PositionedInsertion G)) :
    inputGhostNumber (dilateInsertionPoints a input) = inputGhostNumber input := by
  simp [inputGhostNumber,dilateInsertionPoints,List.map_map,Function.comp_def]

lemma InsertionFlowConditions.rescaled_oversubtraction_flow {background : FlowFamily G}
    {L : InsertedFlowFamily G} {F : OversubtractedFamily G} {mu : ℝ}
    (h : InsertionFlowConditions background L F mu) (a : ℝ) (positive : 0 < a)
    (D : ℕ) (input : InsertionCluster G) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (ir_positive : 0 < Λ) (ir_lt : Λ < UV) :
    HasDerivAt (fun scale => rescaleOversubtractions a F D input.insertions loop scale UV legs q)
      (oversubtractionFlowRHS (rescaleFlow a background) (rescaleInsertedFlow a L)
        (rescaleOversubtractions a F) D input.insertions loop Λ UV legs q) Λ := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have equation := h.oversubtraction_flow D (dilateInsertionCluster a input)
    loop (a*Λ) (a*UV) legs (a • q) (mul_pos positive ir_positive)
      (mul_lt_mul_of_pos_left ir_lt positive)
  rw [dilateInsertionCluster_insertions] at equation
  have composed := equation.scomp Λ ((hasDerivAt_id Λ).const_mul a)
  have derivative := composed.const_mul ((a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input.insertions))
  simp only [rescaleOversubtractions,rescaleDegree,Complex.ofReal_zpow] at ⊢
  rw [oversubtractionFlowRHS_rescale a positive]
  simp only [Complex.real_smul,mul_one,← mul_assoc] at derivative
  have weight : (a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input.insertions) * (a : ℂ) =
      (a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input.insertions+1) :=
    (zpow_add_one₀ nonzero _).symm
  rw [weight] at derivative
  exact derivative

/-- The full fixed inserted system transports together with its SAME
background, statistics, signs, actual integrals, flow and boundary projectors. -/
theorem InsertionFlowConditions.rescale {background : FlowFamily G}
    {L : InsertedFlowFamily G} {F : OversubtractedFamily G} {mu : ℝ}
    (h : InsertionFlowConditions background L F mu) (a : ℝ) (positive : 0 < a) :
    InsertionFlowConditions (rescaleFlow a background) (rescaleInsertedFlow a L)
      (rescaleOversubtractions a F) (a⁻¹*mu) := by
  refine {
    single_boundary := h.single_boundary.rescale a positive
    oversubtraction_boundary := h.oversubtraction_boundary.rescale a positive
    background_identity := ?_
    single_statistics := ?_
    oversubtraction_statistics := ?_
    single_graded_symmetry := ?_
    oversubtraction_graded_symmetry := ?_
    single_translation := ?_
    single_loop_integrable := ?_
    oversubtraction_loop_integrable := ?_
    independent_pair_integrable := ?_
    single_flow := h.rescaled_single_flow a positive
    oversubtraction_flow := h.rescaled_oversubtraction_flow a positive }
  · simpa only [rescaleInsertedFlow,inputEngineeringDegree,dilateInsertionPoints,List.map_nil,
      rescaleDegree_four] using congrArg (rescaleFlow a) h.background_identity
  · intro input loop Λ UV legs q forbidden
    unfold rescaleInsertedFlow rescaleDegree
    rw [h.single_statistics (dilateInsertionPoints a input) loop (a*Λ) (a*UV) legs (a • q)
      (by simpa only [inputOddMultiplicity_dilate,inputGhostNumber_dilate] using forbidden),mul_zero]
  · intro D input loop Λ UV legs q forbidden
    unfold rescaleOversubtractions rescaleDegree
    rw [h.oversubtraction_statistics D (dilateInsertionPoints a input) loop (a*Λ) (a*UV) legs (a • q)
      (by simpa only [inputOddMultiplicity_dilate,inputGhostNumber_dilate] using forbidden),mul_zero]
  · intro A x loop Λ UV legs q pi
    simp only [rescaleInsertedFlow_single,rescaleDegree,totalDimension_permuted,
      ← permutedMomenta_smul,h.single_graded_symmetry]
    ring
  · intro D input loop Λ UV legs q pi
    simp only [rescaleOversubtractions,rescaleDegree,totalDimension_permuted,
      ← permutedMomenta_smul,h.oversubtraction_graded_symmetry]
    ring
  · intro A x y loop Λ UV legs q
    simp only [rescaleInsertedFlow_single,rescaleDegree]
    rw [h.single_translation A (a⁻¹ • x) (a⁻¹ • y) loop (a*Λ) (a*UV) legs (a • q)]
    simp only [Pi.smul_apply,← Finset.smul_sum,euclideanPair_inverse_scale a (ne_of_gt positive),smul_sub]
    ring
  · intro A x loop Λ UV legs q ir_positive ir_lt
    rw [rescaleInsertedFlow_single]
    apply linearFlowIntegrand_rescaled_integrable a positive
    exact h.single_loop_integrable A (a⁻¹ • x) loop (a*Λ) (a*UV) legs (a • q)
      (mul_pos positive ir_positive) (mul_lt_mul_of_pos_left ir_lt positive)
  · intro D input loop Λ UV legs q ir_positive ir_lt
    unfold rescaleOversubtractions
    apply linearFlowIntegrand_rescaled_integrable a positive
    exact h.oversubtraction_loop_integrable D (dilateInsertionPoints a input)
      loop (a*Λ) (a*UV) legs (a • q) (mul_pos positive ir_positive)
        (mul_lt_mul_of_pos_left ir_lt positive)
  · intro input k l loop Λ UV legs q ordered ir_positive ir_lt
    have singleton (i : Fin input.length) : rescaleInsertedFlow a L [input.get i] =
        rescaleDegree a (input.get i).monomial.dimension
          (L [(dilateInsertionPoints a input).get (dilateInsertionIndex a input i)]) := by
      rw [get_dilateInsertionPoints]
      exact rescaleInsertedFlow_single a L (input.get i).monomial (input.get i).position
    rw [singleton,singleton]
    have integrable := h.independent_pair_integrable (dilateInsertionPoints a input)
      (dilateInsertionIndex a input k) (dilateInsertionIndex a input l) loop (a*Λ) (a*UV) legs (a • q)
      ordered (mul_pos positive ir_positive) (mul_lt_mul_of_pos_left ir_lt positive)
    simp only [get_dilateInsertionPoints] at integrable ⊢
    apply Integrable.congr ((integrable.comp_smul (ne_of_gt positive)).const_mul
      ((a : ℂ)^((totalDimension legs : ℤ)-(input.get k).monomial.dimension-(input.get l).monomial.dimension+5)))
    filter_upwards [] with p
    exact (independentContractionIntegrand_rescaleDegree a positive _ _ _ _ _ loop Λ UV legs q p).symm

end YangMills.PerturbativeFlow
