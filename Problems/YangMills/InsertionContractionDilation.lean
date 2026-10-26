import Problems.YangMills.InsertionEquationDilation
import Problems.YangMills.OversubtractionBoundaryDilation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

/-- The actual graded external Leibniz product respects the sum of input
degrees. The ordered split signs and Cauchy loop factors are retained. -/
theorem flowProduct_rescaleDegree (a : ℝ) (positive : 0 < a) (D E : ℕ) (A B : FlowFamily G) :
    flowProduct (rescaleDegree a D A) (rescaleDegree a E B) =
      rescaleDegree a (D+E) (flowProduct A B) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  funext loop Λ UV legs q
  unfold flowProduct amplitudeProduct
  simp only [rescaleDegree,selectedMomenta_smul,Complex.ofReal_zpow,Nat.cast_add]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro s _
  have partition : (totalDimension (selectedLegs legs s) : ℤ) +
      totalDimension (selectedLegs legs (complementIndices legs s)) = totalDimension legs := by
    exact_mod_cast totalDimension_partition legs s
  have weight :
      (a : ℂ)^((totalDimension (selectedLegs legs s) : ℤ)-D) *
        (a : ℂ)^((totalDimension (selectedLegs legs (complementIndices legs s)) : ℤ)-E) =
      (a : ℂ)^((totalDimension legs : ℤ)-(D+E)) := by
    rw [← zpow_add₀ nonzero]
    congr 1
    linear_combination partition
  linear_combination weight * (splitSign legs s *
    A l (a*Λ) (a*UV) (selectedLegs legs s) (a • selectedMomenta legs s q) *
    B (loop-l) (a*Λ) (a*UV) (selectedLegs legs (complementIndices legs s))
      (a • selectedMomenta legs (complementIndices legs s) q))

lemma rescaleDegree_flowUnit (a : ℝ) : rescaleDegree a 0 (flowUnit : FlowFamily G) = flowUnit := by
  funext loop Λ UV legs q
  unfold rescaleDegree flowUnit
  split_ifs with only
  · obtain ⟨_,equal⟩ := only
    subst legs
    simp [totalDimension]
  · simp

/-- All actual spectator insertions are transported, with no replacement
moment/disconnected word family introduced. -/
theorem singleInsertionProduct_rescale (a : ℝ) (positive : 0 < a) (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) :
    singleInsertionProduct (rescaleInsertedFlow a L) input =
      rescaleDegree a (positionedInsertionDegreeSum input) (singleInsertionProduct L (dilateInsertionPoints a input)) := by
  induction input with
  | nil => simp [singleInsertionProduct,positionedInsertionDegreeSum,dilateInsertionPoints,rescaleDegree_flowUnit]
  | cons item input ih =>
    rcases item with ⟨m,x⟩
    simp only [singleInsertionProduct,rescaleInsertedFlow_single,dilateInsertionPoints,List.map_cons]
    rw [ih,flowProduct_rescaleDegree a positive]
    rfl

lemma independentContractionIntegrand_rescaleDegree (a : ℝ) (positive : 0 < a)
    (D E : ℕ) (parity : Bool) (A B : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    independentContractionIntegrand parity (rescaleDegree a D A) (rescaleDegree a E B)
      loop Λ UV legs q p =
      (a : ℂ)^((totalDimension legs : ℤ)-D-E+5) *
        independentContractionIntegrand parity A B loop (a*Λ) (a*UV) legs (a • q) (a • p) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  unfold independentContractionIntegrand
  simp only [rescaleDegree,totalDimension_cons,ExternalLeg.dimension,prependMomenta_smul,
    selectedMomenta_smul,smul_neg,Complex.ofReal_zpow,Nat.cast_add]
  rw [← mul_div_assoc]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro N _
  rw [basicDerivativeCovariance_dilate a Λ positive M N,Complex.ofReal_mul,Complex.ofReal_zpow]
  have partition : (totalDimension (selectedLegs legs s) : ℤ) +
      totalDimension (selectedLegs legs (complementIndices legs s)) = totalDimension legs := by
    exact_mod_cast totalDimension_partition legs s
  have weight :
      (a : ℂ)^((N.dimension : ℤ)+totalDimension (selectedLegs legs s)-D) *
        (a : ℂ)^((M.dimension : ℤ)+totalDimension (selectedLegs legs (complementIndices legs s))-E) =
      (a : ℂ)^((totalDimension legs : ℤ)-D-E+5) * (a : ℂ)^((M.dimension : ℤ)+N.dimension-5) := by
    rw [← zpow_add₀ nonzero,← zpow_add₀ nonzero]
    congr 1
    linear_combination partition
  linear_combination weight * (splitSign legs s * intrinsicContractionSign parity M *
    (basicDerivativeCovariance Λ M N p : ℂ) *
    A l.val (a*Λ) (a*UV) (.inl N :: selectedLegs legs s)
      (prependMomenta (.inl N) (-(a • p)) (a • selectedMomenta legs s q)) *
    B (loop-l.val) (a*Λ) (a*UV) (.inl M :: selectedLegs legs (complementIndices legs s))
      (prependMomenta (.inl M) (a • p) (a • selectedMomenta legs (complementIndices legs s) q)))

lemma weighted_integral_dilation (a : ℝ) (positive : 0 < a) (weight : ℤ) (f : Spacetime → ℂ) :
    (∫ p : Spacetime, (a : ℂ)^weight * f (a • p)) =
      (a : ℂ)^(weight-4) * ∫ p : Spacetime, f p := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume _ a (hR := positive.le)]
  have dimension : Module.finrank ℝ Spacetime = 4 := by simp [Spacetime]
  rw [dimension,Complex.real_smul,← mul_assoc]
  push_cast
  have fourth : ((a : ℂ)^4)⁻¹ = (a : ℂ)^(-4 : ℤ) := by simp [zpow_neg,zpow_ofNat]
  rw [fourth,← zpow_add₀ nonzero]
  congr 2

/-- The pair source's independent internal momentum contributes its actual
4D Jacobian. The extra factor a is exactly the flow derivative degree. -/
theorem independentContractionRHS_rescaleDegree (a : ℝ) (positive : 0 < a)
    (D E : ℕ) (parity : Bool) (A B : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    independentContractionRHS parity (rescaleDegree a D A) (rescaleDegree a E B)
      loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-D-E+1) *
        independentContractionRHS parity A B loop (a*Λ) (a*UV) legs (a • q) := by
  unfold independentContractionRHS
  simp_rw [independentContractionIntegrand_rescaleDegree a positive]
  rw [weighted_integral_dilation a positive]
  congr 2
  ring

end YangMills.PerturbativeFlow
