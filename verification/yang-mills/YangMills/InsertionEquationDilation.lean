import YangMills.InsertionBoundaryDilation
import YangMills.OversubtractedFlow

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

def scaleFlow (c : ℂ) (F : FlowFamily G) : FlowFamily G :=
  fun loop Λ UV legs q => c * F loop Λ UV legs q

lemma linearFlowIntegrand_scaleFlow (c : ℂ) (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand (scaleFlow c F) loop Λ UV legs q p =
      c * linearFlowIntegrand F loop Λ UV legs q p := by
  unfold linearFlowIntegrand
  by_cases loopzero : loop=0
  · simp only [loopzero,ite_true,mul_zero]
  · simp only [loopzero,ite_false,scaleFlow]
    rw [← mul_div_assoc]
    congr 1
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro N _
    ring

lemma linearFlowRHS_scaleFlow (c : ℂ) (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    linearFlowRHS (scaleFlow c F) loop Λ UV legs q = c * linearFlowRHS F loop Λ UV legs q := by
  unfold linearFlowRHS
  simp_rw [linearFlowIntegrand_scaleFlow]
  rw [integral_const_mul]

lemma quadraticSplit_scaleFlow_right (c : ℂ) (L F : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) :
    quadraticSplit L (scaleFlow c F) loop leftLoop Λ UV legs q s =
      c * quadraticSplit L F loop leftLoop Λ UV legs q s := by
  simp only [quadraticSplit,scaleFlow]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro N _
  ring

lemma quadraticFlowRHS_scaleFlow_right (c : ℂ) (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    quadraticFlowRHS L (scaleFlow c F) loop Λ UV legs q =
      c * quadraticFlowRHS L F loop Λ UV legs q := by
  unfold quadraticFlowRHS
  simp_rw [quadraticSplit_scaleFlow_right,Finset.mul_sum]

lemma insertionHomogeneousRHS_scaleFlow_right (c : ℂ) (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    insertionHomogeneousRHS L (scaleFlow c F) loop Λ UV legs q =
      c * insertionHomogeneousRHS L F loop Λ UV legs q := by
  unfold insertionHomogeneousRHS
  rw [linearFlowRHS_scaleFlow,quadraticFlowRHS_scaleFlow_right]
  ring

lemma rescaleDegree_eq_scaleFlow (a : ℝ) (positive : 0 < a) (degree : ℕ) (F : FlowFamily G) :
    rescaleDegree a degree F = scaleFlow ((a : ℂ)^(4-(degree : ℤ))) (rescaleFlow a F) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  funext loop Λ UV legs q
  simp only [rescaleDegree,rescaleFlow,scaleFlow,Complex.ofReal_zpow]
  rw [← mul_assoc,← zpow_add₀ nonzero]
  congr 2
  ring

/-- Local degree D, rather than the background degree four, is used for the
inserted amplitude. The actual background remains the SAME rescaled L. -/
theorem insertionHomogeneousRHS_rescaleDegree (a : ℝ) (positive : 0 < a)
    (degree : ℕ) (L F : FlowFamily G) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    insertionHomogeneousRHS (rescaleFlow a L) (rescaleDegree a degree F) loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-degree+1) *
        insertionHomogeneousRHS L F loop (a*Λ) (a*UV) legs (a • q) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  rw [rescaleDegree_eq_scaleFlow a positive,insertionHomogeneousRHS_scaleFlow_right,
    insertionHomogeneousRHS_rescale a positive,← mul_assoc,← zpow_add₀ nonzero]
  congr 2
  ring

/-- A genuine local insertion solution transforms to a solution of its SAME
homogeneous flow. No insertion covariance or chosen solution equality is
assumed; its position change is supplied by rescaleInsertedFlow below. -/
theorem rescaleDegree_preserves_single_equation (a : ℝ) (positive : 0 < a)
    (degree : ℕ) (L F : FlowFamily G) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (equation : HasDerivAt (fun scale => F loop scale (a*UV) legs (a • q))
      (insertionHomogeneousRHS L F loop (a*Λ) (a*UV) legs (a • q)) (a*Λ)) :
    HasDerivAt (fun scale => rescaleDegree a degree F loop scale UV legs q)
      (insertionHomogeneousRHS (rescaleFlow a L) (rescaleDegree a degree F) loop Λ UV legs q) Λ := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have composed := equation.scomp Λ ((hasDerivAt_id Λ).const_mul a)
  have derivative : HasDerivAt (fun scale => rescaleDegree a degree F loop scale UV legs q)
      ((a : ℂ)^((totalDimension legs : ℤ)-degree) *
        (a • insertionHomogeneousRHS L F loop (a*Λ) (a*UV) legs (a • q))) Λ := by
    simpa only [rescaleDegree,Function.comp_def,mul_one,Complex.ofReal_zpow] using
      composed.const_mul ((a : ℂ)^((totalDimension legs : ℤ)-degree))
  have weight : (a : ℂ)^((totalDimension legs : ℤ)-degree) * (a : ℂ) =
      (a : ℂ)^((totalDimension legs : ℤ)-degree+1) := (zpow_add_one₀ nonzero _).symm
  rw [insertionHomogeneousRHS_rescaleDegree a positive]
  simp only [Complex.real_smul,← mul_assoc] at derivative
  rw [weight] at derivative
  exact derivative

theorem InsertionFlowConditions.rescaled_single_flow {background : FlowFamily G}
    {L : InsertedFlowFamily G} {F : OversubtractedFamily G} {mu : ℝ}
    (h : InsertionFlowConditions background L F mu) (a : ℝ) (positive : 0 < a)
    (A : LocalMonomial G) (x : Spacetime) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (ir_positive : 0 < Λ) (ir_lt : Λ < UV) :
    HasDerivAt (fun scale => rescaleInsertedFlow a L [⟨A,x⟩] loop scale UV legs q)
      (insertionHomogeneousRHS (rescaleFlow a background) (rescaleInsertedFlow a L [⟨A,x⟩])
        loop Λ UV legs q) Λ := by
  rw [rescaleInsertedFlow_single]
  apply rescaleDegree_preserves_single_equation a positive
  exact h.single_flow A (a⁻¹ • x) loop (a*Λ) (a*UV) legs (a • q)
    (mul_pos positive ir_positive) (mul_lt_mul_of_pos_left ir_lt positive)

end YangMills.PerturbativeFlow
