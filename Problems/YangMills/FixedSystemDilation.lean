import Problems.YangMills.InsertionFlowDilation
import Problems.YangMills.PerturbativeCoefficientLimits

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Coupling and momentum are transported jointly; coefficient projectors
therefore remain on the SAME smooth generated family. -/
theorem CoupledInsertionFlowConditions.rescale {background : ℝ → FlowFamily G}
    {L : ℝ → InsertedFlowFamily G} {F : ℝ → OversubtractedFamily G} {mu : ℝ}
    (h : CoupledInsertionFlowConditions background L F mu) (a : ℝ) (positive : 0 < a) :
    CoupledInsertionFlowConditions (fun g => rescaleFlow a (background g))
      (fun g => rescaleInsertedFlow a (L g)) (fun g => rescaleOversubtractions a (F g)) (a⁻¹*mu) := by
  refine {
    per_coupling := fun g => (h.per_coupling g).rescale a positive
    single_joint_smooth := ?_
    oversubtraction_joint_smooth := ?_ }
  · intro input loop Λ UV legs ir_positive ordered
    have smooth := h.single_joint_smooth (dilateInsertionPoints a input) loop (a*Λ) (a*UV) legs
      (mul_pos positive ir_positive) (mul_le_mul_of_nonneg_left ordered positive.le)
    simpa only [rescaleInsertedFlow,rescaleDegree,Function.comp_def,smul_eq_mul] using!
      (smooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul a))).const_smul
        (((a ^ ((totalDimension legs : ℤ)-inputEngineeringDegree input) : ℝ)) : ℂ)
  · intro D input loop Λ UV legs ir_positive ordered
    have smooth := h.oversubtraction_joint_smooth D (dilateInsertionPoints a input) loop (a*Λ) (a*UV) legs
      (mul_pos positive ir_positive) (mul_le_mul_of_nonneg_left ordered positive.le)
    simpa only [rescaleOversubtractions,rescaleDegree,Function.comp_def,smul_eq_mul] using!
      (smooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul a))).const_smul
        (((a ^ ((totalDimension legs : ℤ)-positionedInsertionDegreeSum input) : ℝ)) : ℂ)

/-- Actual transformed finite prescription: the same G, frame, marginal
scheme, background equation and full single/multiple-insertion equation.
This constructs a solution from a solution; equality with a chosen solution
is a separate uniqueness theorem, never an assumed covariance field. -/
def FixedFlowSystem.dilate {B : InvariantForm G} {e : ColorFrame B}
    (S : FixedFlowSystem e) (a : ℝ) (positive : 0 < a) : FixedFlowSystem e where
  referenceScale := ⟨a⁻¹*S.referenceScale.val,mul_pos (inv_pos.mpr positive) S.referenceScale.property⟩
  localScheme := S.localScheme
  background := rescaleScaleCoupling a S.background
  insertions := fun mu g => rescaleInsertedFlow a (S.insertions (a*mu) g)
  oversubtractions := fun mu g => rescaleOversubtractions a (S.oversubtractions (a*mu) g)
  background_equations := S.background_equations.rescale a positive
  insertion_equations := by
    intro mu mu_positive
    have transformed := (S.insertion_equations (a*mu) (mul_pos positive mu_positive)).rescale a positive
    simpa only [rescaleScaleCoupling,inv_mul_cancel_left₀ (ne_of_gt positive)] using! transformed

@[simp] theorem FixedFlowSystem.dilate_same_scheme {B : InvariantForm G} {e : ColorFrame B}
    (S : FixedFlowSystem e) (a : ℝ) (positive : 0 < a) :
    (S.dilate a positive).localScheme = S.localScheme := rfl

end YangMills.PerturbativeFlow
