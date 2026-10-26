import Problems.YangMills.PerturbativeFlow
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

lemma euclideanSquare_smul (a : ℝ) (p : Spacetime) :
    euclideanSquare (a • p) = a^2 * euclideanSquare p := by
  simp only [euclideanSquare,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]

lemma exponentialRegulator_dilate (a scale : ℝ) (nonzero : a ≠ 0) (p : Spacetime) :
    exponentialRegulator (a*scale) (a • p) = exponentialRegulator scale p := by
  unfold exponentialRegulator
  rw [euclideanSquare_smul,mul_pow]
  congr 1
  by_cases scalezero : scale=0
  · simp [scalezero]
  · field_simp

lemma flowDerivativeKernel_dilate (a scale : ℝ) (nonzero : a ≠ 0) (p : Spacetime) :
    flowDerivativeKernel (a*scale) (a • p) = a⁻¹^3 * flowDerivativeKernel scale p := by
  unfold flowDerivativeKernel
  rw [exponentialRegulator_dilate _ _ nonzero,mul_pow]
  field_simp

def dilateCutoffs (s : CutoffScales) (a : ℝ) (positive : 0 < a) : CutoffScales :=
  ⟨a*s.infrared,a*s.ultraviolet,mul_pos positive s.infrared_pos,
    mul_le_mul_of_nonneg_left s.ordered positive.le⟩

lemma flowCovariance_dilate (s : CutoffScales) (a : ℝ) (positive : 0 < a) (p : Spacetime) :
    flowCovariance (dilateCutoffs s a positive) (a • p) = a⁻¹^2 * flowCovariance s p := by
  have nonzero := ne_of_gt positive
  unfold flowCovariance dilateCutoffs
  rw [euclideanSquare_smul]
  by_cases zero : euclideanSquare p = 0
  · simp [zero,mul_inv_rev,mul_pow]
    ring
  · have scaled_nonzero : a^2 * euclideanSquare p ≠ 0 := mul_ne_zero (pow_ne_zero _ nonzero) zero
    rw [if_neg scaled_nonzero,if_neg zero,
      exponentialRegulator_dilate _ _ nonzero,exponentialRegulator_dilate _ _ nonzero]
    field_simp

lemma basicDerivativeCovariance_dilate (a scale : ℝ) (positive : 0 < a)
    (K L : BasicField G) (p : Spacetime) :
    basicDerivativeCovariance (a*scale) K L (a • p) =
      a ^ ((K.dimension : ℤ) + L.dimension - 5) * basicDerivativeCovariance scale K L p := by
  have nonzero := ne_of_gt positive
  cases K <;> cases L <;>
    simp only [basicDerivativeCovariance,BasicField.dimension] <;>
    try simp
  all_goals split_ifs <;> try simp
  all_goals rw [flowDerivativeKernel_dilate _ _ nonzero]
  all_goals try rw [euclideanSquare_smul]
  all_goals norm_num [zpow_neg,zpow_ofNat]
  all_goals field_simp

/-- Canonical momentum amplitude rescaling. The full background functional
has dimension four, while its external coefficient has dimension 4-sum d. -/
def rescaleFlow (a : ℝ) (L : FlowFamily G) : FlowFamily G :=
  fun loop Λ UV legs q => ((a ^ ((totalDimension legs : ℤ)-4) : ℝ) : ℂ) *
    L loop (a*Λ) (a*UV) legs (a • q)

@[simp] lemma totalDimension_cons (K : ExternalLeg G) (legs : List (ExternalLeg G)) :
    totalDimension (K::legs) = K.dimension + totalDimension legs := rfl

lemma prependMomenta_smul (a : ℝ) {legs : List (ExternalLeg G)} (K : ExternalLeg G)
    (p : Spacetime) (q : Fin legs.length → Spacetime) :
    a • prependMomenta K p q = prependMomenta K (a • p) (a • q) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma selectedMomenta_smul (a : ℝ) (legs : List (ExternalLeg G))
    (s : Finset (Fin legs.length)) (q : Fin legs.length → Spacetime) :
    selectedMomenta legs s (a • q) = a • selectedMomenta legs s q := rfl

lemma selectedMomentum_smul (a : ℝ) (legs : List (ExternalLeg G))
    (s : Finset (Fin legs.length)) (q : Fin legs.length → Spacetime) :
    selectedMomentum legs s (a • q) = a • selectedMomentum legs s q := by
  simp [selectedMomentum,Finset.smul_sum]

lemma totalDimension_selected (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length)) :
    totalDimension (selectedLegs legs s) = ∑ i ∈ s, (legs.get i).dimension := by
  classical
  unfold totalDimension selectedLegs selectedIndices
  rw [List.map_map]
  simpa only [Finset.sort_toFinset, Function.comp_def] using
    (List.sum_toFinset (fun i => (legs.get i).dimension) (s.sort_nodup (· ≤ ·))).symm

lemma totalDimension_partition (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length)) :
    totalDimension (selectedLegs legs s) + totalDimension (selectedLegs legs (complementIndices legs s)) =
      totalDimension legs := by
  classical
  rw [totalDimension_selected,totalDimension_selected]
  change (∑ i ∈ s, (legs.get i).dimension) + (∑ i ∈ sᶜ, (legs.get i).dimension) = _
  rw [Finset.sum_add_sum_compl,← List.sum_ofFn]
  simp [totalDimension]

lemma linearFlowIntegrand_rescale (a : ℝ) (positive : 0 < a) (L : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand (rescaleFlow a L) loop Λ UV legs q p =
      (a : ℂ)^((totalDimension legs : ℤ)+1) *
        linearFlowIntegrand L loop (a*Λ) (a*UV) legs (a • q) (a • p) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  unfold linearFlowIntegrand
  by_cases loopzero : loop=0
  · simp only [loopzero,ite_true,mul_zero]
  · simp only [loopzero,ite_false,rescaleFlow,totalDimension_cons,ExternalLeg.dimension,
      prependMomenta_smul,smul_neg,Complex.ofReal_zpow,Nat.cast_add]
    rw [← mul_div_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N _
    have covariance := basicDerivativeCovariance_dilate a Λ positive M N (-p)
    simp only [smul_neg] at covariance
    rw [covariance,Complex.ofReal_mul,Complex.ofReal_zpow]
    have weight : (a : ℂ)^((M.dimension : ℤ)+(N.dimension+totalDimension legs)-4) =
        (a : ℂ)^((totalDimension legs : ℤ)+1) * (a : ℂ)^((M.dimension : ℤ)+N.dimension-5) := by
      rw [← zpow_add₀ nonzero]
      congr 1
      ring
    rw [weight]
    ring

lemma linearFlowRHS_rescale (a : ℝ) (positive : 0 < a) (L : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    linearFlowRHS (rescaleFlow a L) loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-3) *
        linearFlowRHS L loop (a*Λ) (a*UV) legs (a • q) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  unfold linearFlowRHS
  simp_rw [linearFlowIntegrand_rescale a positive]
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume _ a (hR := positive.le)]
  have dimension : Module.finrank ℝ Spacetime = 4 := by simp [Spacetime]
  rw [dimension]
  rw [Complex.real_smul]
  rw [← mul_assoc]
  push_cast
  have fourth : ((a : ℂ)^4)⁻¹ = (a : ℂ)^(-4 : ℤ) := by simp [zpow_neg,zpow_ofNat]
  rw [fourth,← zpow_add₀ nonzero]
  congr 2
  ring

lemma quadraticSplit_rescale (a : ℝ) (positive : 0 < a) (L F : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) :
    quadraticSplit (rescaleFlow a L) (rescaleFlow a F) loop leftLoop Λ UV legs q s =
      (a : ℂ)^((totalDimension legs : ℤ)-3) *
        quadraticSplit L F loop leftLoop (a*Λ) (a*UV) legs (a • q) s := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have partition : (totalDimension (selectedLegs legs s) : ℤ) +
      totalDimension (selectedLegs legs (complementIndices legs s)) = totalDimension legs := by
    exact_mod_cast totalDimension_partition legs s
  unfold quadraticSplit
  simp only [rescaleFlow,totalDimension_cons,ExternalLeg.dimension,prependMomenta_smul,
    selectedMomenta_smul,selectedMomentum_smul,smul_neg,Complex.ofReal_zpow,Nat.cast_add]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro N _
  rw [basicDerivativeCovariance_dilate a Λ positive M N,
    Complex.ofReal_mul,Complex.ofReal_zpow]
  have weight :
      (a : ℂ)^((N.dimension : ℤ)+totalDimension (selectedLegs legs s)-4) *
        (a : ℂ)^((M.dimension : ℤ)+totalDimension (selectedLegs legs (complementIndices legs s))-4) =
      (a : ℂ)^((totalDimension legs : ℤ)-3) * (a : ℂ)^((M.dimension : ℤ)+N.dimension-5) := by
    rw [← zpow_add₀ nonzero,← zpow_add₀ nonzero]
    congr 1
    linear_combination partition
  linear_combination weight * (splitSign legs s *
    (basicDerivativeCovariance Λ M N (selectedMomentum legs s q) : ℂ) *
    L leftLoop (a*Λ) (a*UV) (.inl N :: selectedLegs legs s)
      (prependMomenta (.inl N) (-(a • selectedMomentum legs s q))
        (a • selectedMomenta legs s q)) *
    F (loop-leftLoop) (a*Λ) (a*UV) (.inl M :: selectedLegs legs (complementIndices legs s))
      (prependMomenta (.inl M) (a • selectedMomentum legs s q)
        (a • selectedMomenta legs (complementIndices legs s) q)))

lemma quadraticFlowRHS_rescale (a : ℝ) (positive : 0 < a) (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    quadraticFlowRHS (rescaleFlow a L) (rescaleFlow a F) loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-3) *
        quadraticFlowRHS L F loop (a*Λ) (a*UV) legs (a • q) := by
  unfold quadraticFlowRHS
  simp_rw [quadraticSplit_rescale a positive,Finset.mul_sum]

lemma backgroundFlowRHS_rescale (a : ℝ) (positive : 0 < a) (L : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    backgroundFlowRHS (rescaleFlow a L) loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-3) *
        backgroundFlowRHS L loop (a*Λ) (a*UV) legs (a • q) := by
  unfold backgroundFlowRHS
  rw [linearFlowRHS_rescale a positive,quadraticFlowRHS_rescale a positive]
  ring

lemma insertionHomogeneousRHS_rescale (a : ℝ) (positive : 0 < a) (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    insertionHomogeneousRHS (rescaleFlow a L) (rescaleFlow a F) loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-3) *
        insertionHomogeneousRHS L F loop (a*Λ) (a*UV) legs (a • q) := by
  unfold insertionHomogeneousRHS
  rw [linearFlowRHS_rescale a positive,quadraticFlowRHS_rescale a positive]
  ring

/-- A true solution of the actual nonlinear flow equation transforms to a
solution of that SAME equation. No covariance of the proposed solution is
assumed: the loop Jacobian and quadratic terms above establish the RHS. -/
theorem rescaleFlow_preserves_flow_equation (a : ℝ) (positive : 0 < a)
    (L : FlowFamily G) (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime)
    (equation : HasDerivAt (fun scale => L loop scale (a*UV) legs (a • q))
      (backgroundFlowRHS L loop (a*Λ) (a*UV) legs (a • q)) (a*Λ)) :
    HasDerivAt (fun scale => rescaleFlow a L loop scale UV legs q)
      (backgroundFlowRHS (rescaleFlow a L) loop Λ UV legs q) Λ := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have composed := equation.scomp Λ ((hasDerivAt_id Λ).const_mul a)
  have derivative : HasDerivAt (fun scale => rescaleFlow a L loop scale UV legs q)
      ((a : ℂ)^((totalDimension legs : ℤ)-4) *
        (a • backgroundFlowRHS L loop (a*Λ) (a*UV) legs (a • q))) Λ := by
    simpa only [rescaleFlow,Function.comp_def,mul_one,Complex.ofReal_zpow] using
      composed.const_mul ((a : ℂ)^((totalDimension legs : ℤ)-4))
  have weight : (a : ℂ)^((totalDimension legs : ℤ)-4) * (a : ℂ) =
      (a : ℂ)^((totalDimension legs : ℤ)-3) := by
    rw [← zpow_add_one₀ nonzero]
    congr 1
    ring
  rw [backgroundFlowRHS_rescale a positive]
  simp only [Complex.real_smul,← mul_assoc] at derivative
  rw [weight] at derivative
  exact derivative

def rescaleScaleCoupling (a : ℝ) (A : ScaleCouplingFamily G) : ScaleCouplingFamily G :=
  fun mu g => rescaleFlow a (A (a*mu) g)

lemma balancedMomenta_smul (a : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (balanced : BalancedMomenta legs q) :
    BalancedMomenta legs (a • q) := by
  unfold BalancedMomenta at balanced ⊢
  simp only [Pi.smul_apply]
  rw [← Finset.smul_sum,balanced,smul_zero]

/-- The concrete transformed subtraction-scale family satisfies the actual
flow part of the fixed prescription at every admissible scale and momentum. -/
theorem CoefficientFlowConditions.rescaled_flow {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (h : CoefficientFlowConditions e scheme A) (a : ℝ) (positive : 0 < a)
    (mu g : ℝ) (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (mu_positive : 0 < mu) (mu_le : mu ≤ UV)
    (ir_positive : 0 < Λ) (ir_lt : Λ < UV) (nonempty : legs ≠ []) (balanced : BalancedMomenta legs q) :
    HasDerivAt (fun scale => rescaleScaleCoupling a A mu g loop scale UV legs q)
      (backgroundFlowRHS (rescaleScaleCoupling a A mu g) loop Λ UV legs q) Λ := by
  apply rescaleFlow_preserves_flow_equation a positive
  exact h.flow (a*mu) g loop (a*Λ) (a*UV) legs (a • q)
    (mul_pos positive mu_positive) (mul_le_mul_of_nonneg_left mu_le positive.le)
    (mul_pos positive ir_positive) (mul_lt_mul_of_pos_left ir_lt positive)
    nonempty (balancedMomenta_smul a legs q balanced)

end YangMills.PerturbativeFlow
