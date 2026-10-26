import YangMills.InsertionProjectorWeights

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- A local inserted functional has its actual input degree, whereas the
noninserted integrated background has degree four. -/
def rescaleDegree (a : ℝ) (degree : ℕ) (L : FlowFamily G) : FlowFamily G :=
  fun loop Λ UV legs q => ((a ^ ((totalDimension legs : ℤ)-degree) : ℝ) : ℂ) *
    L loop (a*Λ) (a*UV) legs (a • q)

def inputEngineeringDegree : List (PositionedInsertion G) → ℕ
  | [] => 4
  | A::rest => A.monomial.dimension + (rest.map (fun B => B.monomial.dimension)).sum

def dilateInsertionPoints (a : ℝ) (input : List (PositionedInsertion G)) : List (PositionedInsertion G) :=
  input.map (fun A => ⟨A.monomial,a⁻¹ • A.position⟩)

def rescaleInsertedFlow (a : ℝ) (L : InsertedFlowFamily G) : InsertedFlowFamily G :=
  fun input => rescaleDegree a (inputEngineeringDegree input) (L (dilateInsertionPoints a input))

lemma rescaleInsertedFlow_single (a : ℝ) (L : InsertedFlowFamily G)
    (A : LocalMonomial G) (x : Spacetime) :
    rescaleInsertedFlow a L [⟨A,x⟩] = rescaleDegree a A.dimension (L [⟨A,a⁻¹ • x⟩]) := by
  simp [rescaleInsertedFlow,inputEngineeringDegree,dilateInsertionPoints]

lemma rescaleDegree_four (a : ℝ) (L : FlowFamily G) : rescaleDegree a 4 L = rescaleFlow a L := rfl

lemma momentumJet_rescaleDegree (a : ℝ) (positive : 0 < a) (degree : ℕ) (L : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) (q : Fin legs.length → Spacetime) :
    momentumJet directions (rescaleDegree a degree L loop Λ UV legs) q =
      (a : ℂ)^((totalDimension legs : ℤ)+directions.length-degree) *
        momentumJet directions (L loop (a*Λ) (a*UV) legs) (a • q) := by
  have nonzero := ne_of_gt positive
  have complex_nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  unfold rescaleDegree
  rw [momentumJet_scaledValue _ (zpow_ne_zero _ nonzero),momentumJet_scaledArgument a nonzero,
    Complex.ofReal_zpow,Complex.ofReal_pow,← mul_assoc]
  have weight : (a : ℂ)^((totalDimension legs : ℤ)-degree) * (a : ℂ)^directions.length =
      (a : ℂ)^((totalDimension legs : ℤ)+directions.length-degree) := by
    rw [← zpow_natCast,← zpow_add₀ complex_nonzero]
    congr 1
    ring
  rw [weight]

/-- Exact output-projector scaling includes all actual external functional
and multiindex momentum derivatives and the same fixed factorials. -/
theorem extractCoefficient_rescaleDegree (a : ℝ) (positive : 0 < a) (degree : ℕ)
    (L : FlowFamily G) (loop : ℕ) (Λ UV : ℝ) (m : LocalMonomial G)
    (q : Fin m.legs.length → Spacetime) :
    extractCoefficient m (rescaleDegree a degree L loop Λ UV) q =
      (a : ℂ)^((m.dimension : ℤ)-degree) *
        extractCoefficient m (L loop (a*Λ) (a*UV)) (a • q) := by
  unfold extractCoefficient
  have jet := momentumJet_rescaleDegree a positive degree L loop Λ UV m.legs m.momentumDirections q
  unfold momentumJet at jet
  rw [jet]
  have weight : (totalDimension m.legs : ℤ)+m.momentumDirections.length-degree = (m.dimension : ℤ)-degree := by
    have actual := m.projector_dimension
    omega
  rw [weight]
  ring

/-- The fixed normalized monomial insertion boundary prescription is
preserved under simultaneous positive scale/position/momentum dilation. -/
theorem SingleInsertionBoundaryConditions.rescale {L : InsertedFlowFamily G}
    {mu : ℝ} (h : SingleInsertionBoundaryConditions L mu) (a : ℝ) (positive : 0 < a) :
    SingleInsertionBoundaryConditions (rescaleInsertedFlow a L) (a⁻¹*mu) := by
  have nonzero := ne_of_gt positive
  refine {
    scale_positive := mul_pos (inv_pos.mpr positive) h.scale_positive
    smooth := ?_
    scale_jet_continuous := ?_
    invalid := ?_
    normalized := ?_
    irrelevant := ?_ }
  · intro input loop Λ UV hΛ hΛUV legs
    have smooth := h.smooth (dilateInsertionPoints a input) loop (a*Λ) (a*UV)
      (mul_pos positive hΛ) (mul_le_mul_of_nonneg_left hΛUV positive.le) legs
    simpa only [rescaleInsertedFlow,rescaleDegree,Function.comp_def,smul_eq_mul] using
      (smooth.comp (contDiff_id.const_smul a)).const_smul
        (((a ^ ((totalDimension legs : ℤ)-inputEngineeringDegree input) : ℝ)) : ℂ)
  · intro input loop UV legs directions q
    have continuous := h.scale_jet_continuous (dilateInsertionPoints a input) loop (a*UV) legs directions (a • q)
    have composed := continuous.comp (continuous_const.mul continuous_id).continuousOn
      (fun x (hx : x ∈ Set.Ioc 0 UV) =>
        (show a*x ∈ Set.Ioc 0 (a*UV) from
          ⟨mul_pos positive hx.1,mul_le_mul_of_nonneg_left hx.2 positive.le⟩))
    apply (composed.const_smul ((a : ℂ)^((totalDimension legs : ℤ)+directions.length-inputEngineeringDegree input))).congr
    intro x _
    simpa only [rescaleInsertedFlow,Function.comp_def,id_eq,smul_eq_mul] using
      momentumJet_rescaleDegree a positive (inputEngineeringDegree input)
        (L (dilateInsertionPoints a input)) loop x UV legs directions q
  · intro A invalid x loop Λ UV legs q
    rw [rescaleInsertedFlow_single]
    unfold rescaleDegree
    rw [h.invalid A invalid,mul_zero]
  · intro A B ha hb bounded loop UV scale_le
    rw [rescaleInsertedFlow_single,smul_zero,extractCoefficient_rescaleDegree a positive,smul_zero,
      mul_inv_cancel_left₀ nonzero]
    have ordered : mu ≤ a*UV := by
      have := mul_le_mul_of_nonneg_left scale_le positive.le
      simpa only [mul_inv_cancel_left₀ nonzero] using this
    rw [h.normalized A B ha hb bounded loop (a*UV) ordered]
    split_ifs with normalized
    · obtain ⟨equal,_⟩ := normalized
      subst B
      simp
    · simp
  · intro A B ha hb bounded loop UV scale_le q
    rw [rescaleInsertedFlow_single,smul_zero,extractCoefficient_rescaleDegree a positive]
    have ordered : mu ≤ a*UV := by
      have := mul_le_mul_of_nonneg_left scale_le positive.le
      simpa only [mul_inv_cancel_left₀ nonzero] using this
    rw [h.irrelevant A B ha hb bounded loop (a*UV) ordered,mul_zero]

end YangMills.PerturbativeFlow
