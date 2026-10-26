import Problems.YangMills.FiniteFlowDilation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

/-- Actual nonzero scalar coordinate change, including on nonsmooth test
families: the totalized derivative convention is transported by an equiv. -/
def scalarCoordinateEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (nonzero : a ≠ 0) : E ≃L[ℝ] E where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E a nonzero
  continuous_toFun := continuous_const_smul a
  continuous_invFun := continuous_const_smul a⁻¹

lemma momentumJet_scaledArgument (a : ℝ) (nonzero : a ≠ 0)
    {legs : List (ExternalLeg G)} (directions : List (Fin legs.length × Fin 4))
    (F : (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime) :
    momentumJet directions (fun p => F (a • p)) q =
      ((a ^ directions.length : ℝ) : ℂ) * momentumJet directions F (a • q) := by
  let e := scalarCoordinateEquiv (Fin legs.length → Spacetime) a nonzero
  have derivative := e.iteratedFDerivWithin_comp_right F uniqueDiffOn_univ
    (Set.mem_univ (e q)) directions.length
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ] at derivative
  unfold momentumJet
  change iteratedFDeriv ℝ directions.length (F ∘ e) q _ = _
  rw [derivative]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (iteratedFDeriv ℝ directions.length F (a • q))
    (fun i => a • (Pi.single (directions.get i).1
      (Pi.single (directions.get i).2 1 : Spacetime) : Fin legs.length → Spacetime)) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Complex.real_smul]

lemma momentumJet_scaledValue (a : ℝ) (nonzero : a ≠ 0)
    {legs : List (ExternalLeg G)} (directions : List (Fin legs.length × Fin 4))
    (F : (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime) :
    momentumJet directions (fun p => (a : ℂ) * F p) q =
      (a : ℂ) * momentumJet directions F q := by
  let e := scalarCoordinateEquiv ℂ a nonzero
  have derivative := e.iteratedFDeriv_comp_left (f := F) (x := q) (i := directions.length)
  unfold momentumJet
  change iteratedFDeriv ℝ directions.length (e ∘ F) q _ = _
  rw [derivative]
  rfl

/-- Exact Taylor-jet scaling, with no hidden smoothness/integrability premise.
Nonzero linear coordinate changes preserve the actual totalized derivatives. -/
theorem momentumJet_rescaleFlow (a : ℝ) (positive : 0 < a) (L : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) (q : Fin legs.length → Spacetime) :
    momentumJet directions (rescaleFlow a L loop Λ UV legs) q =
      (a : ℂ)^((totalDimension legs : ℤ)+directions.length-4) *
        momentumJet directions (L loop (a*Λ) (a*UV) legs) (a • q) := by
  have nonzero := ne_of_gt positive
  have complex_nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  unfold rescaleFlow
  rw [momentumJet_scaledValue _ (zpow_ne_zero _ nonzero),momentumJet_scaledArgument a nonzero,
    Complex.ofReal_zpow,Complex.ofReal_pow]
  rw [← mul_assoc]
  have weight : (a : ℂ)^((totalDimension legs : ℤ)-4) * (a : ℂ)^directions.length =
      (a : ℂ)^((totalDimension legs : ℤ)+directions.length-4) := by
    rw [← zpow_natCast,← zpow_add₀ complex_nonzero]
    congr 1
    ring
  rw [weight]

/-- Irrelevant UV Taylor data are preserved by the actual transformed family. -/
theorem CoefficientFlowConditions.rescaled_irrelevant_uv {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (h : CoefficientFlowConditions e scheme A) (a : ℝ) (positive : 0 < a)
    (mu g : ℝ) (loop : ℕ) (UV : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) (q : Fin legs.length → Spacetime)
    (mu_positive : 0 < mu) (mu_le : mu ≤ UV) (reduced : ReducedDirections legs directions)
    (irrelevant : 4 < totalDimension legs + directions.length) :
    momentumJet directions (rescaleScaleCoupling a A mu g loop UV UV legs) q = 0 := by
  rw [rescaleScaleCoupling,momentumJet_rescaleFlow a positive]
  rw [h.irrelevant_uv (a*mu) g loop (a*UV) legs directions (a • q)
    (mul_pos positive mu_positive) (mul_le_mul_of_nonneg_left mu_le positive.le) reduced irrelevant,mul_zero]

/-- The fixed marginal normalization is exactly invariant, since its
engineering exponent is zero. No desired covariance of A is assumed. -/
theorem CoefficientFlowConditions.rescaled_marginal {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (h : CoefficientFlowConditions e scheme A) (a : ℝ) (positive : 0 < a)
    (mu g : ℝ) (loop : ℕ) (UV : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (mu_positive : 0 < mu) (mu_le : mu ≤ UV) (reduced : ReducedDirections legs directions)
    (marginal : totalDimension legs + directions.length = 4) :
    marginalJet (rescaleScaleCoupling a A mu g) loop mu UV legs directions =
      momentumJet directions
        (fun q => marginalNormalization e scheme loop g legs (conservingMomenta legs q)) 0 := by
  unfold marginalJet rescaleScaleCoupling
  rw [momentumJet_rescaleFlow a positive,smul_zero]
  have exponent : (totalDimension legs : ℤ)+directions.length-4 = 0 := by omega
  rw [exponent,zpow_zero,one_mul]
  exact h.marginal (a*mu) g loop (a*UV) legs directions (mul_pos positive mu_positive)
    (mul_le_mul_of_nonneg_left mu_le positive.le) reduced marginal

/-- Relevant massless IR Taylor normalization is also preserved exactly. -/
theorem CoefficientFlowConditions.rescaled_relevant_ir {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (h : CoefficientFlowConditions e scheme A) (a : ℝ) (positive : 0 < a)
    (mu g : ℝ) (loop : ℕ) (UV : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (mu_positive : 0 < mu) (mu_le : mu ≤ UV) (reduced : ReducedDirections legs directions)
    (relevant : totalDimension legs + directions.length < 4) :
    momentumJet directions (rescaleScaleCoupling a A mu g loop 0 UV legs) 0 = 0 := by
  rw [rescaleScaleCoupling,momentumJet_rescaleFlow a positive,smul_zero,mul_zero]
  rw [h.relevant_ir (a*mu) g loop (a*UV) legs directions (mul_pos positive mu_positive)
    (mul_le_mul_of_nonneg_left mu_le positive.le) reduced relevant,mul_zero]

lemma conservingMomenta_smul (a : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    conservingMomenta legs (a • q) = a • conservingMomenta legs q := by
  funext i
  simp only [conservingMomenta,Pi.smul_apply]
  split_ifs
  · rw [smul_neg,Finset.smul_sum]
  · rfl

lemma totalDimension_permuted (legs : List (ExternalLeg G)) (pi : Equiv.Perm (Fin legs.length)) :
    totalDimension (permutedLegs legs pi) = totalDimension legs := by
  unfold totalDimension permutedLegs
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  calc
    _ = ∑ i : Fin legs.length, (legs.get i).dimension := Equiv.sum_comp pi _
    _ = _ := by rw [← List.sum_ofFn]; simp

lemma permutedMomenta_smul (a : ℝ) (legs : List (ExternalLeg G))
    (pi : Equiv.Perm (Fin legs.length)) (q : Fin legs.length → Spacetime) :
    permutedMomenta legs pi (a • q) = a • permutedMomenta legs pi q := rfl

lemma tendsto_positive_scale (a : ℝ) (positive : 0 < a) :
    Filter.Tendsto (fun x : ℝ => a*x) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using! ((continuous_const.mul continuous_id).tendsto (0 : ℝ)).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos positive hx

/-- The whole concrete finite background prescription is preserved:
nonlinear flow, actual regularity/statistics, massless relevant data,
fixed marginal data and irrelevant local UV boundary all transform together. -/
theorem CoefficientFlowConditions.rescale {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (h : CoefficientFlowConditions e scheme A) (a : ℝ) (positive : 0 < a) :
    CoefficientFlowConditions e scheme (rescaleScaleCoupling a A) := by
  have positive_mu (mu : ℝ) (hm : 0 < mu) : 0 < a*mu := mul_pos positive hm
  have ordered (mu UV : ℝ) (hm : mu ≤ UV) : a*mu ≤ a*UV :=
    mul_le_mul_of_nonneg_left hm positive.le
  refine {
    local_symmetries := h.local_symmetries
    momentum_smooth := ?_
    coupling_smooth := ?_
    joint_coupling_momentum_smooth := ?_
    positive_scale_jet_continuity := ?_
    reduced_extension := ?_
    statistics := ?_
    graded_symmetry := ?_
    vacuum_subtraction := ?_
    no_free_interaction := ?_
    loop_integrable := ?_
    flow := h.rescaled_flow a positive
    irrelevant_uv := h.rescaled_irrelevant_uv a positive
    relevant_ir_regularity := ?_
    relevant_ir := h.rescaled_relevant_ir a positive
    relevant_ir_limit := ?_
    marginal := h.rescaled_marginal a positive }
  · intro mu g loop Λ UV legs hmu hmuUV hΛ hΛUV
    simpa only [rescaleScaleCoupling,rescaleFlow,Function.comp_def,smul_eq_mul] using!
      ((h.momentum_smooth (a*mu) g loop (a*Λ) (a*UV) legs
      (positive_mu mu hmu) (ordered mu UV hmuUV) (positive_mu Λ hΛ) (ordered Λ UV hΛUV)).comp
      (contDiff_id.const_smul a)).const_smul ((((a ^ ((totalDimension legs : ℤ)-4) : ℝ)) : ℂ))
  · intro mu loop Λ UV legs q hmu hmuUV hΛ hΛUV
    simpa only [rescaleScaleCoupling,rescaleFlow,Function.comp_def,smul_eq_mul] using!
      (h.coupling_smooth (a*mu) loop (a*Λ) (a*UV) legs (a • q)
      (positive_mu mu hmu) (ordered mu UV hmuUV) (positive_mu Λ hΛ) (ordered Λ UV hΛUV)).const_smul ((((a ^ ((totalDimension legs : ℤ)-4) : ℝ)) : ℂ))
  · intro mu loop Λ UV legs hmu hmuUV hΛ hΛUV
    simpa only [rescaleScaleCoupling,rescaleFlow,Function.comp_def,smul_eq_mul] using!
      ((h.joint_coupling_momentum_smooth (a*mu) loop (a*Λ) (a*UV) legs
      (positive_mu mu hmu) (ordered mu UV hmuUV) (positive_mu Λ hΛ) (ordered Λ UV hΛUV)).comp
      (contDiff_fst.prodMk (contDiff_snd.const_smul a))).const_smul ((((a ^ ((totalDimension legs : ℤ)-4) : ℝ)) : ℂ))
  · intro mu g loop UV legs directions q hmu hmuUV
    have hj := h.positive_scale_jet_continuity (a*mu) g loop (a*UV) legs directions (a • q)
      (positive_mu mu hmu) (ordered mu UV hmuUV)
    have hc := hj.comp (continuous_const.mul continuous_id).continuousOn
      (fun x (hx : x ∈ Set.Ioc 0 UV) =>
        (show a*x ∈ Set.Ioc 0 (a*UV) from ⟨positive_mu x hx.1,ordered x UV hx.2⟩))
    apply (hc.const_smul ((a : ℂ)^((totalDimension legs : ℤ)+directions.length-4))).congr
    intro x _
    simpa only [rescaleScaleCoupling,Function.comp_def,id_eq,smul_eq_mul] using!
      momentumJet_rescaleFlow a positive (A (a*mu) g) loop x UV legs directions q
  · intro mu g loop Λ UV legs q
    unfold rescaleScaleCoupling rescaleFlow
    rw [h.reduced_extension (a*mu) g loop (a*Λ) (a*UV) legs (a • q),conservingMomenta_smul]
  · intro mu g loop Λ UV legs q forbidden
    unfold rescaleScaleCoupling rescaleFlow
    rw [h.statistics (a*mu) g loop (a*Λ) (a*UV) legs (a • q) forbidden,mul_zero]
  · intro mu g loop Λ UV legs q pi balanced
    unfold rescaleScaleCoupling rescaleFlow
    rw [totalDimension_permuted,← permutedMomenta_smul,
      h.graded_symmetry (a*mu) g loop (a*Λ) (a*UV) legs (a • q) pi (balancedMomenta_smul a legs q balanced)]
    ring
  · intro mu g loop Λ UV q
    unfold rescaleScaleCoupling rescaleFlow
    rw [h.vacuum_subtraction,mul_zero]
  · intro mu g Λ UV legs q short
    unfold rescaleScaleCoupling rescaleFlow
    rw [h.no_free_interaction (a*mu) g (a*Λ) (a*UV) legs (a • q) short,mul_zero]
  · intro mu g loop Λ UV legs q hmu hmuUV hΛ hΛUV balanced
    have integrable := h.loop_integrable (a*mu) g loop (a*Λ) (a*UV) legs (a • q)
      (positive_mu mu hmu) (ordered mu UV hmuUV) (positive_mu Λ hΛ)
      (mul_lt_mul_of_pos_left hΛUV positive) (balancedMomenta_smul a legs q balanced)
    change Integrable (linearFlowIntegrand (rescaleFlow a (A (a*mu) g)) loop Λ UV legs q)
    apply Integrable.congr ((integrable.comp_smul (ne_of_gt positive)).const_mul
      ((a : ℂ)^((totalDimension legs : ℤ)+1)))
    filter_upwards [] with p
    exact (linearFlowIntegrand_rescale a positive (A (a*mu) g) loop Λ UV legs q p).symm
  · intro mu g loop UV legs directions hmu hmuUV reduced relevant
    have regular := h.relevant_ir_regularity (a*mu) g loop (a*UV) legs directions
      (positive_mu mu hmu) (ordered mu UV hmuUV) reduced relevant
    have regular_scaled : ContDiffAt ℝ directions.length (A (a*mu) g loop 0 (a*UV) legs)
        (a • (0 : Fin legs.length → Spacetime)) := by simpa only [smul_zero] using! regular
    have composed := regular_scaled.comp (0 : Fin legs.length → Spacetime)
      (contDiff_id.const_smul a).contDiffAt
    unfold rescaleScaleCoupling rescaleFlow
    simpa only [mul_zero,Function.comp_def,smul_eq_mul] using! composed.const_smul
      (((a ^ ((totalDimension legs : ℤ)-4) : ℝ)) : ℂ)
  · intro mu g loop UV legs directions hmu hmuUV reduced relevant
    have limit := (h.relevant_ir_limit (a*mu) g loop (a*UV) legs directions
      (positive_mu mu hmu) (ordered mu UV hmuUV) reduced relevant).comp (tendsto_positive_scale a positive)
    have multiplied := limit.const_mul ((a : ℂ)^((totalDimension legs : ℤ)+directions.length-4))
    simpa only [rescaleScaleCoupling,momentumJet_rescaleFlow a positive,smul_zero,mul_zero] using! multiplied

theorem rescaleScaleCoupling_inverse (a : ℝ) (nonzero : a ≠ 0) (A : ScaleCouplingFamily G) :
    rescaleScaleCoupling a⁻¹ (rescaleScaleCoupling a A) = A := by
  funext mu g loop Λ UV legs q
  simp only [rescaleScaleCoupling,rescaleFlow,Complex.ofReal_zpow,
    mul_inv_cancel_left₀ nonzero,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  have factors : ((a⁻¹ : ℝ) : ℂ)^((totalDimension legs : ℤ)-4) *
      (a : ℂ)^((totalDimension legs : ℤ)-4) = 1 := by
    rw [← mul_zpow,← Complex.ofReal_mul,inv_mul_cancel₀ nonzero]
    simp
  rw [← mul_assoc,factors,one_mul]

/-- A genuine equivalence of the SAME fixed finite flow/normalization
problem, including all its analytical admissibility conditions. -/
theorem CoefficientFlowConditions.rescale_iff {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (a : ℝ) (positive : 0 < a) :
    CoefficientFlowConditions e scheme (rescaleScaleCoupling a A) ↔
      CoefficientFlowConditions e scheme A := by
  constructor
  · intro h
    have back := h.rescale a⁻¹ (inv_pos.mpr positive)
    rw [rescaleScaleCoupling_inverse a (ne_of_gt positive) A] at back
    exact back
  · exact fun h => h.rescale a positive

theorem GraphHomogeneous.rescale {A : ScaleCouplingFamily G} (h : GraphHomogeneous A) (a : ℝ) :
    GraphHomogeneous (rescaleScaleCoupling a A) := by
  intro mu loop Λ UV legs q g
  unfold rescaleScaleCoupling rescaleFlow
  rw [h (a*mu) loop (a*Λ) (a*UV) legs (a • q) g]
  ring

end YangMills.PerturbativeFlow
