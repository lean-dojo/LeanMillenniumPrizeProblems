import Problems.YangMills.ReducedMomentumDeterminacy

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative

/-- The actual positive-cutoff interval includes its UV endpoint. No
endpoint differentiability or passage through the singular IR cutoff is used. -/
theorem positiveScale_constancy {f : ℝ → ℂ} {UV : ℝ}
    (continuous : ContinuousOn f (Set.Ioc 0 UV))
    (zeroDerivative : ∀ x, 0 < x → x < UV → HasDerivAt f 0 x)
    {x y : ℝ} (hx : 0 < x) (hxUV : x ≤ UV) (hy : 0 < y) (hyUV : y ≤ UV) :
    f x = f y := by
  have hmin : 0 < min x y := lt_min hx hy
  have hc : ContinuousOn f (Set.Icc (min x y) UV) :=
    continuous.mono (fun z hz => ⟨hmin.trans_le hz.1, hz.2⟩)
  have hd : ∀ z ∈ Set.Ico (min x y) UV, HasDerivWithinAt f 0 (Set.Ici z) z := by
    intro z hz
    exact (zeroDerivative z (hmin.trans_le hz.1) hz.2).hasDerivWithinAt
  have h := constant_of_has_deriv_right_zero hc hd
  exact (h x ⟨min_le_left _ _, hxUV⟩).trans (h y ⟨min_le_right _ _, hyUV⟩).symm

theorem conservingMomenta_balanced (G : CompactSimpleGaugeGroup)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    BalancedMomenta legs (conservingMomenta legs q) := by
  classical
  cases legs with
  | nil => simp [BalancedMomenta]
  | cons K rest =>
    have first (i : Fin rest.length) : i.val + 1 < rest.length + 1 := by omega
    have filtered : (∑ j ∈ (Finset.univ : Finset (Fin (rest.length+1))).filter
        (fun j => j.val+1 < rest.length+1), q j) =
        ∑ i : Fin rest.length, q i.castSucc := by
      rw [Finset.sum_filter, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, lt_self_iff_false, if_false, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rw [if_pos (first i)]
    unfold BalancedMomenta conservingMomenta
    simp only [List.length_cons]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [filtered]
    have hsum : (∑ i : Fin rest.length, if i.val+1 = rest.length+1 then
        -(∑ i : Fin rest.length, q i.castSucc) else q i.castSucc) =
        ∑ i : Fin rest.length, q i.castSucc := by
      apply Finset.sum_congr rfl
      intro i _
      rw [if_neg (by have hi := first i; omega)]
    rw [hsum]
    simp

/-- Equal actual right-hand sides force the difference of two regulated
amplitudes to be cutoff-constant, with the UV endpoint included. -/
theorem flowDifference_scaleConstant {G : CompactSimpleGaugeGroup}
    {B : InvariantForm G} {e : ColorFrame B} {scheme : LocalMarginalData G}
    {A C : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A) (hC : CoefficientFlowConditions e scheme C)
    (μ g UV : ℝ) (loop : ℕ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (nonempty : legs ≠ []) (balanced : BalancedMomenta legs q)
    (rhs : ∀ Λ, 0 < Λ → Λ < UV →
      backgroundFlowRHS (A μ g) loop Λ UV legs q =
        backgroundFlowRHS (C μ g) loop Λ UV legs q)
    {x y : ℝ} (hx : 0 < x) (hxUV : x ≤ UV) (hy : 0 < y) (hyUV : y ≤ UV) :
    A μ g loop x UV legs q - C μ g loop x UV legs q =
      A μ g loop y UV legs q - C μ g loop y UV legs q := by
  apply positiveScale_constancy (f := fun Λ => A μ g loop Λ UV legs q - C μ g loop Λ UV legs q) (UV := UV)
  · have ca := hA.positive_scale_jet_continuity μ g loop UV legs [] q hμ hUV
    have cc := hC.positive_scale_jet_continuity μ g loop UV legs [] q hμ hUV
    have ha : ContinuousOn (fun Λ => A μ g loop Λ UV legs q) (Set.Ioc 0 UV) := by
      simpa [momentumJet, iteratedFDeriv_zero_apply] using! ca
    have hc : ContinuousOn (fun Λ => C μ g loop Λ UV legs q) (Set.Ioc 0 UV) := by
      simpa [momentumJet, iteratedFDeriv_zero_apply] using! cc
    exact ha.sub hc
  · intro Λ hp hlt
    have d := (hA.flow μ g loop Λ UV legs q hμ hUV hp hlt nonempty balanced).sub
      (hC.flow μ g loop Λ UV legs q hμ hUV hp hlt nonempty balanced)
    simpa only [rhs Λ hp hlt, sub_self] using! d
  all_goals assumption

/-- Conserving extension transports the actual scale constancy to all
external coordinate values, as required before taking momentum derivatives. -/
theorem flowDifference_scaleConstant_all {G : CompactSimpleGaugeGroup}
    {B : InvariantForm G} {e : ColorFrame B} {scheme : LocalMarginalData G}
    {A C : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A) (hC : CoefficientFlowConditions e scheme C)
    (μ g UV : ℝ) (loop : ℕ) (legs : List (ExternalLeg G))
    (hμ : 0 < μ) (hUV : μ ≤ UV) (nonempty : legs ≠ [])
    (rhs : ∀ Λ q, 0 < Λ → Λ < UV → BalancedMomenta legs q →
      backgroundFlowRHS (A μ g) loop Λ UV legs q =
        backgroundFlowRHS (C μ g) loop Λ UV legs q)
    {x y : ℝ} (hx : 0 < x) (hxUV : x ≤ UV) (hy : 0 < y) (hyUV : y ≤ UV) :
    (fun q => A μ g loop x UV legs q - C μ g loop x UV legs q) =
      (fun q => A μ g loop y UV legs q - C μ g loop y UV legs q) := by
  funext q
  rw [hA.reduced_extension μ g loop x UV legs q, hC.reduced_extension μ g loop x UV legs q,
    hA.reduced_extension μ g loop y UV legs q, hC.reduced_extension μ g loop y UV legs q]
  exact flowDifference_scaleConstant hA hC μ g UV loop legs _ hμ hUV nonempty
    (conservingMomenta_balanced G legs q)
    (fun Λ hp hl => rhs Λ _ hp hl (conservingMomenta_balanced G legs q)) hx hxUV hy hyUV

end YangMills.PerturbativeFlow
