import Problems.YangMills.IntegratedMarginalFlow
import Problems.YangMills.ReducedLinearInsertionUniqueness

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow Filter
open scoped ContDiff Topology
variable {G : CompactSimpleGaugeGroup}

def IntegratedMarginalConditions.reducedRegularity
    {A F : ScaleCouplingFamily G} {terms : ℝ → List (LocalVertex G)}
    (hF : IntegratedMarginalConditions A F terms) (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV) :
    ReducedLinearInsertionRegularity (A μ g) (F μ g) UV := {
  smooth := fun loop Λ legs hp hle => hF.momentum_smooth μ g loop Λ UV legs hμ hUV hp hle
  continuous := fun loop legs d q => hF.positive_scale_jet_continuity μ g loop UV legs d q hμ hUV
  extension := fun loop Λ legs q => hF.reduced_extension μ g loop Λ UV legs q
  vacuum := fun loop Λ q => hF.vacuum_subtraction μ g loop Λ UV q
  flow := fun loop Λ legs q hp hlt hn hb => hF.flow μ g loop Λ UV legs q hμ hUV hp hlt hn hb
}

/-- The source's mixed integrated boundary problem determines every
cutoff-constant difference without converting it to pointwise normalization. -/
theorem integratedMarginalDifference_zero_of_constant
    {A F H : ScaleCouplingFamily G} {terms : ℝ → List (LocalVertex G)}
    (hF : IntegratedMarginalConditions A F terms) (hH : IntegratedMarginalConditions A H terms)
    (μ g UV : ℝ) (loop : ℕ) (legs : List (ExternalLeg G))
    (hμ : 0 < μ) (hUV : μ ≤ UV)
    (constant : ∀ Λ, 0 < Λ → Λ ≤ UV →
      (fun q => F μ g loop UV UV legs q - H μ g loop UV UV legs q) =
        (fun q => F μ g loop Λ UV legs q - H μ g loop Λ UV legs q)) :
    (fun q => F μ g loop UV UV legs q - H μ g loop UV UV legs q) = 0 := by
  have uvpos : 0 < UV := hμ.trans_le hUV
  have smoothA := hF.momentum_smooth μ g loop UV UV legs hμ hUV uvpos le_rfl
  have smoothC := hH.momentum_smooth μ g loop UV UV legs hμ hUV uvpos le_rfl
  let f := fun q => F μ g loop UV UV legs q - H μ g loop UV UV legs q
  have hf : ContDiff ℝ ∞ f := smoothA.sub smoothC
  have extension : ∀ q, f q = f (conservingMomenta legs q) := by
    intro q
    exact congrArg₂ (· - ·) (hF.reduced_extension μ g loop UV UV legs q)
      (hH.reduced_extension μ g loop UV UV legs q)
  have jet_at (d : List (Fin legs.length × Fin 4)) (q : Fin legs.length → Spacetime)
      (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV) :
      momentumJet d f q = momentumJet d (F μ g loop Λ UV legs) q -
        momentumJet d (H μ g loop Λ UV legs) q := by
    change momentumJet d (fun q => F μ g loop UV UV legs q - H μ g loop UV UV legs q) q = _
    rw [constant Λ hp hle]
    exact momentumJet_difference_smooth d
      (hF.momentum_smooth μ g loop Λ UV legs hμ hUV hp hle)
      (hH.momentum_smooth μ g loop Λ UV legs hμ hUV hp hle) q
  have irrelevant (d : List (Fin legs.length × Fin 4)) (hd : ReducedDirections legs d)
      (hdeg : 4 < totalDimension legs + d.length) (q : Fin legs.length → Spacetime) :
      momentumJet d f q = 0 := by
    rw [jet_at d q UV uvpos le_rfl, hF.irrelevant_uv μ g loop UV legs d q hμ hUV hd hdeg,
      hH.irrelevant_uv μ g loop UV legs d q hμ hUV hd hdeg, sub_self]
  have normalized (d : List (Fin legs.length × Fin 4)) (hd : ReducedDirections legs d)
      (hdeg : totalDimension legs + d.length ≤ 4) : momentumJet d f 0 = 0 := by
    rcases lt_or_eq_of_le hdeg with ht | he
    · have hlim := (hF.relevant_ir_limit μ g loop UV legs d hμ hUV hd ht).sub
        (hH.relevant_ir_limit μ g loop UV legs d hμ hUV hd ht)
      simp only [sub_self] at hlim
      have ev : ∀ᶠ Λ in nhdsWithin 0 (Set.Ioi 0),
          momentumJet d (F μ g loop Λ UV legs) 0 -
            momentumJet d (H μ g loop Λ UV legs) 0 = momentumJet d f 0 := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds uvpos).filter_mono nhdsWithin_le_nhds] with Λ hp hlt
        exact (jet_at d 0 Λ hp hlt.le).symm
      have hlim' : Tendsto (fun _ : ℝ => momentumJet d f 0)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hlim.congr' ev
      exact tendsto_nhds_unique tendsto_const_nhds hlim'
    · rw [jet_at d 0 μ hμ hUV]
      have ha := hF.marginal μ g loop UV legs d hμ hUV hd he
      have hc := hH.marginal μ g loop UV legs d hμ hUV hd he
      exact sub_eq_zero.mpr (ha.trans hc.symm)
  by_cases high : 4 < totalDimension legs
  · funext q
    simpa only [momentumJet, List.length_nil, iteratedFDeriv_zero_apply, Pi.zero_apply]
      using irrelevant [] (by intro d hd; simp at hd) (by simpa using high) q
  · apply reducedJet_determinacy hf extension (4 - totalDimension legs)
    · intro d hd hlen q
      exact irrelevant d hd (by omega) q
    · intro d hd hlen
      exact normalized d hd (by omega)

/-- The SAME massless integrated dimension-four response is unique for
its actual Table-II seed and background. No pointwise/integrated equality or
response existence is assumed by this supporting theorem. -/
theorem IntegratedMarginalConditions.unique {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A F H : ScaleCouplingFamily G}
    {terms : ℝ → List (LocalVertex G)} (hA : CoefficientFlowConditions e scheme A)
    (hF : IntegratedMarginalConditions A F terms) (hH : IntegratedMarginalConditions A H terms)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (hΛUV : Λ ≤ UV)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    F μ g loop Λ UV legs q = H μ g loop Λ UV legs q := by
  have uvpos : 0 < UV := hμ.trans_le hUV
  have regF := hF.reducedRegularity μ g UV hμ hUV
  have regH := hH.reducedRegularity μ g UV hμ hUV
  have main : ∀ loop n, ∀ legs : List (ExternalLeg G), legs.length = n →
      ∀ Λ, 0 < Λ → Λ ≤ UV → ∀ q,
      F μ g loop Λ UV legs q = H μ g loop Λ UV legs q := by
    intro loop
    induction loop using Nat.strong_induction_on with
    | h loop ihloop =>
      intro n
      induction n using Nat.strong_induction_on with
      | h n iharity =>
        intro legs hlen Λ hp hle q
        by_cases empty : legs = []
        · subst legs
          rw [hF.vacuum_subtraction, hH.vacuum_subtraction]
        · have rhs : ∀ t p, 0 < t → t < UV → BalancedMomenta legs p →
              insertionHomogeneousRHS (A μ g) (F μ g) loop t UV legs p =
                insertionHomogeneousRHS (A μ g) (H μ g) loop t UV legs p := by
            intro t p ht htUV _
            apply insertionHomogeneousRHS_congr_lower
            · intro l ls p' hl
              rcases hl with hl | ⟨hl, hls⟩
              · exact ihloop l hl ls.length ls rfl t ht htUV.le p'
              · subst l
                exact iharity ls.length (by omega) ls rfl t ht htUV.le p'
            · intro ls p' hls
              exact hA.no_free_interaction μ g t UV ls p' hls
          have constant : ∀ t, 0 < t → t ≤ UV →
              (fun p => F μ g loop UV UV legs p - H μ g loop UV UV legs p) =
                (fun p => F μ g loop t UV legs p - H μ g loop t UV legs p) := by
            intro t ht htUV
            exact regF.scaleConstant_all regH loop legs empty rhs uvpos le_rfl ht htUV
          have hz := integratedMarginalDifference_zero_of_constant hF hH μ g UV loop legs hμ hUV constant
          have hvalue := congrFun ((constant Λ hp hle).symm.trans hz) q
          exact sub_eq_zero.mp hvalue
  exact main loop legs.length legs rfl Λ hΛ hΛUV q

end YangMills.IntegratedNormalization
