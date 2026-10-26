import Problems.YangMills.FlowTriangularity

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative Filter
open scoped Topology ContDiff
variable {G : CompactSimpleGaugeGroup}

lemma momentumJet_difference_smooth {legs : List (ExternalLeg G)}
    (directions : List (Fin legs.length × Fin 4))
    {f h : (Fin legs.length → Spacetime) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (q : Fin legs.length → Spacetime) :
    momentumJet directions (fun p => f p - h p) q =
      momentumJet directions f q - momentumJet directions h q := by
  unfold momentumJet
  have hfa : ContDiffAt ℝ directions.length f q :=
    (hf.of_le (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
  have hha : ContDiffAt ℝ directions.length h q :=
    (hh.of_le (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
  simp only [sub_eq_add_neg]
  rw [fun_iteratedFDeriv_add_apply hfa hha.neg]
  rw [show (fun p => -h p) = -h from rfl, iteratedFDeriv_neg_apply]
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.neg_apply]

/-- The mixed IR/marginal/UV normalization determines a cutoff-constant
flow difference. All derivatives are actual reduced momentum derivatives. -/
theorem flowDifference_eq_zero_of_constant {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {A C : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A) (hC : CoefficientFlowConditions e scheme C)
    (μ g UV : ℝ) (loop : ℕ) (legs : List (ExternalLeg G))
    (hμ : 0 < μ) (hUV : μ ≤ UV)
    (constant : ∀ Λ, 0 < Λ → Λ ≤ UV →
      (fun q => A μ g loop UV UV legs q - C μ g loop UV UV legs q) =
        (fun q => A μ g loop Λ UV legs q - C μ g loop Λ UV legs q)) :
    (fun q => A μ g loop UV UV legs q - C μ g loop UV UV legs q) = 0 := by
  have uvpos : 0 < UV := hμ.trans_le hUV
  have smoothA := hA.momentum_smooth μ g loop UV UV legs hμ hUV uvpos le_rfl
  have smoothC := hC.momentum_smooth μ g loop UV UV legs hμ hUV uvpos le_rfl
  let f := fun q => A μ g loop UV UV legs q - C μ g loop UV UV legs q
  have hf : ContDiff ℝ ∞ f := smoothA.sub smoothC
  have extension : ∀ q, f q = f (conservingMomenta legs q) := by
    intro q
    exact congrArg₂ (· - ·) (hA.reduced_extension μ g loop UV UV legs q)
      (hC.reduced_extension μ g loop UV UV legs q)
  have jet_at (d : List (Fin legs.length × Fin 4)) (q : Fin legs.length → Spacetime)
      (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV) :
      momentumJet d f q = momentumJet d (A μ g loop Λ UV legs) q -
        momentumJet d (C μ g loop Λ UV legs) q := by
    change momentumJet d (fun q => A μ g loop UV UV legs q - C μ g loop UV UV legs q) q = _
    rw [constant Λ hp hle]
    exact momentumJet_difference_smooth d
      (hA.momentum_smooth μ g loop Λ UV legs hμ hUV hp hle)
      (hC.momentum_smooth μ g loop Λ UV legs hμ hUV hp hle) q
  have irrelevant (d : List (Fin legs.length × Fin 4)) (hd : ReducedDirections legs d)
      (hdeg : 4 < totalDimension legs + d.length) (q : Fin legs.length → Spacetime) :
      momentumJet d f q = 0 := by
    rw [jet_at d q UV uvpos le_rfl, hA.irrelevant_uv μ g loop UV legs d q hμ hUV hd hdeg,
      hC.irrelevant_uv μ g loop UV legs d q hμ hUV hd hdeg, sub_self]
  have normalized (d : List (Fin legs.length × Fin 4)) (hd : ReducedDirections legs d)
      (hdeg : totalDimension legs + d.length ≤ 4) : momentumJet d f 0 = 0 := by
    rcases lt_or_eq_of_le hdeg with ht | he
    · have hlim := (hA.relevant_ir_limit μ g loop UV legs d hμ hUV hd ht).sub
        (hC.relevant_ir_limit μ g loop UV legs d hμ hUV hd ht)
      simp only [sub_self] at hlim
      have ev : ∀ᶠ Λ in nhdsWithin 0 (Set.Ioi 0),
          momentumJet d (A μ g loop Λ UV legs) 0 -
            momentumJet d (C μ g loop Λ UV legs) 0 = momentumJet d f 0 := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds uvpos).filter_mono nhdsWithin_le_nhds] with Λ hp hlt
        exact (jet_at d 0 Λ hp hlt.le).symm
      have hlim' : Tendsto (fun _ : ℝ => momentumJet d f 0)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hlim.congr' ev
      exact tendsto_nhds_unique tendsto_const_nhds hlim'
    · rw [jet_at d 0 μ hμ hUV]
      have ha := hA.marginal μ g loop UV legs d hμ hUV hd he
      have hc := hC.marginal μ g loop UV legs d hμ hUV hd he
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

end YangMills.PerturbativeFlow
