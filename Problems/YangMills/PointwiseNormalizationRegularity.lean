import Problems.YangMills.PointwiseNormalizationJetComparison

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem momentumJet_sum_regular {J : Type*} (S : Finset J)
    {legs : List (ExternalLeg G)} (d : List (Fin legs.length × Fin 4))
    (F : J → (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime)
    (smooth : ∀ j ∈ S, ContDiff ℝ d.length (F j)) :
    momentumJet d (fun p => ∑ j ∈ S, F j p) q = ∑ j ∈ S, momentumJet d (F j) q := by
  unfold momentumJet
  rw [congrFun (iteratedFDeriv_sum smooth) q]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]

theorem momentumJet_const_mul_regular {legs : List (ExternalLeg G)}
    (d : List (Fin legs.length × Fin 4)) (c : ℂ)
    (F : (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime)
    (smooth : ContDiff ℝ d.length F) :
    momentumJet d (fun p => c * F p) q = c * momentumJet d F q := by
  unfold momentumJet
  have hs := iteratedFDeriv_const_smul_apply' (a := c) (smooth.contDiffAt (x := q))
  change iteratedFDeriv ℝ d.length (fun p => c * F p) q =
    c • iteratedFDeriv ℝ d.length F q at hs
  rw [hs]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]

theorem pointwiseNormalizationResponse_jet_formula
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g Λ UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hΛ : 0 < Λ) (hUV : Λ ≤ UV)
    (labels : List (ExternalLeg G)) (d : List (Fin labels.length × Fin 4))
    (q : Fin labels.length → Spacetime) :
    momentumJet d (pointwiseNormalizationResponse L I D μ g loop Λ UV labels) q =
      ∑ m ∈ monomialsBelow G (D+1), ∑ r ∈ Finset.range (loop+1),
        normalizationCoefficient (L μ g) I D μ g UV r m *
          momentumJet d (L μ g [⟨m, 0⟩] (loop-r) Λ UV labels) q := by
  classical
  have hs m r : ContDiff ℝ d.length (L μ g [⟨m, 0⟩] (loop-r) Λ UV labels) :=
    (h.smooth _ _ _ _ hΛ hUV _).of_le
      (by exact_mod_cast (show (d.length : ℕ∞) ≤ ⊤ from le_top))
  unfold pointwiseNormalizationResponse
  rw [momentumJet_sum_regular]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [momentumJet_sum_regular]
    · apply Finset.sum_congr rfl
      intro r hr
      exact momentumJet_const_mul_regular d _ _ q (hs m r)
    · intro r hr
      exact contDiff_const.mul (hs m r)
  · intro m hm
    exact ContDiff.sum (fun r hr => contDiff_const.mul (hs m r))

/-- Actual positive-scale jet continuity of the computed finite Cauchy
response. Its normalization coefficients are fixed in the running cutoff. -/
theorem pointwiseNormalizationResponse_jet_continuous
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ)
    (labels : List (ExternalLeg G)) (d : List (Fin labels.length × Fin 4))
    (q : Fin labels.length → Spacetime) :
    ContinuousOn (fun Λ => momentumJet d
      (pointwiseNormalizationResponse L I D μ g loop Λ UV labels) q) (Set.Ioc 0 UV) := by
  classical
  have hc : ContinuousOn (fun Λ =>
      ∑ m ∈ monomialsBelow G (D+1), ∑ r ∈ Finset.range (loop+1),
        normalizationCoefficient (L μ g) I D μ g UV r m *
          momentumJet d (L μ g [⟨m, 0⟩] (loop-r) Λ UV labels) q) (Set.Ioc 0 UV) := by
    apply continuousOn_finsetSum _
    intro m hm
    apply continuousOn_finsetSum _
    intro r hr
    exact continuousOn_const.mul (h.scale_jet_continuous _ _ _ _ d q)
  apply hc.congr
  intro Λ hΛ
  exact pointwiseNormalizationResponse_jet_formula L I D μ g Λ UV loop h hΛ.1 hΛ.2 labels d q

end YangMills.IntegratedNormalization
