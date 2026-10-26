import Problems.YangMills.IntegratedPointwiseNormalization

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem extractCoefficient_const_mul_regular (m : LocalMonomial G)
    (c : ℂ) (F : OrderedAmplitude G) (q : Fin m.legs.length → Spacetime)
    (hF : ContDiff ℝ m.momentumDirections.length (F m.legs)) :
    extractCoefficient m (fun legs p => c * F legs p) q = c * extractCoefficient m F q := by
  unfold extractCoefficient
  have hi := iteratedFDeriv_const_smul_apply' (a := c) (hF.contDiffAt (x := q))
  change iteratedFDeriv ℝ m.momentumDirections.length (fun p => c * F m.legs p) q =
    c • iteratedFDeriv ℝ m.momentumDirections.length (F m.legs) q at hi
  rw [hi]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem extractCoefficient_sum_regular {J : Type*} (S : Finset J)
    (m : LocalMonomial G) (F : J → OrderedAmplitude G)
    (q : Fin m.legs.length → Spacetime)
    (hF : ∀ j ∈ S, ContDiff ℝ m.momentumDirections.length (F j m.legs)) :
    extractCoefficient m (fun legs p => ∑ j ∈ S, F j legs p) q =
      ∑ j ∈ S, extractCoefficient m (F j) q := by
  unfold extractCoefficient
  have hi := congrFun (iteratedFDeriv_sum hF) q
  rw [hi]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]

/-- Projecting the constructed finite amplitude gives the SAME computed
scalar jet matrix. Smoothness comes from the actual insertion family. -/
theorem pointwiseNormalizationResponse_projector
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (output : LocalMonomial G)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV) :
    extractCoefficient output (pointwiseNormalizationResponse L I D μ g loop μ UV) 0 =
      normalizationMatrixValue (L μ g) I D μ g UV loop output := by
  classical
  let k := output.momentumDirections.length
  have hs (input : LocalMonomial G) (r : ℕ) :
      ContDiff ℝ k (L μ g [⟨input, 0⟩] (loop-r) μ UV output.legs) :=
    (h.smooth _ _ _ _ h.scale_positive hUV _).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  unfold pointwiseNormalizationResponse normalizationMatrixValue
  rw [extractCoefficient_sum_regular]
  · apply Finset.sum_congr rfl
    intro input hinput
    rw [extractCoefficient_sum_regular]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [extractCoefficient_const_mul_regular _ _ _ _ (hs input r)]
      rfl
    · intro r hr
      exact contDiff_const.mul (hs input r)
  · intro input hinput
    exact ContDiff.sum (fun r hr => contDiff_const.mul (hs input r))

/-- All subtraction-scale projectors through D match the actual finite
Taylor target. No finite normalization matrix is chosen by a witness. -/
theorem pointwiseNormalizationResponse_normalized
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (output : LocalMonomial G)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (ho : output.Admissible) (hd : output.dimension ≤ D) :
    extractCoefficient output (pointwiseNormalizationResponse L I D μ g loop μ UV) 0 =
      integratedTaylorJet D I μ g UV loop output := by
  rw [pointwiseNormalizationResponse_projector L I D μ g UV loop output h hUV]
  exact normalizationMatrixValue_eq (L μ g) I D μ g UV loop output h hUV ho hd

end YangMills.IntegratedNormalization
