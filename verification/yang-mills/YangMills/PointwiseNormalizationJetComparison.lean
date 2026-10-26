import YangMills.IntegratedNormalizationProjectors
import YangMills.IntegratedTaylorJetRecovery
import YangMills.LocalVertexExternalCovariance
import YangMills.LowProjectorAdequacy

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem pointwiseNormalizationResponse_smooth
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g Λ UV : ℝ) (loop : ℕ) (labels : List (ExternalLeg G))
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hΛ : 0 < Λ) (hUV : Λ ≤ UV) :
    ContDiff ℝ ∞ (pointwiseNormalizationResponse L I D μ g loop Λ UV labels) := by
  classical
  unfold pointwiseNormalizationResponse
  apply ContDiff.sum
  intro m hm
  apply ContDiff.sum
  intro r hr
  apply contDiff_const.mul
  exact (h.smooth _ _ _ _ hΛ hUV _).of_le (by simp)

theorem pointwiseNormalizationResponse_graded
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g Λ UV : ℝ) (loop : ℕ)
    (symmetry : ∀ m r labels q (e : Equiv.Perm (Fin labels.length)),
      L μ g [⟨m, 0⟩] r Λ UV (permutedLegs labels e) (permutedMomenta labels e q) =
        permutationSign labels e * L μ g [⟨m, 0⟩] r Λ UV labels q)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime)
    (e : Equiv.Perm (Fin labels.length)) :
    pointwiseNormalizationResponse L I D μ g loop Λ UV
        (permutedLegs labels e) (permutedMomenta labels e q) =
      permutationSign labels e * pointwiseNormalizationResponse L I D μ g loop Λ UV labels q := by
  classical
  unfold pointwiseNormalizationResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [symmetry]
  ring

theorem extractCoefficient_sub_regular (m : LocalMonomial G) (F H : OrderedAmplitude G)
    (q : Fin m.legs.length → Spacetime)
    (smoothF : ContDiff ℝ ∞ (F m.legs)) (smoothH : ContDiff ℝ ∞ (H m.legs)) :
    extractCoefficient m (fun labels p => F labels p - H labels p) q =
      extractCoefficient m F q - extractCoefficient m H q := by
  change _ * momentumJet m.momentumDirections (fun p => F m.legs p - H m.legs p) q = _
  rw [momentumJet_sub_regular _ _ _ _
    ((smoothF.of_le (by exact_mod_cast (show (m.momentumDirections.length : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)
    ((smoothH.of_le (by exact_mod_cast (show (m.momentumDirections.length : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  unfold extractCoefficient momentumJet
  ring

/-- The computed finite normalization response has ALL low independent
momentum jets of the actual raw Taylor density, derived from the original
canonical projectors using actual exterior nilpotence. -/
theorem pointwiseNormalizationResponse_raw_jets
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (symmetry : ∀ m r labels q (e : Equiv.Perm (Fin labels.length)),
      L μ g [⟨m, 0⟩] r μ UV (permutedLegs labels e) (permutedMomenta labels e q) =
        permutationSign labels e * L μ g [⟨m, 0⟩] r μ UV labels q)
    (labels : List (ExternalLeg G)) (directions : List (Fin labels.length × Fin 4))
    (degree : totalDimension labels + directions.length ≤ D) :
    momentumJet directions (pointwiseNormalizationResponse L I D μ g loop μ UV labels) 0 =
      momentumJet directions (FullBV.densityAmplitude (integratedTaylorDensity D I μ g loop UV) labels) 0 := by
  let R := pointwiseNormalizationResponse L I D μ g loop μ UV
  let V := FullBV.densityAmplitude (integratedTaylorDensity D I μ g loop UV)
  have hR labels : ContDiff ℝ ∞ (R labels) :=
    pointwiseNormalizationResponse_smooth L I D μ g μ UV loop labels h h.scale_positive hUV
  have hV labels : ContDiff ℝ ∞ (V labels) := densityAmplitude_smooth _ labels
  have hzero := lowProjectorAdequacy (fun labels p => R labels p - V labels p)
    (fun labels => (hR labels).sub (hV labels)) (by
      intro legs q e
      dsimp only
      have hr := pointwiseNormalizationResponse_graded L I D μ g μ UV loop symmetry legs q e
      change R (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * R legs q at hr
      rw [hr]
      have hv := densityAmplitude_vertices_graded
        (reducedTaylorVertices D (I μ g loop μ UV)) 1 legs q e
      change V (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * V legs q at hv
      rw [hv]
      ring) D (by
      intro m hm hd
      rw [extractCoefficient_sub_regular m R V 0 (hR _) (hV _)]
      change extractCoefficient m (pointwiseNormalizationResponse L I D μ g loop μ UV) 0 -
        extractCoefficient m V 0 = 0
      rw [pointwiseNormalizationResponse_normalized L I D μ g UV loop m h hUV hm hd]
      change extractCoefficient m V 0 - extractCoefficient m V 0 = 0
      exact sub_self _) labels directions degree
  rw [momentumJet_sub_regular _ _ _ _
    ((hR labels).of_le (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((hV labels).of_le (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top))).contDiffAt] at hzero
  exact sub_eq_zero.mp hzero

end YangMills.IntegratedNormalization
