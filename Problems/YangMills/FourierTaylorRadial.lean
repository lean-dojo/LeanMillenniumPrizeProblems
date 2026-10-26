import Problems.YangMills.LocalVertexPolarization

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow

/-- Restriction to one real momentum ray. It permits use of the actual
balanced graded law without assuming an all-q graded conserving extension. -/
def radialLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight q

@[simp] theorem radialLine_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E) (t : ℝ) : radialLine q t = t • q := rfl

theorem iteratedDeriv_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (q : E) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => f (t • q)) 0 =
      iteratedFDeriv ℝ k f 0 (fun _ => q) := by
  have hc := (radialLine q).iteratedFDeriv_comp_right hf (0 : ℝ)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  have hv := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ) ℂ =>
    T (fun _ => 1)) hc
  simpa only [iteratedDeriv_eq_iteratedFDeriv, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, radialLine_apply, zero_smul,
    one_smul] using hv

/-- Actual equality on a balanced ray determines diagonal Taylor tensors.
The source extension can remain ungraded away from balanced momenta. -/
theorem diagonalTaylor_of_radial {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E → ℂ) (h : E' → ℂ) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (q : E) (r : E') (c : ℂ) (k : ℕ)
    (hrad : ∀ t : ℝ, f (t • q) = c * h (t • r)) :
    iteratedFDeriv ℝ k f 0 (fun _ => q) = c * iteratedFDeriv ℝ k h 0 (fun _ => r) := by
  rw [← iteratedDeriv_radial f hf q k, ← iteratedDeriv_radial h hh r k]
  have he : (fun t : ℝ => f (t • q)) = fun t : ℝ => c * h (t • r) := funext hrad
  rw [he]
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have hs : ContDiff ℝ k (fun t : ℝ => h (t • r)) :=
    (hh.comp (radialLine r).contDiff).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  have hm := iteratedFDeriv_const_smul_apply' (a := c) (hs.contDiffAt (x := 0))
  change iteratedFDeriv ℝ k (fun t : ℝ => c * h (t • r)) 0 =
    c • iteratedFDeriv ℝ k (fun t : ℝ => h (t • r)) 0 at hm
  rw [hm]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]

theorem BalancedMomenta_smul {G : CompactSimpleGaugeGroup} (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (hq : BalancedMomenta legs q) (t : ℝ) :
    BalancedMomenta legs (fun i => t • q i) := by
  change (∑ i, t • q i) = 0
  rw [← Finset.smul_sum]
  change t • (∑ i, q i) = 0
  rw [hq, smul_zero]

/-- The actual balanced external-permutation law transports all diagonal
Taylor coefficients. No all-independent-momentum graded extension is used. -/
theorem balancedGraded_diagonalTaylor {G : CompactSimpleGaugeGroup} (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length))
    (q : Fin legs.length → Spacetime) (hq : BalancedMomenta legs q)
    (smooth : ContDiff ℝ ∞ (F legs))
    (smoothPerm : ContDiff ℝ ∞ (F (permutedLegs legs π)))
    (graded : ∀ p, BalancedMomenta legs p →
      F (permutedLegs legs π) (permutedMomenta legs π p) = permutationSign legs π * F legs p)
    (k : ℕ) :
    iteratedFDeriv ℝ k (F (permutedLegs legs π)) 0
        (fun _ => permutedMomenta legs π q) =
      permutationSign legs π * iteratedFDeriv ℝ k (F legs) 0 (fun _ => q) := by
  apply diagonalTaylor_of_radial _ _ smoothPerm smooth _ _ _ k
  intro t
  have ht := graded (fun i => t • q i) (BalancedMomenta_smul legs q hq t)
  exact ht

end YangMills.IntegratedNormalization
