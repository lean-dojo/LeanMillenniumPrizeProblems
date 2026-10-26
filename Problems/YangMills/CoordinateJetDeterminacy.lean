import Problems.YangMills.ReducedMomentumDeterminacy

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
open scoped ContDiff
variable {G : CompactSimpleGaugeGroup}

/-- Independent momentum coordinates of pointwise insertions. This is the
actual `momentumJet`, with no supermonomial-projector completeness assumed. -/
theorem coordinateJet_determinacy {legs : List (ExternalLeg G)}
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f) (degree : ℕ)
    (highest : ∀ directions : List (Fin legs.length × Fin 4),
      directions.length = degree+1 → ∀ q, momentumJet directions f q = 0)
    (lower : ∀ directions : List (Fin legs.length × Fin 4),
      directions.length ≤ degree → momentumJet directions f 0 = 0) : f = 0 := by
  apply finiteJet_determinacy smooth degree
  · intro q
    apply doublePi_multilinear_zero
    intro p
    have h := highest (List.ofFn p) List.length_ofFn q
    rwa [momentumJet_ofFn] at h
  · intro k hk
    apply doublePi_multilinear_zero
    intro p
    have h := lower (List.ofFn p) (by simpa only [List.length_ofFn] using hk)
    rwa [momentumJet_ofFn] at h

end YangMills.PerturbativeFlow
