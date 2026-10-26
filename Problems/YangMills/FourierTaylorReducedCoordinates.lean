import Problems.YangMills.FourierTaylorCoordinates
import Problems.YangMills.ReducedMomentumDeterminacy

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Conserving extension removes the last independent momentum coordinate
at the level of the ACTUAL derivative tensor, at every base point. -/
theorem momentumJet_nonreduced_zero {legs : List (ExternalLeg G)}
    (f : (Fin legs.length → Spacetime) → ℂ) (smooth : ContDiff ℝ ∞ f)
    (extension : ∀ q, f q = f (conservingMomenta legs q)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (q : Fin legs.length → Spacetime)
    (hp : ¬ ReducedDirections legs (List.ofFn p)) :
    momentumJet (List.ofFn p) f q = 0 := by
  classical
  rw [momentumJet_ofFn]
  have heq : iteratedFDeriv ℝ k f q =
      (iteratedFDeriv ℝ k f (reducedMomentumProjection legs q)).compContinuousLinearMap
        (fun _ => reducedMomentumProjection legs) := by
    conv_lhs => rw [reduced_extension_projection extension]
    exact (reducedMomentumProjection legs).iteratedFDeriv_comp_right smooth q
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  rw [heq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hn : ∃ i, ¬ (p i).1.val + 1 < legs.length := by
    by_contra hn
    push Not at hn
    apply hp
    intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact hn i
  obtain ⟨i, hi⟩ := hn
  apply ContinuousMultilinearMap.map_coord_zero _ i
  rw [reducedMomentumProjection_basis, if_neg hi]

/-- Exact finite Taylor polarization in the source's independent momenta.
Only reduced actual jets remain, although q itself can be balanced and have
a nonzero dependent last momentum. No Taylor convergence is assumed. -/
theorem diagonalTaylor_reduced_expansion {legs : List (ExternalLeg G)}
    (f : (Fin legs.length → Spacetime) → ℂ) (smooth : ContDiff ℝ ∞ f)
    (extension : ∀ q, f q = f (conservingMomenta legs q)) (k : ℕ)
    (q : Fin legs.length → Spacetime) :
    iteratedFDeriv ℝ k f 0 (fun _ => q) =
      ∑ p : Fin k → Fin legs.length × Fin 4,
        if ReducedDirections legs (List.ofFn p) then
          (∏ i : Fin k, q (p i).1 (p i).2) • momentumJet (List.ofFn p) f 0
        else 0 := by
  classical
  rw [doublePi_multilinear_expansion]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← momentumJet_ofFn]
  split_ifs with h
  · rfl
  · rw [momentumJet_nonreduced_zero f smooth extension k p 0 h, smul_zero]

end YangMills.IntegratedNormalization
