import Problems.YangMills.FourierTaylorCoordinates
import Problems.YangMills.ReducedMomentumDeterminacy

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

def conservingMomentumMap (legs : List (ExternalLeg G)) :
    (Fin legs.length → Spacetime) →L[ℝ] (Fin legs.length → Spacetime) :=
  ContinuousLinearMap.pi fun i =>
    if i.val + 1 = legs.length then
      -(∑ j ∈ (Finset.univ : Finset (Fin legs.length)).filter
        (fun j => j.val + 1 < legs.length), ContinuousLinearMap.proj j)
    else ContinuousLinearMap.proj i

@[simp] theorem conservingMomentumMap_apply (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    conservingMomentumMap legs q = conservingMomenta legs q := by
  ext i μ
  simp only [conservingMomentumMap, conservingMomenta, ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

/-- Equality of the actual independent coordinate jets determines the whole
derivative tensor, hence its pullback by ANY fixed continuous linear map. -/
theorem momentumJet_compCLM_of_equal_jets (legs : List (ExternalLeg G))
    (f h : (Fin legs.length → Spacetime) → ℂ)
    (smoothF : ContDiff ℝ ∞ f) (smoothH : ContDiff ℝ ∞ h)
    (C : (Fin legs.length → Spacetime) →L[ℝ] (Fin legs.length → Spacetime))
    (directions : List (Fin legs.length × Fin 4))
    (jets : ∀ p : Fin directions.length → Fin legs.length × Fin 4,
      momentumJet (List.ofFn p) f 0 = momentumJet (List.ofFn p) h 0) :
    momentumJet directions (f ∘ C) 0 = momentumJet directions (h ∘ C) 0 := by
  have hd : iteratedFDeriv ℝ directions.length f 0 =
      iteratedFDeriv ℝ directions.length h 0 := by
    apply sub_eq_zero.mp
    apply doublePi_multilinear_zero
    intro p
    simp only [ContinuousMultilinearMap.sub_apply]
    rw [← momentumJet_ofFn, ← momentumJet_ofFn, jets p, sub_self]
  unfold momentumJet
  rw [C.iteratedFDeriv_comp_right smoothF 0
    (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top)),
    C.iteratedFDeriv_comp_right smoothH 0
    (by exact_mod_cast (show (directions.length : ℕ∞) ≤ ⊤ from le_top))]
  simp only [map_zero]
  rw [hd]

end YangMills.IntegratedNormalization
