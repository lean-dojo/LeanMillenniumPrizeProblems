import YangMills.CanonicalProjectorDirections
import YangMills.MomentumCoordinateRelabel

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma directionalWord_const_mul (directions : List E) (c : ℂ)
    {f : E → ℂ} (smooth : ContDiff ℝ ∞ f) (x : E) :
    directionalWord directions (fun y => c*f y) x = c * directionalWord directions f x := by
  induction directions generalizing x with
  | nil => rfl
  | cons v rest ih =>
    simp only [directionalWord]
    have equal : directionalWord rest (fun y => c*f y) =
        fun y => c * directionalWord rest f y := funext ih
    rw [equal]
    have differentiable := (directionalWord_smooth rest smooth).differentiable (by simp)
    have derivative := (differentiable x).hasFDerivAt.const_smul c
    change (fderiv ℝ (c • directionalWord rest f) x) v = _
    rw [derivative.fderiv]
    rfl

variable {G : CompactSimpleGaugeGroup}

/-- Exact canonicalization of an actual jet under the same component's
slot covariance. The supplied equality is the ordinary graded component
transport relation, not an assumption about derivatives or projectors. -/
theorem canonicalProjector_momentumJet (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) (c : ℂ)
    {f : (Fin legs.length → Spacetime) → ℂ}
    {canonical : (Fin (directionMonomial legs directions).legs.length → Spacetime) → ℂ}
    (smooth : ContDiff ℝ ∞ f) (canonical_smooth : ContDiff ℝ ∞ canonical)
    (transport : canonical ∘ momentumCoordinateRelabel (canonicalProjectorSlotEquiv legs directions) =
      fun q => c*f q) (q : Fin legs.length → Spacetime) :
    momentumJet (directionMonomial legs directions).momentumDirections canonical
      (momentumCoordinateRelabel (canonicalProjectorSlotEquiv legs directions) q) =
      c * momentumJet directions f q := by
  let e := canonicalProjectorSlotEquiv legs directions
  rw [momentumJet_perm _ (canonicalProjectorDirections_perm legs directions) canonical_smooth]
  rw [momentumJet_eq_directionalWord _ _ canonical_smooth]
  simp only [List.map_map,Function.comp_def]
  rw [← directionalCoordinates_relabel e directions canonical_smooth,transport,
    directionalWord_const_mul _ c smooth]
  rw [momentumJet_eq_directionalWord legs directions smooth]

end YangMills.PerturbativeFlow
