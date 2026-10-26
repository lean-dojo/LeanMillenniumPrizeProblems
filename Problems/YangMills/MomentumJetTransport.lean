import Problems.YangMills.MomentumJetSymmetry

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual directional-word chain rule under a continuous linear
change of all independent momentum coordinates. -/
theorem directionalWord_comp_linearEquiv (e : E ≃L[ℝ] F) (directions : List E)
    {f : F → ℂ} (smooth : ContDiff ℝ ∞ f) (x : E) :
    directionalWord directions (f ∘ e) x =
      directionalWord (directions.map e) f (e x) := by
  induction directions generalizing x with
  | nil => rfl
  | cons v rest ih =>
    simp only [directionalWord,List.map_cons]
    have equal : directionalWord rest (f ∘ e) =
        (directionalWord (rest.map e) f) ∘ e := funext ih
    rw [equal]
    have differentiable := (directionalWord_smooth (rest.map e) smooth).differentiable (by simp)
    have derivative := ((differentiable (e x)).hasFDerivAt.comp x e.hasFDerivAt)
    rw [derivative.fderiv]
    rfl

end YangMills.PerturbativeFlow
