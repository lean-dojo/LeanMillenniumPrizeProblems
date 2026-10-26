import Problems.YangMills.MomentumJetTransport

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow

/-- Relabel every actual independent external momentum slot. -/
def momentumCoordinateRelabel {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    (ι → Spacetime) ≃L[ℝ] (κ → Spacetime) where
  toFun q := fun i => q (e i)
  invFun q := fun i => q (e.symm i)
  left_inv := by intro q; funext i; simp
  right_inv := by intro q; funext i; simp
  map_add' := by intro q p; rfl
  map_smul' := by intro c q; rfl
  continuous_toFun := continuous_pi (fun i => continuous_apply (e i))
  continuous_invFun := continuous_pi (fun i => continuous_apply (e.symm i))

lemma momentumCoordinateRelabel_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (i : ι) (mu : Fin 4) :
    momentumCoordinateRelabel e (Pi.single i (Pi.single mu 1)) =
      Pi.single (e.symm i) (Pi.single mu 1) := by
  ext j nu
  change (Pi.single i (Pi.single mu (1 : ℝ)) : ι → Spacetime) (e j) nu = _
  have equal : e j = i ↔ j = e.symm i := e.apply_eq_iff_eq_symm_apply
  simp only [Pi.single_apply,ite_apply,Pi.zero_apply]
  simp only [equal]

/-- Coordinate derivatives transform by the inverse slot relabeling; all
independent momenta, rather than a conserving subset, participate. -/
theorem directionalCoordinates_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (directions : List (ι × Fin 4))
    {f : (κ → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f) (q : ι → Spacetime) :
    directionalWord (directions.map (fun d => (Pi.single d.1 (Pi.single d.2 1) : ι → Spacetime)))
      (f ∘ momentumCoordinateRelabel e) q =
      directionalWord (directions.map (fun d =>
        (Pi.single (e.symm d.1) (Pi.single d.2 1) : κ → Spacetime))) f (momentumCoordinateRelabel e q) := by
  rw [directionalWord_comp_linearEquiv _ _ smooth]
  simp only [List.map_map,Function.comp_def,momentumCoordinateRelabel_single]

end YangMills.PerturbativeFlow
