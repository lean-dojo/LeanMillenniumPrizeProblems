import Problems.YangMills.QFT.Wightman
import Mathlib.Logic.Small.Basic
import Mathlib.Algebra.Module.Shrink

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills
universe u

/-- Separability makes the physical carrier small, without choosing a basis
or imposing an infinite-dimensional Hilbert-space model. -/
theorem separableMetric_small (H : Type u) [MetricSpace H]
    [TopologicalSpace.SeparableSpace H] : Small.{0} H :=
by
  classical
  by_cases h : Nonempty H
  · letI := h
    obtain ⟨p,hp⟩ := TopologicalSpace.exists_dense_seq H
    apply small_of_injective (f := fun x : H => fun n : ℕ => dist x (p n))
    intro x y hxy
    have heq : (fun z : H => dist x z) = (fun z : H => dist y z) :=
      (continuous_const.dist continuous_id).ext_on hp
        (continuous_const.dist continuous_id) (by
          rintro z ⟨n,rfl⟩
          exact congrFun hxy n)
    have hz := congrFun heq x
    simpa only [dist_self,eq_comm,dist_eq_zero] using hz
  · letI : IsEmpty H := not_nonempty_iff.mp h
    exact small_of_injective (f := (fun x : H => isEmptyElim x : H → Empty)) (by
      intro x; exact isEmptyElim x)

namespace SmallHilbert
variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Small.{0} H]

instance normed : NormedAddCommGroup (Shrink.{0} H) :=
  NormedAddCommGroup.induced _ H (Shrink.linearEquiv ℂ H).toAddEquiv.toAddMonoidHom
    (Shrink.linearEquiv ℂ H).injective

instance innerProduct : InnerProductSpace ℂ (Shrink.{0} H) where
  inner x y := inner ℂ (Shrink.linearEquiv ℂ H x) (Shrink.linearEquiv ℂ H y)
  norm_smul_le r x := by
    change ‖Shrink.linearEquiv ℂ H (r • x)‖ ≤ ‖r‖ * ‖Shrink.linearEquiv ℂ H x‖
    rw [map_smul]
    exact norm_smul_le r _
  norm_sq_eq_re_inner x := by
    change ‖Shrink.linearEquiv ℂ H x‖ ^ 2 = _
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  conj_inner_symm x y := inner_conj_symm _ _
  add_left x y z := by simp only [map_add,inner_add_left]
  smul_left x y r := by simp only [map_smul,inner_smul_left]

/-- Literal carrier transport, preserving the actual norm and scalar product. -/
def carrier : Shrink.{0} H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := Shrink.linearEquiv ℂ H
  norm_map' _ := rfl

end SmallHilbert
end YangMills
