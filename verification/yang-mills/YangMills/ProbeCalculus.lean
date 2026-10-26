import YangMills.WardActionCoordinates
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open YangMills
namespace YangMills.WardAction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem iterated_two_product (L M : E →L[ℝ] ℂ) (x : E) (d : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun q => L q * M q) x d =
      L (d 0) * M (d 1) + M (d 0) * L (d 1) := by
  rw [iteratedFDeriv_two_apply]
  let D : E →L[ℝ] E →L[ℝ] ℂ := L.smulRight M + M.smulRight L
  have h : fderiv ℝ (fun q => L q * M q) = D := by
    funext y
    simpa [D, add_comm] using (L.hasFDerivAt.mul M.hasFDerivAt (x := y)).fderiv
  rw [h, D.fderiv]
  simp [D]
end YangMills.WardAction
namespace YangMills.WardAction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem iterated_two_quadratic (B : E →L[ℝ] E →L[ℝ] ℂ) (x : E) (d : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun q => B q q) x d =
      B (d 0) (d 1) + B (d 1) (d 0) := by
  rw [iteratedFDeriv_two_apply]
  have h : fderiv ℝ (fun q => B q q) = (B + B.flip : E →L[ℝ] E →L[ℝ] ℂ) := by
    funext y
    have hh := (B.hasFDerivAt.clm_apply (hasFDerivAt_id y)).fderiv
    ext v
    simpa [add_comm] using congrArg (fun (D : E →L[ℝ] ℂ) => D v) hh
  rw [h, ContinuousLinearMap.fderiv]
  simp
end YangMills.WardAction
