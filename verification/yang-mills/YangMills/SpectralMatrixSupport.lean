import YangMills.QFT.Wightman
noncomputable section
namespace YangMills
open MeasureTheory
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual scalar Fourier pairing is integrable, so totalized scalar
integrals cannot make the support condition pass spuriously. -/
theorem WightmanAxioms.spectral_matrix_integrable {Q : WightmanData H}
    (h : WightmanAxioms H Q) (f : TestFunction) (u v : H) :
    Integrable (fun a : Spacetime => WightmanData.spectralKernel f a *
      inner ℂ u (Q.unitary (PoincareTransform.translate a) v)) := by
  simpa only [innerSL_apply_apply,inner_smul_right] using
    (innerSL ℂ u).integrable_comp (h.spectral_integrable f v)

/-- The fixed operator Fourier support is literally Fourier support of
EVERY scalar matrix coefficient of the SAME translation representation. -/
theorem WightmanAxioms.spectral_matrix_annihilates {Q : WightmanData H}
    (h : WightmanAxioms H Q) (f : TestFunction)
    (hf : ∀ p ∈ FutureCone, f p = 0) (u v : H) :
    (∫ a : Spacetime, WightmanData.spectralKernel f a *
      inner ℂ u (Q.unitary (PoincareTransform.translate a) v)) = 0 := by
  letI : CompleteSpace H := h.complete
  have hc := (innerSL ℂ u).integral_comp_comm (h.spectral_integrable f v)
  simpa only [innerSL_apply_apply,inner_smul_right,h.spectral_support f hf v,inner_zero_right] using hc

/-- Conversely, the all-matrix coefficient formulation determines the
operator condition itself; there is no weaker vacuum-only spectral test. -/
theorem WightmanAxioms.spectral_operator_of_matrix {Q : WightmanData H}
    (h : WightmanAxioms H Q) (f : TestFunction)
    (zero : ∀ u v : H, (∫ a : Spacetime, WightmanData.spectralKernel f a *
      inner ℂ u (Q.unitary (PoincareTransform.translate a) v)) = 0) (v : H) :
    (∫ a : Spacetime, WightmanData.spectralKernel f a •
      Q.unitary (PoincareTransform.translate a) v) = 0 := by
  letI : CompleteSpace H := h.complete
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hc := (innerSL ℂ (∫ a : Spacetime, WightmanData.spectralKernel f a •
      Q.unitary (PoincareTransform.translate a) v)).integral_comp_comm (h.spectral_integrable f v)
  simpa only [innerSL_apply_apply,inner_smul_right,zero] using hc.symm

end YangMills
