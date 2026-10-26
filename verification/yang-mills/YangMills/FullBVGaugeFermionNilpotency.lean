import YangMills.FullBVGaugeFixedAction
import YangMills.FullBVNilpotencyPromotion
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Nilpotency of the actual gauge-fermion term follows from proved basic
coordinate nilpotency and the proved full graded differential algebra.
No interacting antifield or master-equation hypothesis is needed. -/
theorem classicalLocalST_square_gaugeFermion {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (gaugeFermionDensity G)) = 0 := by
  have hb (K : BasicField G) (alpha : Multiindex) :
      localST (masterActionDensity e g)
        (localST (masterActionDensity e g) (jet ⟨.inl K,alpha⟩)) = 0 :=
    classicalLocalST_square_basic_jet e g K alpha
  unfold gaugeFermionDensity antighostJet auxiliaryJet
  simp only [classicalLocalSTDensity, localST_sum, localST_add, localST_smul,
    localST_square_mul _ (parity_masterActionDensity e g), hb, zero_mul,
    mul_zero, add_zero, smul_zero, Finset.sum_const_zero]

end YangMills.FullBV
