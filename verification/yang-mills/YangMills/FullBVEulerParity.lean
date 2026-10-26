import YangMills.FullBVClassicalSTParity
noncomputable section
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem rightEuler_eq_parity_leftEuler (field : ExternalLeg G) (P : JetAlgebra G) :
    rightEuler field P = if field.parity then parity (leftEuler field P) else leftEuler field P := by
  cases h : field.parity
  · simp only [h, Bool.false_eq_true, if_false]
    unfold rightEuler leftEuler
    apply finsum_congr
    intro alpha
    simp only [rightPartialJet, h, Bool.false_eq_true, if_false]
  · simp only [h, if_true]
    have hm := parity.toAddMonoidHom.map_finsum (leftEulerSummands_finite field P)
    unfold rightEuler
    trans ∑ᶠ alpha : Multiindex, parity (((-1 : ℂ) ^ derivativeOrder alpha) •
      totalDerivatives alpha (leftPartialJet ⟨field,alpha⟩ P))
    · apply finsum_congr
      intro alpha
      simp only [rightPartialJet, h, if_true, LinearMap.comp_apply, map_smul,
        ← totalDerivatives_parity]
    · exact hm.symm

/-- Right and left variational derivatives of an actual even action
have the prescribed species sign, including every antifield. -/
theorem rightEuler_even_eq_leftEuler (S : JetAlgebra G) (hS : parity S = S) (field : ExternalLeg G) :
    rightEuler field S = if field.parity then -(leftEuler field S) else leftEuler field S := by
  cases hf : field.parity
  · simpa only [hf, Bool.false_eq_true, if_false] using rightEuler_eq_parity_leftEuler field S
  · simp only [hf, if_true]
    have hright : rightEuler field S = parity (leftEuler field S) := by
      simpa only [hf, if_true] using rightEuler_eq_parity_leftEuler field S
    have hleft : leftEuler field S = -(rightEuler field S) := by
      calc
        _ = parity (rightEuler field S) := by rw [hright,parity_parity]
        _ = _ := by simpa only [hf,if_true,complex_neg_one_smul] using rightEuler_even_parity S hS field
    calc
      _ = -(-(rightEuler field S)) := (neg_neg _).symm
      _ = _ := congrArg Neg.neg hleft.symm

theorem leftEuler_even_parity (S : JetAlgebra G) (hS : parity S = S) (field : ExternalLeg G) :
    parity (leftEuler field S) =
      (if field.parity then (-1 : ℂ) else 1) • leftEuler field S := by
  have hright := rightEuler_even_parity S hS field
  rw [rightEuler_even_eq_leftEuler S hS field] at hright
  cases hf : field.parity <;>
    simp only [hf,Bool.false_eq_true,if_false,if_true,one_smul,complex_neg_one_smul,map_neg] at hright ⊢
  · exact hright
  · exact neg_injective hright

end YangMills.FullBV
