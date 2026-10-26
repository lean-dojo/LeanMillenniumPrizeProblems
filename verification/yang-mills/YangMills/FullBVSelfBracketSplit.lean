import YangMills.FullBVEulerParity
import YangMills.FullBVHomogeneousCommutation
noncomputable section
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- For an actual even action the two conjugate species contributions to
its self-bracket coincide. The factor two is derived, not a normalization. -/
theorem densityBracket_self_split (S : JetAlgebra G) (hS : parity S = S) :
    densityBracket S S = (2 : ℂ) • ∑ K : BasicField G,
      stCharacteristic S (.inl K) * leftEuler (.inl K) S := by
  classical
  unfold densityBracket
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro K _
  have hn (X Y : JetAlgebra G) : (-X)*Y = -(X*Y) := neg_mul X Y
  have hm (X Y : JetAlgebra G) : X*(-Y) = -(X*Y) := mul_neg X Y
  cases hK : K.fermionic
  · have basic : rightEuler (.inl K) S = leftEuler (.inl K) S := by
      simpa only [ExternalLeg.parity,hK,Bool.false_eq_true,if_false] using
        rightEuler_even_eq_leftEuler S hS (.inl K)
    have anti : rightEuler (.inr K) S = -(leftEuler (.inr K) S) := by
      simpa only [ExternalLeg.parity,hK,Bool.not_false,if_true] using
        rightEuler_even_eq_leftEuler S hS (.inr K)
    have even : parity (leftEuler (.inl K) S) = leftEuler (.inl K) S := by
      simpa only [ExternalLeg.parity,hK,Bool.false_eq_true,if_false,one_smul] using
        leftEuler_even_parity S hS (.inl K)
    have commute := evenPolynomial_commute (leftEuler (.inl K) S) (leftEuler (.inr K) S) even
    simp only [stCharacteristic, Pi.neg_apply,basic,anti,neg_neg,hn]
    rw [commute]
    simp only [two_smul]
    abel
  · have basic : rightEuler (.inl K) S = -(leftEuler (.inl K) S) := by
      simpa only [ExternalLeg.parity,hK,if_true] using
        rightEuler_even_eq_leftEuler S hS (.inl K)
    have anti : rightEuler (.inr K) S = leftEuler (.inr K) S := by
      simpa only [ExternalLeg.parity,hK,Bool.not_true,Bool.false_eq_true,if_false] using
        rightEuler_even_eq_leftEuler S hS (.inr K)
    have even : parity (leftEuler (.inr K) S) = leftEuler (.inr K) S := by
      simpa only [ExternalLeg.parity,hK,Bool.not_true,Bool.false_eq_true,if_false,one_smul] using
        leftEuler_even_parity S hS (.inr K)
    have commute := (evenPolynomial_commute (leftEuler (.inr K) S) (leftEuler (.inl K) S) even).symm
    simp only [stCharacteristic,Pi.neg_apply,basic,anti,hn]
    rw [commute]
    simp only [two_smul]
    abel

/-- The sign in varying a characteristic-linear source term cancels the
actual even-action right/left Euler sign, for either ghost parity. -/
theorem basicSourceVariation_even (S : JetAlgebra G) (hS : parity S = S) (K : BasicField G) :
    (if K.fermionic then (-1 : ℂ) else 1) •
      (stCharacteristic S (.inl K) * rightEuler (.inl K) S) =
    stCharacteristic S (.inl K) * leftEuler (.inl K) S := by
  rw [rightEuler_even_eq_leftEuler S hS]
  cases hK : K.fermionic <;>
    simp only [ExternalLeg.parity,hK,Bool.false_eq_true,if_false,if_true,
      one_smul,complex_neg_one_smul]
  have hm (X Y : JetAlgebra G) : X*(-Y) = -(X*Y) := mul_neg X Y
  rw [hm,neg_neg]

end YangMills.FullBV
