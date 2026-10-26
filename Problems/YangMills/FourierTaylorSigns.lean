import Problems.YangMills.LocalVertexPolarization

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.LegendreInsertionBridge

/-- The exact weighted inversion count of a bijection and its inverse,
with the parity assignment transported to the same external word. -/
theorem weightedInversionCount_inverse (n : ℕ) (p : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) :
    weightedInversionCount (fun i => p (π.symm i)) π = weightedInversionCount p π.symm := by
  unfold weightedInversionCount
  simp only [π.symm_apply_apply]
  have hr : (∑ a : Fin n, ∑ b : Fin n,
      if a < b ∧ π.symm b < π.symm a ∧ p (π.symm a) = true ∧ p (π.symm b) = true then
        (1 : ℕ) else 0) =
      ∑ j : Fin n, ∑ i : Fin n,
        if π j < π i ∧ i < j ∧ p j = true ∧ p i = true then (1 : ℕ) else 0 := by
    apply Fintype.sum_equiv π.symm
    intro a
    apply Fintype.sum_equiv π.symm
    intro b
    simp only [π.apply_symm_apply]
  rw [hr, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [and_assoc, and_comm, and_left_comm]

/-- The two ACTUAL Koszul factors from the functional derivative and
balanced graded covariance cancel. -/
theorem parityExternalSign_inverse_cancel (n : ℕ) (p : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) :
    parityExternalSign (fun i => p (π.symm i)) π * parityExternalSign p π.symm = 1 := by
  simp only [parityExternalSign, weightedInversionCount_inverse, ← mul_pow]
  simp

end YangMills.IntegratedNormalization
