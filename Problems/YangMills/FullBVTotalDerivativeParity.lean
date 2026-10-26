import Problems.YangMills.FullBVTotalDerivativeAlgebra

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

theorem totalDerivative_neg (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivative mu (-P) = -totalDerivative mu P := by
  simpa only [complex_neg_one_smul] using totalDerivative_smul mu (-1 : ℂ) P

/-- Parity is preserved by ordinary derivatives of full local insertions. -/
theorem totalDerivative_parity (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivative mu (parity P) = parity (totalDerivative mu P) := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one =>
      have hp : parity (1 : JetAlgebra G) = 1 := by
        simp [parity, Algebra.TensorProduct.one_def]
      rw [hp, totalDerivative_one, map_zero]
  | add P Q hP hQ => simp only [map_add, totalDerivative_add, hP, hQ]
  | smul c P hP => simp only [map_smul, totalDerivative_smul, hP]
  | mul P j hP =>
      cases hj : j.field.parity <;>
        simp [parity_mul, parity_jet, totalDerivative_mul, totalDerivative_jet,
          map_add, hP, Jet.shift, hj, if_true, if_false, totalDerivative_neg]

theorem totalDerivatives_parity (alpha : Multiindex)
    (P : JetAlgebra G) : totalDerivatives alpha (parity P) = parity (totalDerivatives alpha P) := by
  unfold totalDerivatives
  generalize derivativeList alpha = l
  induction l with
  | nil => rfl
  | cons mu l ih =>
      simpa only [List.foldr_cons, ih] using totalDerivative_parity mu (l.foldr totalDerivative P)

end YangMills.FullBV
