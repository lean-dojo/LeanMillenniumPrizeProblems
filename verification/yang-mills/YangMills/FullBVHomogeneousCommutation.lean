import YangMills.FullBVTotalDerivativeAlgebra
import YangMills.FullBVActionParity
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

/-- An actually even local superpolynomial commutes with every insertion. -/
theorem evenPolynomial_commute (C P : JetAlgebra G) (hc : parity C = C) :
    C * P = P * C := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp
  | add P Q hP hQ => simp only [mul_add, add_mul, hP, hQ]
  | smul c P hP => simp only [mul_smul_comm, smul_mul_assoc, hP]
  | mul P j hP =>
      have hj : C * jet j = jet j * C := by
        by_cases hj : j.field.parity = true
        · have h := (oddJet_mul_polynomial (G := G) ⟨j,hj⟩ C).symm
          simpa only [hc, jet, hj, dif_pos] using h
        · have h := evenJet_commute (G := G)
            ⟨j, by cases h : j.field.parity <;> simp_all⟩ C
          simpa only [jet, hj, dif_neg] using h.symm
      rw [← mul_assoc, hP, mul_assoc, hj, ← mul_assoc]

/-- An actually odd local superpolynomial commutes with the parity of the
other factor. This uses the actual exterior algebra, not a supplied sign. -/
theorem oddPolynomial_commute (C P : JetAlgebra G) (hc : parity C = -C) :
    C * P = parity P * C := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp [parity_one]
  | add P Q hP hQ => simp only [mul_add, map_add, add_mul, hP, hQ]
  | smul c P hP => simp only [mul_smul_comm, smul_mul_assoc, map_smul, hP]
  | mul P j hP =>
      by_cases hj : j.field.parity = true
      · have commute : C * jet j = -(jet j * C) := by
          have h := oddJet_mul_polynomial (G := G) ⟨j,hj⟩ C
          have h' : jet j * C = (-C) * jet j := by
            simpa only [hc, jet, hj, dif_pos] using h
          calc
            C * jet j = -((-C) * jet j) := by rw [neg_mul C (jet j), neg_neg]
            _ = -(jet j * C) := congrArg Neg.neg h'.symm
        rw [← mul_assoc, hP, mul_assoc, commute, parity_mul, parity_jet]
        simp only [hj, if_true, mul_assoc]
        rw [neg_mul (jet j) C]
      · have commute : C * jet j = jet j * C := by
          have h := evenJet_commute (G := G)
            ⟨j, by cases h : j.field.parity <;> simp_all⟩ C
          simpa only [jet, hj, dif_neg] using h.symm
        rw [← mul_assoc, hP, mul_assoc, commute, parity_mul, parity_jet]
        simp [hj, mul_assoc]

end YangMills.FullBV
