import Problems.YangMills.FullBVActualGaugeNilpotency

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem exterior_odd_generator_commute (j : OddJet G)
    (u : ExteriorAlgebra ℂ (OddJet G →₀ ℂ)) :
    ExteriorAlgebra.ι ℂ (Finsupp.single j 1) * u =
      CliffordAlgebra.involute u * ExteriorAlgebra.ι ℂ (Finsupp.single j 1) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.commutes]
  | add u v hu hv => simp [mul_add, add_mul, hu, hv]
  | ι_mul u v hu =>
      have ha : ExteriorAlgebra.ι ℂ (Finsupp.single j 1) * ExteriorAlgebra.ι ℂ v =
          -(ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ (Finsupp.single j 1)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      calc
        _ = (ExteriorAlgebra.ι ℂ (Finsupp.single j 1) * ExteriorAlgebra.ι ℂ v) * u :=
          (mul_assoc _ _ _).symm
        _ = -((ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ (Finsupp.single j 1)) * u) := by
          rw [ha, neg_mul]
        _ = -(ExteriorAlgebra.ι ℂ v * (CliffordAlgebra.involute u *
            ExteriorAlgebra.ι ℂ (Finsupp.single j 1))) := by rw [mul_assoc, hu]
        _ = _ := by simp [map_mul, CliffordAlgebra.involute_ι, mul_assoc]

theorem oddJet_mul_polynomial (j : OddJet G) (P : JetAlgebra G) :
    oddJet j * P = parity P * oddJet j := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp [mul_add, add_mul, hP, hQ]
  | tmul p u =>
      simp [oddJet, parity, Algebra.TensorProduct.tmul_mul_tmul,
        exterior_odd_generator_commute]

theorem oddJet_mul_parity (j : OddJet G) (P : JetAlgebra G) :
    oddJet j * parity P = P * oddJet j := by
  simpa only [parity_parity] using! oddJet_mul_polynomial j (parity P)

/-- The actual ordinary total derivative obeys the ordinary product rule
against any generator, even when the preceding polynomial is inhomogeneous. -/
theorem totalDerivative_mul_jet_ordinary (mu : Fin 4) (P : JetAlgebra G) (j : Jet G) :
    totalDerivative mu (P * jet j) = totalDerivative mu P * jet j + P * totalDerivative mu (jet j) := by
  rw [totalDerivative_mul_jet, totalDerivative_jet]
  congr 1
  by_cases hj : j.field.parity = true
  · simpa only [jet, Jet.shift, hj, dif_pos, if_true] using!
      oddJet_mul_parity (G := G) (oddShift mu ⟨j, hj⟩) P
  · simpa only [jet, Jet.shift, hj, dif_neg, if_false] using!
      evenJet_commute (G := G)
        (evenShift mu ⟨j, by cases h : j.field.parity <;> simp_all⟩) P

end YangMills.FullBV
