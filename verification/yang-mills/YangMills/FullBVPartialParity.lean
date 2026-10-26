import YangMills.FullBVActionParity
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem contraction_involute (d : Module.Dual ℂ (OddJet G →₀ ℂ))
    (u : ExteriorAlgebra ℂ (OddJet G →₀ ℂ)) :
    CliffordAlgebra.contractLeft (Q := 0) d (CliffordAlgebra.involute u) =
      -(CliffordAlgebra.involute (CliffordAlgebra.contractLeft d u)) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, hu, hv, neg_add]
  | ι_mul u a hu =>
      simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg,
        CliffordAlgebra.contractLeft_ι_mul, hu, map_sub, map_smul]
      simp only [mul_neg, neg_neg, sub_eq_add_neg, neg_add_rev, neg_mul]

theorem evenPartial_parity (j : EvenJet G) (P : JetAlgebra G) :
    evenPartial j (parity P) = parity (evenPartial j P) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ]
  | tmul p u => simp [evenPartial, parity]

theorem oddPartial_parity (j : OddJet G) (P : JetAlgebra G) :
    oddPartial j (parity P) = -(parity (oddPartial j P)) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ, add_comm]
  | tmul p u => simp [oddPartial, parity, contraction_involute, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

/-- Fixed parity covariance of canonical partials on the full actual
superjet algebra; there is no parity convention parameter. -/
theorem leftPartialJet_parity (j : Jet G) (P : JetAlgebra G) :
    leftPartialJet j (parity P) =
      (if j.field.parity then (-1 : ℂ) else 1) • parity (leftPartialJet j P) := by
  by_cases hj : j.field.parity = true
  · simpa [leftPartialJet, hj, complex_neg_one_smul] using
      oddPartial_parity ⟨j, hj⟩ P
  · simpa [leftPartialJet, hj, one_smul] using
      evenPartial_parity ⟨j, by cases h : j.field.parity <;> simp_all⟩ P

end YangMills.FullBV
