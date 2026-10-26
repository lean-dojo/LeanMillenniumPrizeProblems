import YangMills.FullBVOrdinaryJetDerivation

/-!
# Arbitrary local superpolynomials from the actual jet generators

This induction principle keeps the full polynomial/exterior algebra; it
never replaces a point insertion by its integrated divergence class.
-/
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

/-- Linear closure and right multiplication by the actual even/odd jets
suffice for every local superpolynomial. -/
theorem polynomial_induction {P : JetAlgebra G → Prop}
    (zero : P 0) (one : P 1)
    (add : ∀ a b, P a → P b → P (a+b))
    (smul : ∀ (c : ℂ) a, P a → P (c • a))
    (even : ∀ a (j : EvenJet G), P a → P (a * evenJet j))
    (odd : ∀ a (j : OddJet G), P a → P (a * oddJet j))
    (a : JetAlgebra G) : P a := by
  classical
  induction a using TensorProduct.induction_on with
  | zero => exact zero
  | add a b ha hb => exact add a b ha hb
  | tmul p u =>
    have base : P (TensorProduct.tmul ℂ p 1) := by
      induction p using MvPolynomial.induction_on with
      | C c =>
          have hc : MvPolynomial.C c = c • (1 : MvPolynomial (EvenJet G) ℂ) :=
            Algebra.algebraMap_eq_smul_one c
          rw [hc, ← TensorProduct.smul_tmul']
          simpa only [Algebra.TensorProduct.one_def] using smul c 1 one
      | add p q hp hq => simpa only [TensorProduct.add_tmul] using add _ _ hp hq
      | mul_X p j hp =>
          simpa only [evenJet, Algebra.TensorProduct.tmul_mul_tmul, mul_one] using even _ j hp
    induction u using CliffordAlgebra.right_induction with
    | algebraMap c =>
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
        exact smul c _ base
    | add u v hu hv => simpa only [TensorProduct.tmul_add] using add _ _ hu hv
    | mul_ι v u hu =>
        induction v using Finsupp.induction_linear with
        | zero => simpa using zero
        | add v w hv hw =>
            simpa only [map_add, mul_add, TensorProduct.tmul_add] using add _ _ hv hw
        | single j c =>
            have hv : Finsupp.single j c = c • Finsupp.single j (1 : ℂ) := by simp
            rw [hv, map_smul, mul_smul_comm, TensorProduct.tmul_smul]
            apply smul
            simpa only [oddJet, Algebra.TensorProduct.tmul_mul_tmul, mul_one] using odd _ j hu

end YangMills.FullBV
