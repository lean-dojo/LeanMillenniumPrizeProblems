import Problems.YangMills.FullBVPolynomialInduction

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

@[simp] theorem jet_even (j : EvenJet G) : jet j.val = evenJet j := by
  simp [jet, j.property]

@[simp] theorem jet_odd (j : OddJet G) : jet j.val = oddJet j := by
  simp [jet, j.property]

theorem polynomial_induction_jet {P : JetAlgebra G → Prop}
    (zero : P 0) (one : P 1)
    (add : ∀ a b, P a → P b → P (a+b))
    (smul : ∀ (c : ℂ) a, P a → P (c • a))
    (mul : ∀ a (j : Jet G), P a → P (a * jet j)) (a : JetAlgebra G) : P a := by
  apply polynomial_induction zero one add smul _ _ a
  · intro a j ha; simpa only [jet_even] using mul a j.val ha
  · intro a j ha; simpa only [jet_odd] using mul a j.val ha

attribute [local simp] totalDerivative_one

/-- Ordinary coordinate derivatives act on the full local insertion algebra,
without quotienting by divergence or assuming homogeneous inputs. -/
theorem totalDerivative_mul (mu : Fin 4) (P Q : JetAlgebra G) :
    totalDerivative mu (P * Q) = totalDerivative mu P * Q + P * totalDerivative mu Q := by
  induction Q using polynomial_induction_jet with
  | zero => simp
  | one => simp
  | add Q R hQ hR =>
      simp only [mul_add, totalDerivative_add, hQ, hR]
      abel
  | smul c Q hQ =>
      simp only [mul_smul_comm, totalDerivative_smul, hQ, smul_add]
  | mul Q j hQ =>
      rw [← mul_assoc, totalDerivative_mul_jet_ordinary, hQ,
        totalDerivative_mul_jet_ordinary]
      simp only [add_mul, mul_add, mul_assoc]
      abel

@[simp] theorem Jet.shift_shift (j : Jet G) (mu nu : Fin 4) :
    (j.shift mu).shift nu = (j.shift nu).shift mu := by
  simp [Jet.shift, add_right_comm]

/-- The actual total coordinate derivatives commute on arbitrary local
superpolynomials, including all antifield and odd-jet factors. -/
theorem totalDerivative_comm (mu nu : Fin 4) (P : JetAlgebra G) :
    totalDerivative mu (totalDerivative nu P) = totalDerivative nu (totalDerivative mu P) := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp
  | add P Q hP hQ => simp only [totalDerivative_add, hP, hQ]
  | smul c P hP => simp only [totalDerivative_smul, hP]
  | mul P j hP =>
      simp only [totalDerivative_mul, totalDerivative_add, totalDerivative_jet, hP]
      rw [Jet.shift_shift]
      abel

end YangMills.FullBV
