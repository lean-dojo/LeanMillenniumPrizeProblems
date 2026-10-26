import YangMills.FullBVHomogeneousCommutation
import YangMills.FullBVEvolutionaryDerivation
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

/-- Concrete parity condition on the actual prolonged Hamiltonian images.
This is a theorem hypothesis for a general S, not a new candidate field. -/
def OddCharacteristics (S : JetAlgebra G) : Prop :=
  ∀ j : Jet G, parity (prolongedST S j) =
    if j.field.parity then prolongedST S j else -prolongedST S j

theorem localST_mul_jet_graded (S P : JetAlgebra G) (hS : OddCharacteristics S) (j : Jet G) :
    localST S (P * jet j) = localST S P * jet j + parity P * localST S (jet j) := by
  rw [localST_mul_jet, localST_jet]
  change _ + _ = _ + parity P * prolongedST S j
  congr 1
  by_cases hj : j.field.parity = true
  · have hc : parity (prolongedST S j) = prolongedST S j := by simpa only [hj, if_true] using hS j
    simpa only [hj, if_true] using evenPolynomial_commute (prolongedST S j) (parity P) hc
  · have hc : parity (prolongedST S j) = -prolongedST S j := by
      simpa only [hj, if_false] using hS j
    simpa only [hj, if_false] using oddPolynomial_commute (prolongedST S j) P hc

/-- Full graded Leibniz on every local polynomial, derived from the actual
jet images and the actual exterior-algebra parity. -/
theorem localST_mul_graded (S P Q : JetAlgebra G) (hS : OddCharacteristics S) :
    localST S (P*Q) = localST S P * Q + parity P * localST S Q := by
  induction Q using polynomial_induction_jet with
  | zero => simp
  | one => simp [localST_one]
  | add Q R hQ hR =>
      simp only [mul_add, localST_add, hQ, hR]
      abel
  | smul c Q hQ => simp only [mul_smul_comm, localST_smul, hQ, smul_add]
  | mul Q j hQ =>
      rw [← mul_assoc, localST_mul_jet_graded S _ hS, hQ,
        localST_mul_jet_graded S Q hS, parity_mul]
      simp only [add_mul, mul_add, mul_assoc]
      abel

end YangMills.FullBV
