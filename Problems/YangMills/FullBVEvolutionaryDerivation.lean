import Problems.YangMills.FullBVMultiDerivativeAlgebra
import Problems.YangMills.FullBVTotalDerivativeParity

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

@[simp] theorem localST_one (S : JetAlgebra G) : localST S 1 = 0 := by
  simp [localST, coordinateDifferential, evenPartial, oddPartial,
    Algebra.TensorProduct.one_def]

theorem totalDerivative_prolongedST (S : JetAlgebra G) (mu : Fin 4) (j : Jet G) :
    totalDerivative mu (prolongedST S j) = prolongedST S (j.shift mu) := by
  exact (totalDerivatives_shift j.derivative mu (stCharacteristic S j.field)).symm

/-- The actual evolutionary ST operator commutes with ordinary spacetime
jet derivatives on every local polynomial. This is an identity of point
insertions, not the assertion that an integrated derivative is zero. -/
theorem totalDerivative_localST (S : JetAlgebra G) (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivative mu (localST S P) = localST S (totalDerivative mu P) := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp [totalDerivative_one]
  | add P Q hP hQ => simp only [localST_add, totalDerivative_add, hP, hQ]
  | smul c P hP => simp only [localST_smul, totalDerivative_smul, hP]
  | mul P j hP =>
      simp only [localST_mul_jet, totalDerivative_add, totalDerivative_mul,
        totalDerivative_jet, localST_add, localST_mul_jet,
        totalDerivative_prolongedST, hP]
      by_cases hj : j.field.parity = true
      · simp only [hj, if_true, Jet.shift, totalDerivative_parity]
        abel
      · simp only [hj, Jet.shift]
        abel

/-- Prolongation commutes with the same local ST differential at every
multiindex, including derivative insertions needed by OPE and stress. -/
theorem totalDerivatives_localST (S : JetAlgebra G) (alpha : Multiindex) (P : JetAlgebra G) :
    totalDerivatives alpha (localST S P) = localST S (totalDerivatives alpha P) := by
  unfold totalDerivatives
  generalize derivativeList alpha = l
  induction l with
  | nil => rfl
  | cons mu l ih =>
      simpa only [List.foldr_cons, ih] using
        totalDerivative_localST S mu (l.foldr totalDerivative P)

end YangMills.FullBV
