import Problems.YangMills.FullBVGradedDerivation
import Problems.YangMills.FullBVClassicalSTParity
import Problems.YangMills.FullBVAntighostAntifield

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem oddCharacteristics_of_even (S : JetAlgebra G) (hS : parity S = S) : OddCharacteristics S := by
  intro j
  cases hj : j.field.parity <;>
    simpa only [hj, Bool.false_eq_true, if_false, if_true, one_smul, complex_neg_one_smul] using
      prolongedST_even_parity S hS j

theorem localST_mul_even (S : JetAlgebra G) (hS : parity S = S) (P Q : JetAlgebra G) :
    localST S (P*Q) = localST S P * Q + parity P * localST S Q :=
  localST_mul_graded S P Q (oddCharacteristics_of_even S hS)

/-- The square of the actual odd evolutionary differential is an ordinary
derivation. All mixed terms cancel with the proved actual parity rule. -/
theorem localST_square_mul (S : JetAlgebra G) (hS : parity S = S) (P Q : JetAlgebra G) :
    localST S (localST S (P*Q)) =
      localST S (localST S P) * Q + P * localST S (localST S Q) := by
  simp only [localST_mul_even S hS, localST_add, localST_even_parity S hS, parity_parity]
  have hn (X Y : JetAlgebra G) : (-X)*Y = -(X*Y) := neg_mul X Y
  rw [hn]
  abel

/-- Nilpotency on zero-order coordinates propagates to every derivative
insertion through the actual evolutionary commutation identity. -/
theorem localST_square_jet_of_coordinate (S : JetAlgebra G) (field : ExternalLeg G)
    (base : localST S (localST S (jet ⟨field,0⟩)) = 0) (alpha : Multiindex) :
    localST S (localST S (jet ⟨field,alpha⟩)) = 0 := by
  have hb : localST S (stCharacteristic S field) = 0 := by
    simpa only [localST_jet, totalDerivatives_zero] using base
  rw [localST_jet, ← totalDerivatives_localST, hb, totalDerivatives_zeroInput]

/-- An even action's actual coordinate nilpotency suffices for its full
polynomial nilpotency. This theorem does not assume or declare the missing
interacting antifield coordinate identities. -/
theorem localST_square_of_jets (S : JetAlgebra G) (hS : parity S = S)
    (jets : ∀ j : Jet G, localST S (localST S (jet j)) = 0) (P : JetAlgebra G) :
    localST S (localST S P) = 0 := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp [localST_one]
  | add P Q hP hQ => simp only [localST_add, hP, hQ, add_zero]
  | smul c P hP => simp only [localST_smul, hP, smul_zero]
  | mul P j hP => rw [localST_square_mul S hS, hP, jets j, zero_mul, mul_zero, add_zero]

/-- The actual quadratic BV action is nilpotent on the whole local
polynomial/exterior algebra, not only its generating jets. -/
theorem freeLocalST_square (P : JetAlgebra G) :
    freeLocalSTDensity G (freeLocalSTDensity G P) = 0 := by
  apply localST_square_of_jets
  · exact parity_densityOfVertices_even 0 (freeActionVertices G)
      (fun v hv => freeActionVertices_even v hv)
  · exact freeLocalST_square_jet

/-- Every derivative of every basic interacting field has vanishing square,
from the SAME actual group-specific master action. -/
theorem classicalLocalST_square_basic_jet {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (K : BasicField G) (alpha : Multiindex) :
    classicalLocalSTDensity e g (classicalLocalSTDensity e g (jet ⟨.inl K,alpha⟩)) = 0 :=
  localST_square_jet_of_coordinate _ _ (classicalLocalST_square_basic e g K) alpha

end YangMills.FullBV
