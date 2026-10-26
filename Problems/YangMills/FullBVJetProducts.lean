import Problems.YangMills.FullBVActualGhostNilpotency

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem evenJet_commute (j : EvenJet G) (P : JetAlgebra G) :
    evenJet j * P = P * evenJet j := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp [mul_add, add_mul, hP, hQ]
  | tmul p u => simp [evenJet, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

theorem oddJet_anticommute (j k : OddJet G) :
    oddJet j * oddJet k + oddJet k * oddJet j = 0 := by
  simp only [oddJet, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.tmul_add]
  rw [ExteriorAlgebra.ι_add_mul_swap]
  simp

theorem gaugeJet_commute (mu : Fin 4) (a : Fin G.dimension) (alpha : Multiindex)
    (P : JetAlgebra G) :
    jet ⟨.inl (.gauge mu a), alpha⟩ * P = P * jet ⟨.inl (.gauge mu a), alpha⟩ := by
  exact evenJet_commute _ P

theorem ghostJetDeriv_anticommute (a b : Fin G.dimension) (alpha beta : Multiindex) :
    jet ⟨.inl (.ghost a), alpha⟩ * jet ⟨.inl (.ghost b), beta⟩ =
      -(jet ⟨.inl (.ghost b), beta⟩ * jet ⟨.inl (.ghost a), alpha⟩) := by
  apply eq_neg_of_add_eq_zero_left
  exact oddJet_anticommute _ _

theorem derivativeList_single_one (mu : Fin 4) :
    derivativeList (Pi.single mu 1) = [mu] := by
  fin_cases mu <;> simp [derivativeList, List.finRange_succ, Pi.single_apply]

theorem totalDerivatives_single_one (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivatives (Pi.single mu 1) P = totalDerivative mu P := by
  simp [totalDerivatives, derivativeList_single_one]

/-- Actual ordinary total differentiation uses the same right-generator
product computation, before moving the shifted generator through P. -/
theorem totalDerivative_mul_jet (mu : Fin 4) (P : JetAlgebra G) (j : Jet G) :
    totalDerivative mu (P * jet j) = totalDerivative mu P * jet j +
      jet (j.shift mu) * (if j.field.parity then parity P else P) := by
  by_cases hj : j.field.parity = true
  · simpa only [totalDerivative, jet, hj, dif_pos, if_pos, oddShift, Jet.shift] using!
      coordinateDifferential_mul_oddJet
        (fun j => evenJet (evenShift mu j)) (fun j => oddJet (oddShift mu j)) P ⟨j, hj⟩
  · simpa only [totalDerivative, jet, hj, dif_neg, if_neg, evenShift, Jet.shift] using!
      coordinateDifferential_mul_evenJet
        (fun j => evenJet (evenShift mu j)) (fun j => oddJet (oddShift mu j)) P
          ⟨j, by cases h : j.field.parity <;> simp_all⟩

theorem totalDerivative_ghost_pair (mu : Fin 4) (a b : Fin G.dimension) :
    totalDerivative mu (ghostJet G a * ghostJet G b) =
      jet ⟨.inl (.ghost a), Pi.single mu 1⟩ * ghostJet G b +
        ghostJet G a * jet ⟨.inl (.ghost b), Pi.single mu 1⟩ := by
  rw [totalDerivative_mul_jet, totalDerivative_jet]
  simp only [parity_jet, ExternalLeg.parity, BasicField.fermionic, if_true, Jet.shift,
    zero_add]
  congr 1
  change jet (G := G) ⟨.inl (.ghost b), Pi.single mu 1⟩ *
      (-(jet ⟨.inl (.ghost a), 0⟩)) =
    jet ⟨.inl (.ghost a), 0⟩ * jet ⟨.inl (.ghost b), Pi.single mu 1⟩
  have hn : jet (G := G) ⟨.inl (.ghost b), Pi.single mu 1⟩ *
      (-(jet ⟨.inl (.ghost a), 0⟩)) =
      -(jet ⟨.inl (.ghost b), Pi.single mu 1⟩ * jet ⟨.inl (.ghost a), 0⟩) :=
    mul_neg (jet ⟨.inl (.ghost b), Pi.single mu 1⟩) (jet ⟨.inl (.ghost a), 0⟩)
  rw [hn]
  exact (ghostJetDeriv_anticommute a b 0 (Pi.single mu 1)).symm

end YangMills.FullBV
