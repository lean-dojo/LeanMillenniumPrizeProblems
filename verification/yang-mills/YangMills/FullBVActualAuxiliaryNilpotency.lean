import YangMills.FullBVOrdinaryJetDerivation
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem derivativeList_single_two (mu : Fin 4) :
    derivativeList (Pi.single mu 2) = [mu, mu] := by
  fin_cases mu <;> simp [derivativeList, List.finRange_succ, Pi.single_apply]

theorem totalDerivatives_single_two (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivatives (Pi.single mu 2) P = totalDerivative mu (totalDerivative mu P) := by
  simp [totalDerivatives, derivativeList_single_two]

/-- Exact evolutionary commutation on the actual gauge-ghost quadratic
vertex; the Hamiltonian images themselves are extracted from arbitrary S. -/
theorem localST_totalDerivative_gaugeGhostPair (S : JetAlgebra G) (mu nu : Fin 4)
    (b c : Fin G.dimension) :
    localST S (totalDerivative mu
      (jet ⟨.inl (.gauge nu b), 0⟩ * ghostJet G c)) =
    totalDerivative mu (localST S
      (jet ⟨.inl (.gauge nu b), 0⟩ * ghostJet G c)) := by
  simp only [totalDerivative_mul_jet_ordinary, totalDerivative_jet, localST_add,
    localST_mul_jet, localST_jet, prolongedST, parity_jet, ExternalLeg.parity,
    BasicField.fermionic, if_true, if_false, Jet.shift, zero_add,
    totalDerivatives_zero, totalDerivatives_single_one, totalDerivative_add]
  simp only [Bool.false_eq_true, if_false]
  rw [totalDerivative_mul_jet_ordinary, totalDerivative_jet]
  simp only [Jet.shift, zero_add]
  abel

theorem localST_totalDerivative_gaugeQuadratic (S : JetAlgebra G)
    {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) (mu nu : Fin 4)
    (a : Fin G.dimension) :
    localST S (totalDerivative mu (gaugeQuadratic e g nu a)) =
      totalDerivative mu (localST S (gaugeQuadratic e g nu a)) := by
  simp only [gaugeQuadratic, totalDerivative_sum, totalDerivative_smul,
    localST_sum, localST_smul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  exact localST_totalDerivative_gaugeGhostPair S mu nu b c

theorem localST_totalDerivative_sameGhostDerivative (S : JetAlgebra G)
    (mu : Fin 4) (a : Fin G.dimension) :
    localST S (totalDerivative mu (jet ⟨.inl (.ghost a), Pi.single mu 1⟩)) =
      totalDerivative mu (localST S (jet ⟨.inl (.ghost a), Pi.single mu 1⟩)) := by
  rw [totalDerivative_jet]
  simp only [Jet.shift, single_one_add_one, localST_jet,
    totalDerivatives_single_one, totalDerivatives_single_two]

/-- Exact commutation needed by the shifted B relation; no global
mixed-derivative or full CME hypothesis is substituted. -/
theorem localST_totalDerivative_gaugeCharacteristic {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    localST (masterActionDensity e g)
      (totalDerivative mu (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))) =
      totalDerivative mu (localST (masterActionDensity e g)
        (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))) := by
  have hA : stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) =
      jet ⟨.inl (.ghost a), Pi.single mu 1⟩ + gaugeQuadratic e g mu a :=
    master_characteristic_gauge e g mu a
  rw [hA, totalDerivative_add, localST_add, localST_add, totalDerivative_add,
    localST_totalDerivative_gaugeQuadratic, localST_totalDerivative_sameGhostDerivative]

/-- Full nonlinear shifted-auxiliary nilpotency for the actual master
 action. It follows from the proved same-action sB=i div(sA), actual
 evolutionary commutation on these vertices, and proved gauge nilpotency. -/
theorem classicalLocalST_square_auxiliary {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inl (.auxiliary a), 0⟩)) = 0 := by
  simp only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero,
    master_characteristic_auxiliary_divergence, localST_smul, localST_sum,
    totalDerivatives_single_one, localST_totalDerivative_gaugeCharacteristic]
  have hA (mu : Fin 4) : localST (masterActionDensity e g)
      (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) = 0 := by
    simpa only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero] using
      classicalLocalST_square_gauge e g mu a
  simp only [hA, totalDerivative_zero, Finset.sum_const_zero, smul_zero]

end YangMills.FullBV
