import YangMills.FullBVMasterQuadratic

/-! Same-action free BV coordinate computations. No master-equation axiom. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

@[simp] theorem complex_neg_one_smul (P : JetAlgebra G) : (-1 : ℂ) • P = -P :=
  neg_one_smul ℂ P

theorem leftEuler_sum {I : Type*} (s : Finset I) (P : I → JetAlgebra G)
    (field : ExternalLeg G) : leftEuler field (∑ i ∈ s, P i) = ∑ i ∈ s, leftEuler field (P i) :=
  map_sum (leftEulerLinear field) P s

theorem rightEuler_sum {I : Type*} (s : Finset I) (P : I → JetAlgebra G)
    (field : ExternalLeg G) : rightEuler field (∑ i ∈ s, P i) = ∑ i ∈ s, rightEuler field (P i) :=
  map_sum (rightEulerLinear field) P s

@[simp] theorem leftEuler_neg (field : ExternalLeg G) (P : JetAlgebra G) :
    leftEuler field (-P) = -leftEuler field P := map_neg (leftEulerLinear field) P

@[simp] theorem totalDerivatives_neg (alpha : Multiindex) (P : JetAlgebra G) :
    totalDerivatives alpha (-P) = -totalDerivatives alpha P := by
  simpa only [complex_neg_one_smul] using totalDerivatives_smul alpha (-1 : ℂ) P

@[simp] theorem single_one_add_one (mu : Fin 4) :
    (Pi.single mu 1 : Multiindex) + Pi.single mu 1 = Pi.single mu 2 := by
  funext nu
  by_cases h : mu = nu <;> simp [Pi.single_apply, h, eq_comm]

/-- Every quadratic summand of the same fixed free action is even. Thus its
right Euler derivative has the fixed species parity, including antifields. -/
theorem rightEuler_freeActionDensity (field : ExternalLeg G) :
    rightEuler field (freeActionDensity G) =
      (if field.parity then (-1 : ℂ) else 1) • leftEuler field (freeActionDensity G) := by
  have h0 (a : Fin G.dimension) (alpha beta : Multiindex) :
      rightEuler field (jet ⟨.inl (.auxiliary a), alpha⟩ * jet ⟨.inr (.antighost a), beta⟩) =
        (if field.parity then (-1 : ℂ) else 1) •
          leftEuler field (jet ⟨.inl (.auxiliary a), alpha⟩ * jet ⟨.inr (.antighost a), beta⟩) :=
    rightEuler_even_quadratic _ _ _ (by rfl)
  have h1 (a : Fin G.dimension) (mu : Fin 4) (alpha beta : Multiindex) :
      rightEuler field (jet ⟨.inl (.ghost a), alpha⟩ * jet ⟨.inr (.gauge mu a), beta⟩) =
        (if field.parity then (-1 : ℂ) else 1) •
          leftEuler field (jet ⟨.inl (.ghost a), alpha⟩ * jet ⟨.inr (.gauge mu a), beta⟩) :=
    rightEuler_even_quadratic _ _ _ (by rfl)
  have h2 (a : Fin G.dimension) (mu : Fin 4) (alpha beta : Multiindex) :
      rightEuler field (jet ⟨.inl (.gauge mu a), alpha⟩ * jet ⟨.inr (.antighost a), beta⟩) =
        (if field.parity then (-1 : ℂ) else 1) •
          leftEuler field (jet ⟨.inl (.gauge mu a), alpha⟩ * jet ⟨.inr (.antighost a), beta⟩) :=
    rightEuler_even_quadratic _ _ _ (by rfl)
  have h3 (a : Fin G.dimension) (alpha beta : Multiindex) :
      rightEuler field (jet ⟨.inl (.ghost a), alpha⟩ * jet ⟨.inr (.auxiliary a), beta⟩) =
        (if field.parity then (-1 : ℂ) else 1) •
          leftEuler field (jet ⟨.inl (.ghost a), alpha⟩ * jet ⟨.inr (.auxiliary a), beta⟩) :=
    rightEuler_even_quadratic _ _ _ (by rfl)
  have h4 (a : Fin G.dimension) (alpha beta : Multiindex) :
      rightEuler field (jet ⟨.inl (.antighost a), alpha⟩ * jet ⟨.inl (.ghost a), beta⟩) =
        (if field.parity then (-1 : ℂ) else 1) •
          leftEuler field (jet ⟨.inl (.antighost a), alpha⟩ * jet ⟨.inl (.ghost a), beta⟩) :=
    rightEuler_even_quadratic _ _ _ (by rfl)
  rw [freeActionDensity_eq_quadratic]
  simp only [freeDensityQuadratic, rightEuler_sum, leftEuler_sum, rightEuler_add,
    leftEuler_add, rightEuler_smul, leftEuler_smul, Finset.smul_sum, smul_add]
  simp_rw [rightEuler_even_quadratic field _ _ (by rfl)]
  simp only [h0, h1, h2, h3, h4, smul_smul, mul_comm]

theorem derivativeOrder_zero : derivativeOrder (0 : Multiindex) = 0 := by
  simp [derivativeOrder]

theorem derivativeOrder_single (mu : Fin 4) (n : ℕ) :
    derivativeOrder (Pi.single mu n) = n := by
  simp [derivativeOrder]

@[simp] theorem totalDerivatives_zero (P : JetAlgebra G) : totalDerivatives 0 P = P := by
  simp [totalDerivatives, derivativeList, List.finRange_succ]

/-- Free shifted-B BRST on the actual gauge coordinate. -/
theorem free_characteristic_gauge (mu : Fin 4) (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inl (.gauge mu a)) =
      jet ⟨.inl (.ghost a), Pi.single mu 1⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, parity_jet, ite_and]

 theorem free_characteristic_ghost (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inl (.ghost a)) = 0 := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic]

 theorem free_characteristic_antighost (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inl (.antighost a)) =
      Complex.I • jet ⟨.inl (.auxiliary a), 0⟩ +
        ∑ mu : Fin 4, jet ⟨.inl (.gauge mu a), Pi.single mu 1⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, Finset.sum_add_distrib]
  module

 theorem free_characteristic_auxiliary (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inl (.auxiliary a)) =
      Complex.I • ∑ mu : Fin 4, jet ⟨.inl (.ghost a), Pi.single mu 2⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, parity_jet, ← Finset.smul_sum]

theorem free_characteristic_antigauge (mu : Fin 4) (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inr (.gauge mu a)) =
      -(∑ nu : Fin 4, jet ⟨.inl (.gauge mu a), Pi.single nu 2⟩) +
        jet ⟨.inr (.antighost a), Pi.single mu 1⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, derivativeOrder_single,
    totalDerivatives_jet, parity_jet, Finset.sum_add_distrib, ite_and]
  simp only [← Finset.smul_sum]
  module


theorem free_characteristic_antighostSource (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inr (.ghost a)) =
      -(∑ mu : Fin 4, jet ⟨.inl (.antighost a), Pi.single mu 2⟩) -
      (∑ mu : Fin 4, jet ⟨.inr (.gauge mu a), Pi.single mu 1⟩) +
      Complex.I • ∑ mu : Fin 4, jet ⟨.inr (.auxiliary a), Pi.single mu 2⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, derivativeOrder_single,
    totalDerivatives_jet, parity_jet, Finset.sum_add_distrib, ite_and]
  simp only [sub_eq_add_neg, ← Finset.smul_sum]
  module

theorem free_characteristic_antiantighost (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inr (.antighost a)) =
      ∑ mu : Fin 4, jet ⟨.inl (.ghost a), Pi.single mu 2⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, derivativeOrder_single,
    totalDerivatives_jet, parity_jet, Finset.sum_add_distrib, ite_and]

theorem free_characteristic_antiauxiliary (a : Fin G.dimension) :
    stCharacteristic (freeActionDensity G) (.inr (.auxiliary a)) =
      jet ⟨.inl (.auxiliary a), 0⟩ - Complex.I • jet ⟨.inr (.antighost a), 0⟩ := by
  classical
  simp only [stCharacteristic, rightEuler_freeActionDensity]
  simp [freeActionDensity_eq_quadratic, freeDensityQuadratic, leftEuler_sum,
    leftEuler_add, leftEuler_smul, leftEuler_quadratic, ExternalLeg.parity,
    BasicField.fermionic, derivativeOrder_zero, derivativeOrder_single,
    totalDerivatives_jet, parity_jet, Finset.sum_add_distrib, ite_and]
  module

end YangMills.FullBV
