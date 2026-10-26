import Problems.YangMills.FullBVFreeCoordinates

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! Same-action free nilpotency; the interacting master identity remains work. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def localSTLinear (S : JetAlgebra G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun := localST S
  map_add' := localST_add S
  map_smul' r P := localST_smul S P r

@[simp] theorem localST_zero (S : JetAlgebra G) : localST S 0 = 0 :=
  map_zero (localSTLinear S)

@[simp] theorem localST_neg (S P : JetAlgebra G) : localST S (-P) = -localST S P :=
  map_neg (localSTLinear S) P

theorem localST_sum {I : Type*} (s : Finset I) (P : I → JetAlgebra G)
    (S : JetAlgebra G) : localST S (∑ i ∈ s, P i) = ∑ i ∈ s, localST S (P i) :=
  map_sum (localSTLinear S) P s

def totalDerivativesLinear (alpha : Multiindex) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun := totalDerivatives alpha
  map_add' := totalDerivatives_add alpha
  map_smul' := totalDerivatives_smul alpha

theorem totalDerivatives_sum {I : Type*} (s : Finset I) (P : I → JetAlgebra G)
    (alpha : Multiindex) : totalDerivatives alpha (∑ i ∈ s, P i) =
      ∑ i ∈ s, totalDerivatives alpha (P i) := map_sum (totalDerivativesLinear alpha) P s

/-- Nilpotency on all free field and antifield descendants, extracted from
exactly the same quadratic BV action as the flow's fixed Hessian. -/
theorem freeLocalST_square_jet (j : Jet G) :
    freeLocalSTDensity G (freeLocalSTDensity G (jet j)) = 0 := by
  classical
  rcases j with ⟨field, alpha⟩
  rcases field with K | K <;> cases K <;>
    simp [freeLocalSTDensity, localST_jet, free_characteristic_gauge,
      free_characteristic_ghost, free_characteristic_antighost,
      free_characteristic_auxiliary, free_characteristic_antigauge,
      free_characteristic_antighostSource, free_characteristic_antiantighost,
      free_characteristic_antiauxiliary, totalDerivatives_sum, totalDerivatives_smul,
      totalDerivatives_jet, totalDerivatives_add, localST_sum, localST_add, localST_smul,
      totalDerivatives_neg, sub_eq_add_neg]

  all_goals try simp only [← add_assoc, single_one_add_one]
  all_goals try simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum, smul_smul, Complex.I_mul_I, complex_neg_one_smul]
  case inl.antighost => abel
  case inr.gauge =>
    have he (mu nu : Fin 4) :
        Pi.single mu 1 + Pi.single nu 2 + alpha =
          Pi.single nu 2 + Pi.single mu 1 + alpha := by abel
    simp only [he]
    abel
  case inr.ghost a =>
    have hs : (∑ mu : Fin 4, ∑ nu : Fin 4,
        jet (G := G) ⟨.inl (.gauge nu a), Pi.single nu 1 + Pi.single mu 2 + alpha⟩) =
      ∑ nu : Fin 4, ∑ mu : Fin 4,
        jet (G := G) ⟨.inl (.gauge nu a), Pi.single mu 2 + Pi.single nu 1 + alpha⟩ := by
      rw [Finset.sum_comm]
      congr 1
      ext nu
      congr 1
      ext mu
      congr 2
      abel
    rw [hs]
    simp only [smul_add, smul_neg, smul_smul, Complex.I_mul_I, complex_neg_one_smul]
    abel

end YangMills.FullBV
