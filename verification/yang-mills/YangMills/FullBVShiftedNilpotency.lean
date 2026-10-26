import YangMills.FullBVInteractingCoordinates
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Jacobi for precisely the actual color tensors appearing in the BV
vertices, derived by taking coordinates of G's Lie Jacobi identity. -/
theorem structureConstant_jacobi {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) :
    (∑ r : Fin G.dimension, structureConstant e a b r * structureConstant e r c d) +
    (∑ r : Fin G.dimension, structureConstant e a c r * structureConstant e r d b) +
    (∑ r : Fin G.dimension, structureConstant e a d r * structureConstant e r b c) = 0 := by
  have h := congrArg (fun X : G.Algebra => e.basis.repr X a)
    (lie_jacobi (e.basis b) (e.basis c) (e.basis d))
  simpa [bracket_coordinates, Finsupp.single_apply, ite_mul, mul_ite] using h

private theorem sum_three_rotate {I J K M : Type*} [Fintype I] [Fintype J]
    [Fintype K] [AddCommMonoid M] (F : I → J → K → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ k, ∑ i, ∑ j, F i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, F i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The shifted auxiliary coordinate is exactly i times the divergence of
the SAME nonlinear gauge characteristic, including its actual G vertex. -/
theorem master_characteristic_auxiliary_divergence {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inl (.auxiliary a)) =
      Complex.I • ∑ mu : Fin 4, totalDerivatives (Pi.single mu 1)
        (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) := by
  rw [master_characteristic_auxiliary]
  simp only [master_characteristic_gauge, totalDerivatives_add, totalDerivatives_sum,
    totalDerivatives_smul, totalDerivatives_jet, zero_add, single_one_add_one,
    Finset.sum_add_distrib, smul_add]
  congr 1
  simp only [Finset.smul_sum, smul_smul, mul_assoc]
  exact sum_three_rotate _

/-- Interacting shifted-antighost nilpotency at the point insertion itself.
No Jacobi/CME hypothesis is used: the B-shift cancels its full nonlinear
gauge divergence. This is not yet nilpotency for A,c,B or antifields. -/
theorem classicalLocalST_square_antighost {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inl (.antighost a), 0⟩)) = 0 := by
  simp only [classicalLocalSTDensity, localST_jet, master_characteristic_antighost,
    totalDerivatives_zero, localST_add, localST_smul, localST_sum,
    master_characteristic_auxiliary_divergence]
  simp only [smul_smul, Complex.I_mul_I, complex_neg_one_smul]
  abel

/-- The interacting action contains no basic shifted-B vertex: its auxiliary
Hamiltonian equation is fixed entirely by the original quadratic BV action. -/
theorem master_characteristic_antiauxiliary {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inr (.auxiliary a)) =
      jet ⟨.inl (.auxiliary a), 0⟩ - Complex.I • jet ⟨.inr (.antighost a), 0⟩ := by
  have hi : rightEuler (.inl (.auxiliary a)) (interactionDensity e g) = 0 := by
    unfold interactionDensity
    apply rightEuler_densityOfVertices_absent
    simp [physicalActionVertices, actionMonomials, cubicMonomials, quarticMonomials,
      ghostMonomials, antifieldActionVertices, List.bind_eq_flatMap]
    aesop
  simpa only [stCharacteristic, masterActionDensity, rightEuler_add, hi, add_zero] using
    free_characteristic_antiauxiliary (G := G) a

end YangMills.FullBV
