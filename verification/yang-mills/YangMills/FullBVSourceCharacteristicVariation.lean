import YangMills.FullBVSourceCharacteristicIdentity
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Each same-master basic characteristic is actually ST closed, by the
proved interacting coordinate nilpotency (including all g-dependent terms). -/
theorem classicalLocalST_basicCharacteristic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (K : BasicField G) :
    localST (masterActionDensity e g)
      (stCharacteristic (masterActionDensity e g) (.inl K)) = 0 := by
  simpa only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero] using
    classicalLocalST_square_basic e g K

/-- Exact ST variation of the source-characteristic density. This uses the
same master Euler derivative on the antifields and proved basic nilpotency;
there is no assumed full CME or independent antifield equation. -/
theorem classicalLocalST_sourceCharacteristic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    classicalLocalSTDensity e g (sourceCharacteristicDensity e g) =
      ∑ K : BasicField G,
        (if K.fermionic then (-1 : ℂ) else 1) •
          (stCharacteristic (masterActionDensity e g) (.inl K) *
            rightEuler (.inl K) (masterActionDensity e g)) := by
  rw [sourceCharacteristicDensity_eq_sum]
  change localST (masterActionDensity e g) _ = _
  rw [localST_sum]
  apply Finset.sum_congr rfl; intro K hK
  rw [localST_neg, localST_mul_even _ (parity_masterActionDensity e g),
    classicalLocalST_basicCharacteristic, zero_mul, zero_add,
    localST_jet, totalDerivatives_zero]
  rw [stCharacteristic_even_parity _ (parity_masterActionDensity e g)]
  change -((if K.fermionic then (1 : ℂ) else -1) •
      stCharacteristic (masterActionDensity e g) (.inl K) *
      rightEuler (.inl K) (masterActionDensity e g)) = _
  rw [smul_mul_assoc]
  cases hK : K.fermionic <;>
    simp only [hK, Bool.false_eq_true, if_false, if_true, one_smul]
  all_goals module

end YangMills.FullBV
