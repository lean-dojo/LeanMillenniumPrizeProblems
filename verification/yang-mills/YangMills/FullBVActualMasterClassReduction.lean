import YangMills.FullBVSourceCharacteristicVariation
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The source current is a proved divergence, so the actual full source
functional equals its master-derived characteristic presentation. -/
theorem sourceCharacteristic_class {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    localClass (sourceCharacteristicDensity e g) = localClass (fullAntifieldDensity e g) := by
  have hs := congrArg (divergences G).mkQ (fullAntifieldDensity_characteristic e g)
  simp only [map_add, map_sum] at hs
  change localClass (sourceCharacteristicDensity e g) +
    (∑ a : Fin G.dimension, ∑ mu : Fin 4,
      localClass (totalDerivative mu (sourceShiftCurrent e g a mu))) =
      localClass (fullAntifieldDensity e g) at hs
  simpa only [totalDerivative_class_zero, Finset.sum_const_zero, add_zero] using hs

/-- Actual same-action ST variation reduces to the source-characteristic
variation because the actual physical action was proved invariant and the
source change was proved to be a total divergence. -/
theorem classicalLocalST_master_class_reduction {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    localClass (classicalLocalSTDensity e g (masterActionDensity e g)) =
      localClass (classicalLocalSTDensity e g (sourceCharacteristicDensity e g)) := by
  have hm : masterActionDensity e g = physicalGaugeFixedDensity e g + fullAntifieldDensity e g :=
    masterDensity_physical_antifield e g
  have ha := localST_localClass_eq (masterActionDensity e g)
    (sourceCharacteristicDensity e g) (fullAntifieldDensity e g) (sourceCharacteristic_class e g)
  change localClass (localST (masterActionDensity e g) (masterActionDensity e g)) = _
  have hST : localST (masterActionDensity e g) (masterActionDensity e g) =
      localST (masterActionDensity e g) (physicalGaugeFixedDensity e g) +
        localST (masterActionDensity e g) (fullAntifieldDensity e g) :=
    (congrArg (localST (masterActionDensity e g)) hm).trans (localST_add _ _ _)
  rw [hST]
  change (divergences G).mkQ (_ + _) = _
  rw [map_add]
  change localClass (classicalLocalSTDensity e g (physicalGaugeFixedDensity e g)) +
    localClass (localST (masterActionDensity e g) (fullAntifieldDensity e g)) = _
  rw [classicalLocalST_physicalGaugeFixed_class, zero_add]
  exact ha.symm

/-- No master equation is assumed here: the full actual master variation is
reduced to this explicit actual basic-field Euler contraction. -/
theorem classicalLocalST_master_class_basicEuler {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    localClass (classicalLocalSTDensity e g (masterActionDensity e g)) =
      localClass (∑ K : BasicField G,
        (if K.fermionic then (-1 : ℂ) else 1) •
          (stCharacteristic (masterActionDensity e g) (.inl K) *
            rightEuler (.inl K) (masterActionDensity e g))) := by
  rw [classicalLocalST_master_class_reduction, classicalLocalST_sourceCharacteristic]

end YangMills.FullBV
