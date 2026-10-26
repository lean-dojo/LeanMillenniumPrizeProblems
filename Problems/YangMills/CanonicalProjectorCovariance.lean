import Problems.YangMills.CanonicalProjectorEvaluation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

lemma LocalMonomial.jetAt_field (m : LocalMonomial G) (i : Fin m.legs.length) :
    (m.jetAt i).1 = m.legs.get i := by
  simp [LocalMonomial.jetAt,LocalMonomial.legs]

lemma canonicalProjectorSlotEquiv_field (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (i : Fin (directionMonomial legs directions).legs.length) :
    (directionMonomial legs directions).legs.get i =
      legs.get (canonicalProjectorSlotEquiv legs directions i) := by
  rw [← LocalMonomial.jetAt_field]
  exact congrArg Prod.fst (canonicalProjectorSlotEquiv_jet legs directions i)

lemma canonicalProjectorSlot_length (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    (directionMonomial legs directions).legs.length = legs.length := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (canonicalProjectorSlotEquiv legs directions)

def canonicalExternalPermutation (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : Equiv.Perm (Fin legs.length) :=
  (finCongr (canonicalProjectorSlot_length legs directions)).symm.trans
    (canonicalProjectorSlotEquiv legs directions)

/-- Canonical sorting changes only the ordered external slots of the SAME
actual component. The permutation is computed from its jet multiplicities. -/
theorem canonicalExternalPermutation_fields (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    permutedLegs legs (canonicalExternalPermutation legs directions) =
      (directionMonomial legs directions).legs := by
  apply List.ext_get
  · simp only [permutedLegs,List.length_ofFn,canonicalProjectorSlot_length]
  · intro n hn hm
    simp only [permutedLegs,List.get_ofFn]
    exact (canonicalProjectorSlotEquiv_field legs directions ⟨n,hm⟩).symm

end YangMills.PerturbativeFlow
