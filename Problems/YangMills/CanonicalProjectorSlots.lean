import Problems.YangMills.JetListPermutation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def directionMonomial (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : LocalMonomial G :=
  monomialOfJetList (jetListOfDirections legs directions)

/-- Actual canonical-output slots correspond bijectively to the original
external slots, including repeated bosonic or derivative jet labels. -/
def canonicalProjectorSlotEquiv (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    Fin (directionMonomial legs directions).legs.length ≃ Fin legs.length := by
  classical
  exact (finCongr (by simp [LocalMonomial.legs,directionMonomial])).trans
    ((jetListIndexEquiv (orderedJets_perm_ofJetList (jetListOfDirections legs directions))).trans
      (finCongr (by simp [jetListOfDirections])))

/-- Each canonical jet is the SAME original field and the actual number
of derivatives landing on that slot in each spacetime coordinate. -/
theorem canonicalProjectorSlotEquiv_jet (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (i : Fin (directionMonomial legs directions).legs.length) :
    (directionMonomial legs directions).jetAt i =
      (legs.get (canonicalProjectorSlotEquiv legs directions i),
        fun mu => (directions : Multiset _).count (canonicalProjectorSlotEquiv legs directions i,mu)) := by
  classical
  let m := directionMonomial legs directions
  let castSlot : Fin m.legs.length ≃ Fin m.orderedJets.length := finCongr (by simp [LocalMonomial.legs])
  have exactJet := jetListIndexEquiv_get
    (orderedJets_perm_ofJetList (jetListOfDirections legs directions)) (castSlot i)
  change (jetListOfDirections legs directions).get _ = _ at exactJet
  simp only [jetListOfDirections,List.get_ofFn] at exactJet
  exact exactJet.symm

lemma directionMonomial_dimension (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    (directionMonomial legs directions).dimension = totalDimension legs + directions.length :=
  jetListOfDirections_dimension legs directions

end YangMills.PerturbativeFlow
