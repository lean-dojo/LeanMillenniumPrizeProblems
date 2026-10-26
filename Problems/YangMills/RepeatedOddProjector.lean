import Problems.YangMills.OddTranspositionSign
import Problems.YangMills.OriginAlternatingJet

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 2000000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative YangMills.LegendreInsertionBridge
variable {G : CompactSimpleGaugeGroup}
local instance repeatedOddDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

lemma LocalMonomial.jetAt_fiber_card (m : LocalMonomial G) (v : JetVariable G) :
    Fintype.card {i : Fin m.legs.length // m.jetAt i = v} = m v := by
  classical
  let slots : Fin m.legs.length ≃ Fin m.orderedJets.length := finCongr (by simp [LocalMonomial.legs])
  let fibers : {i : Fin m.legs.length // m.jetAt i = v} ≃
      {j : Fin m.orderedJets.length // m.orderedJets.get j = v} :=
    slots.subtypeEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr fibers,listGet_fiber_card,LocalMonomial.orderedJets_count]

lemma LocalMonomial.nonadmissible_repeated_odd (m : LocalMonomial G) (invalid : ¬ m.Admissible) :
    ∃ i j : Fin m.legs.length, i ≠ j ∧ m.jetAt i = m.jetAt j ∧ (m.legs.get i).parity = true := by
  classical
  unfold LocalMonomial.Admissible at invalid
  push Not at invalid
  obtain ⟨v,odd,count⟩ := invalid
  have cardinal : 1 < Fintype.card {i : Fin m.legs.length // m.jetAt i = v} := by
    rw [m.jetAt_fiber_card]
    exact count
  obtain ⟨i,j,distinct⟩ := Fintype.one_lt_card_iff.mp cardinal
  refine ⟨i.val,j.val,(fun equal => distinct (Subtype.ext equal)),i.property.trans j.property.symm,?_⟩
  rw [← m.jetAt_field i.val,i.property]
  exact odd

lemma LocalMonomial.momentumDirections_swap_perm (m : LocalMonomial G) (i j : Fin m.legs.length)
    (sameJet : m.jetAt i = m.jetAt j) :
    (m.momentumDirections.map (fun d => (Equiv.swap i j d.1,d.2))).Perm m.momentumDirections := by
  classical
  apply List.perm_iff_count.mpr
  rintro ⟨k,mu⟩
  have injective : Function.Injective (fun d : Fin m.legs.length × Fin 4 => (Equiv.swap i j d.1,d.2)) :=
    (Equiv.prodCongr (Equiv.swap i j) (Equiv.refl (Fin 4))).injective
  have counted := List.count_map_of_injective m.momentumDirections
    (fun d : Fin m.legs.length × Fin 4 => (Equiv.swap i j d.1,d.2)) injective (Equiv.swap i j k,mu)
  simp only [Equiv.swap_apply_self] at counted
  rw [counted,m.momentumDirections_count,m.momentumDirections_count]
  by_cases ki : k=i
  · subst k
    simp only [Equiv.swap_apply_left,sameJet]
  · by_cases kj : k=j
    · subst k
      simp only [Equiv.swap_apply_right,sameJet]
    · rw [Equiv.swap_apply_of_ne_of_ne ki kj]

lemma permutationFields_of_preserved (legs : List (ExternalLeg G))
    (pi : Equiv.Perm (Fin legs.length)) (preserved : ∀ i, legs.get (pi i) = legs.get i) :
    permutedLegs legs pi = legs := by
  unfold permutedLegs
  rw [show (fun i => legs.get (pi i)) = legs.get from funext preserved,List.ofFn_get]

lemma orderedAmplitude_relabel_transport (A : OrderedAmplitude G)
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (legs : List (ExternalLeg G)) (pi : Equiv.Perm (Fin legs.length))
    (fields : permutedLegs legs pi = legs) :
    A legs ∘ momentumCoordinateRelabel pi = fun q => permutationSign legs pi * A legs q := by
  funext q
  have actual := graded legs q pi
  have components := orderedAmplitude_component_congr A fields (permutedMomenta legs pi q)
    (momentumCoordinateRelabel pi q) (by intro i; rfl)
  exact components.symm.trans actual

/-- The exterior nilpotence restriction in the source projectors loses no
Taylor coefficient at zero: a repeated odd jet is forced to vanish by the
SAME amplitude's actual graded symmetry and ordinary momentum calculus. -/
theorem extractCoefficient_nonadmissible_zero (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (m : LocalMonomial G) (invalid : ¬ m.Admissible) : extractCoefficient m A 0 = 0 := by
  classical
  obtain ⟨i,j,distinct,sameJet,odd_i⟩ := m.nonadmissible_repeated_odd invalid
  have fields_equal : m.legs.get i = m.legs.get j := by
    rw [← m.jetAt_field i,← m.jetAt_field j,sameJet]
  have odd_j : (m.legs.get j).parity = true := by rw [← fields_equal]; exact odd_i
  have fields : permutedLegs m.legs (Equiv.swap i j) = m.legs := by
    apply permutationFields_of_preserved
    intro k
    by_cases ki : k=i
    · subst k
      simpa only [Equiv.swap_apply_left] using fields_equal.symm
    · by_cases kj : k=j
      · subst k
        simpa only [Equiv.swap_apply_right] using fields_equal
      · rw [Equiv.swap_apply_of_ne_of_ne ki kj]
  have transport := orderedAmplitude_relabel_transport A graded m.legs (Equiv.swap i j) fields
  rw [permutationSign_swap_odd m.legs i j distinct odd_i odd_j] at transport
  simp only [neg_one_mul] at transport
  apply (extractCoefficient_zero_iff m A 0).mpr
  apply momentumJet_origin_zero_of_antisymmetry m.legs (Equiv.swap i j) m.momentumDirections (smooth _)
  · exact transport
  · simpa only [Equiv.symm_swap] using m.momentumDirections_swap_perm i j sameJet

end YangMills.PerturbativeFlow
