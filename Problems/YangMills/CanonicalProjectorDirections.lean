import Problems.YangMills.CanonicalProjectorSlots

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}
local instance projectorDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

lemma orderedMultiindex_count (d : Fin 4 → ℕ) (mu : Fin 4) :
    (orderedMultiindex d).count mu = d mu := by
  simp only [orderedMultiindex,List.count_flatMap,Function.comp_def,List.count_replicate]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp

lemma count_slotMap {n : ℕ} (items : List (Fin 4)) (i j : Fin n) (mu : Fin 4) :
    (items.map (fun nu => (i,nu))).count (j,mu) = if i=j then items.count mu else 0 := by
  by_cases equal : i=j
  · subst j
    simp only [ite_true]
    exact List.count_map_of_injective items (fun nu => (i,nu))
      (by intro x y h; exact congrArg Prod.snd h) mu
  · simp only [equal,ite_false]
    apply List.count_eq_zero.mpr
    intro member
    obtain ⟨nu,_,pair⟩ := List.mem_map.mp member
    exact equal (congrArg Prod.fst pair)

lemma LocalMonomial.momentumDirections_count (m : LocalMonomial G)
    (i : Fin m.legs.length) (mu : Fin 4) :
    m.momentumDirections.count (i,mu) = (m.jetAt i).2 mu := by
  unfold LocalMonomial.momentumDirections
  simp only [List.count_flatMap,Function.comp_def,count_slotMap,orderedMultiindex_count]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp

/-- The canonical projector differentiates in exactly the original
coordinate directions after the actual slot equivalence, merely reordered. -/
theorem canonicalProjectorDirections_perm (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    (directionMonomial legs directions).momentumDirections.Perm
      (directions.map (fun d => ((canonicalProjectorSlotEquiv legs directions).symm d.1,d.2))) := by
  classical
  let e := canonicalProjectorSlotEquiv legs directions
  apply List.perm_iff_count.mpr
  rintro ⟨i,mu⟩
  rw [LocalMonomial.momentumDirections_count,canonicalProjectorSlotEquiv_jet]
  dsimp only
  have injective : Function.Injective (fun d : Fin legs.length × Fin 4 => (e.symm d.1,d.2)) := by
    intro x y equal
    apply Prod.ext
    · exact e.symm.injective (congrArg Prod.fst equal)
    · exact congrArg (fun z : Fin (directionMonomial legs directions).legs.length × Fin 4 => z.2) equal
  have counted := List.count_map_of_injective directions
    (fun d : Fin legs.length × Fin 4 => (e.symm d.1,d.2)) injective (e i,mu)
  simp only [Equiv.symm_apply_apply] at counted
  rw [counted]
  exact Multiset.coe_count (e i,mu) directions

end YangMills.PerturbativeFlow
