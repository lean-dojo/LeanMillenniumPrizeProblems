import Problems.YangMills.MonomialProjectorCoordinates

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.PerturbativeFlow

lemma listGet_fiber_card {α : Type*} [DecidableEq α] (items : List α) (v : α) :
    Fintype.card {i : Fin items.length // items.get i = v} = (items : Multiset α).count v := by
  classical
  rw [Fintype.card_subtype]
  rw [count_eq_sumIndicator]
  have encoded : List.ofFn (fun i : Fin items.length => if items.get i = v then 1 else 0) =
      items.map (fun w => if w = v then 1 else 0) := by
    simpa only [List.ofFn_get] using (List.ofFn_comp' items.get (fun w => if w = v then 1 else 0))
  rw [← encoded,List.sum_ofFn]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]

/-- A permutation of finite lists gives an actual index equivalence even
with repeated generators. Fibres are matched using their proved counts. -/
def jetListIndexEquiv {α : Type*} [DecidableEq α] {items other : List α}
    (permutation : items.Perm other) : Fin items.length ≃ Fin other.length :=
  Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq
    (by rw [listGet_fiber_card,listGet_fiber_card]
        exact congrArg (fun s : Multiset α => s.count v) (Multiset.coe_eq_coe.mpr permutation)))

lemma jetListIndexEquiv_get {α : Type*} [DecidableEq α] {items other : List α}
    (permutation : items.Perm other) (i : Fin items.length) :
    other.get (jetListIndexEquiv permutation i) = items.get i :=
  Equiv.ofFiberEquiv_map _ i

end YangMills.PerturbativeFlow
