import Problems.YangMills.LegendreOddSign

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.LegendreInsertionBridge
open YangMills.PerturbativeFlow YangMills.Legendre

lemma blockIndexPermutation_invariant_spec {n k : ℕ} (a : Fin n → Fin k)
    (pi : Equiv.Perm (Fin n)) (invariant : a ∘ pi = a) (b : Fin k)
    (i : Fin (partitionBlock a b).card) :
    (partitionBlock a b).orderEmbOfFin rfl (blockIndexPermutation a pi b i) =
      pi ((partitionBlock a b).orderEmbOfFin rfl i) := by
  have actual := blockIndexPermutation_spec a pi b i
  simpa only [invariant] using actual

/-- On permutations that preserve parity and fix every even slot, the
weighted actual sign is the ordinary sign, via the actual sorted odd fibre. -/
theorem oddPermutation_sign_of_fixes_even {n : ℕ} (p : Fin n → Bool)
    (pi : Equiv.Perm (Fin n)) (preserved : ∀ i, p (pi i) = p i)
    (moved_odd : ∀ i, pi i ≠ i → p i = true) :
    (oddPermutation p pi).sign = pi.sign := by
  classical
  let a := parityAssignment p
  let S := partitionBlock a 1
  have invariant : a ∘ pi = a := by
    funext i
    simp only [a,parityAssignment,Function.comp_apply,preserved]
  have membership : ∀ i, pi i ∈ S ↔ i ∈ S := by
    intro i
    simp only [S,partitionBlock,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [show a (pi i) = a i from congrFun invariant i]
  letI : Fintype {x : Fin n // x ∈ S} := Subtype.fintype (fun x => x ∈ S)
  let restricted := pi.subtypePerm membership
  let order := (S.orderIsoOfFin rfl).toEquiv
  have same : oddPermutation p pi = (order.trans restricted).trans order.symm := by
    apply Equiv.ext
    intro i
    apply order.injective
    apply Subtype.ext
    change (partitionBlock a 1).orderEmbOfFin rfl (blockIndexPermutation a pi 1 i) = _
    rw [blockIndexPermutation_invariant_spec a pi invariant 1]
    change pi (S.orderEmbOfFin rfl i) = (order (order.symm (restricted (order i)))).val
    rw [order.apply_symm_apply]
    rfl
  rw [same,Equiv.Perm.sign_trans_trans_symm]
  apply Equiv.Perm.sign_subtypePerm pi membership
  intro i moved
  simp only [S,partitionBlock,Finset.mem_filter,Finset.mem_univ,true_and,a,parityAssignment,moved_odd i moved,ite_true]

/-- Swapping any two distinct odd external slots has sign minus one,
independently of intervening even or odd fields. -/
theorem permutationSign_swap_odd {G : CompactSimpleGaugeGroup} (legs : List (ExternalLeg G))
    (i j : Fin legs.length) (distinct : i ≠ j)
    (odd_i : (legs.get i).parity = true) (odd_j : (legs.get j).parity = true) :
    permutationSign legs (Equiv.swap i j) = -1 := by
  classical
  let p : Fin legs.length → Bool := fun k => (legs.get k).parity
  have preserved : ∀ k, p (Equiv.swap i j k) = p k := by
    intro k
    by_cases ki : k=i
    · subst k
      simp only [Equiv.swap_apply_left,p,odd_i,odd_j]
    · by_cases kj : k=j
      · subst k
        simp only [Equiv.swap_apply_right,p,odd_i,odd_j]
      · rw [Equiv.swap_apply_of_ne_of_ne ki kj]
  have moved_odd : ∀ k, Equiv.swap i j k ≠ k → p k = true := by
    intro k moved
    by_cases ki : k=i
    · simpa only [ki,p] using odd_i
    · by_cases kj : k=j
      · simpa only [kj,p] using odd_j
      · exact False.elim (moved (Equiv.swap_apply_of_ne_of_ne ki kj))
  rw [permutationSign_eq_oddSign,complexPermutationSign,
    oddPermutation_sign_of_fixes_even p _ preserved moved_odd,Equiv.Perm.sign_swap distinct]
  norm_num

end YangMills.LegendreInsertionBridge
