import Problems.YangMills.LegendreGradedness

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
variable {G : CompactSimpleGaugeGroup}

/-- External permutation carries each new assignment fibre to the old
fibre while retaining its block label. -/
def blockFibreEquiv {n k : ℕ} (a : Fin n → Fin k) (e : Equiv.Perm (Fin n)) (b : Fin k) :
    {i // i ∈ partitionBlock (a ∘ e) b} ≃ {i // i ∈ partitionBlock a b} where
  toFun i := ⟨e i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp i.property).2⟩⟩
  invFun i := ⟨e.symm i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [Function.comp_apply, e.apply_symm_apply] using (Finset.mem_filter.mp i.property).2⟩⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i.val

theorem blockCard_permutation {n k : ℕ} (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (b : Fin k) :
    (partitionBlock (a ∘ e) b).card = (partitionBlock a b).card := by
  have h := Fintype.card_congr (blockFibreEquiv a e b)
  simpa using h

/-- The actual induced permutation between the SORTED index orders inside
a block. Both enumerations use the old block cardinality, via the proved
cardinality transport; there is no arbitrarily chosen block bijection. -/
def blockIndexPermutation {n k : ℕ} (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (b : Fin k) :
    Equiv.Perm (Fin (partitionBlock a b).card) :=
  ((partitionBlock (a ∘ e) b).orderIsoOfFin (blockCard_permutation a e b)).toEquiv |>.trans
    (blockFibreEquiv a e b) |>.trans
    ((partitionBlock a b).orderIsoOfFin rfl).toEquiv.symm

theorem blockIndexPermutation_spec {n k : ℕ} (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (b : Fin k) (i : Fin (partitionBlock a b).card) :
    (partitionBlock a b).orderEmbOfFin rfl (blockIndexPermutation a e b i) =
      e ((partitionBlock (a ∘ e) b).orderEmbOfFin (blockCard_permutation a e b) i) := by
  let old := (partitionBlock a b).orderIsoOfFin rfl
  let new := (partitionBlock (a ∘ e) b).orderIsoOfFin (blockCard_permutation a e b)
  change (old (old.symm (blockFibreEquiv a e b (new i)))).val = e (new i).val
  rw [OrderIso.apply_symm_apply]
  rfl

/-- Selected ordered legs use exactly mathlib's increasing finite-set
enumeration. This identifies the implementation with the induced block map. -/
theorem selectedLegs_orderEmb (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length)) :
    selectedLegs legs S = List.ofFn (fun i : Fin S.card => legs.get (S.orderEmbOfFin rfl i)) := by
  unfold selectedLegs selectedIndices
  rw [← Finset.listMap_orderEmbOfFin_finRange S rfl, List.map_map, ← List.ofFn_eq_map]
  rfl

theorem selectedMomenta_orderEmb (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length))
    (q : Fin legs.length → Spacetime) (i : Fin (selectedLegs legs S).length) :
    selectedMomenta legs S q i = q (S.orderEmbOfFin (selectedLegs_length legs S).symm i) := by
  simp [selectedMomenta, selectedIndices, Finset.orderEmbOfFin_apply]

end YangMills.LegendreInsertionBridge
