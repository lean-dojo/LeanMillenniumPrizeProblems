import Problems.YangMills.LegendreInsertionBridge

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
variable {G : CompactSimpleGaugeGroup}

/-- The unique coupling/loop assignment for the identity mean-field map:
all order belongs to the outer coefficient and every root has order zero. -/
def cornerOrders (order roots : ℕ) : Fin (roots+1) → Fin (order+1) :=
  Fin.cons (Fin.last order) (fun _ => 0)

theorem cornerOrders_sum (order roots : ℕ) :
    (∑ i : Fin (roots+1), (cornerOrders order roots i).val) = order := by
  simp [cornerOrders, Fin.sum_univ_succ]

theorem orders_eq_corner {order roots : ℕ} (v : Fin (roots+1) → Fin (order+1))
    (total : (∑ i, (v i).val) = order) (zero_roots : ∀ b : Fin roots, (v b.succ).val = 0) :
    v = cornerOrders order roots := by
  have houter : (v 0).val = order := by
    simpa [Fin.sum_univ_succ, zero_roots] using total
  funext i
  refine Fin.cases ?_ (fun b => ?_) i
  · apply Fin.ext
    simpa [cornerOrders] using houter
  · apply Fin.ext
    simpa [cornerOrders] using zero_roots b

theorem meanFieldRoot_zero (s : CutoffScales) (order loop : ℕ) (root : ExternalLeg G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    meanFieldRoot (0 : FormalAmplitude G) s order loop root legs q =
      if order = 0 ∧ loop = 0 then identityRoot root legs else 0 := by
  cases root <;> simp [meanFieldRoot]

/-- All coefficient assignments except the unique corner vanish at the
identity map. This is uniform in external arity and retains every loop order. -/
theorem substitutionSummand_zero_off_corner (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (go : Fin (k+1) → Fin (order+1)) (ho : Fin (k+1) → Fin (loop+1))
    (hne : go ≠ cornerOrders order k ∨ ho ≠ cornerOrders loop k) :
    substitutionSummand A 0 s order loop legs q k assignment roots go ho = 0 := by
  unfold substitutionSummand
  split_ifs with h
  · have hex : ∃ b : Fin k, (go b.succ).val ≠ 0 ∨ (ho b.succ).val ≠ 0 := by
      by_contra hn
      push Not at hn
      have hg := orders_eq_corner go h.2.1 (fun b => (hn b).1)
      have hh := orders_eq_corner ho h.2.2 (fun b => (hn b).2)
      exact hne.elim (fun h => h hg) (fun h => h hh)
    obtain ⟨b, hb⟩ := hex
    have hroot : meanFieldRoot (0 : FormalAmplitude G) s (go b.succ).val
        (ho b.succ).val (roots b) (selectedLegs legs (partitionBlock assignment b))
        (selectedMomenta legs (partitionBlock assignment b) q) = 0 := by
      rw [meanFieldRoot_zero]
      rcases hb with hb | hb <;> simp [hb]
    have hz : (∏ b : Fin k,
        meanFieldRoot (0 : FormalAmplitude G) s (go b.succ).val (ho b.succ).val
          (roots b) (selectedLegs legs (partitionBlock assignment b))
          (selectedMomenta legs (partitionBlock assignment b) q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) hroot
    rw [hz, mul_zero]
  · rfl

/-- The actual sixfold sum has exactly one coupling assignment and one loop
assignment at the identity, before ANY singleton/permutation assumption. -/
theorem coefficient_assignments_collapse (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) :
    (∑ go : Fin (k+1) → Fin (order+1), ∑ ho : Fin (k+1) → Fin (loop+1),
      substitutionSummand A 0 s order loop legs q k assignment roots go ho) =
      substitutionSummand A 0 s order loop legs q k assignment roots
        (cornerOrders order k) (cornerOrders loop k) := by
  rw [Finset.sum_eq_single (cornerOrders order k)]
  · rw [Finset.sum_eq_single (cornerOrders loop k)]
    · intro ho _ hne
      exact substitutionSummand_zero_off_corner A s order loop legs q k assignment roots _ ho
        (Or.inr hne)
    · simp
  · intro go _ hne
    apply Finset.sum_eq_zero
    intro ho _
    exact substitutionSummand_zero_off_corner A s order loop legs q k assignment roots go ho
      (Or.inl hne)
  · simp

theorem substitutionSummand_corner (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) :
    substitutionSummand A 0 s order loop legs q k assignment roots
      (cornerOrders order k) (cornerOrders loop k) =
    if ∀ b, (partitionBlock assignment b).Nonempty then
      (Nat.factorial k : ℂ)⁻¹ * partitionSign legs assignment *
        A order loop (rootLegs roots) (rootMomenta legs q assignment roots) *
        ∏ b : Fin k, identityRoot (roots b) (selectedLegs legs (partitionBlock assignment b))
    else 0 := by
  unfold substitutionSummand
  simp only [cornerOrders_sum, and_true]
  simp [cornerOrders, meanFieldRoot_zero]

/-- Fixed coefficientwise identity-root partition summand. -/
def identityPartitionSummand (A : FormalAmplitude G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) : ℂ :=
  if ∀ b, (partitionBlock assignment b).Nonempty then
    (Nat.factorial k : ℂ)⁻¹ * partitionSign legs assignment *
      A order loop (rootLegs roots) (rootMomenta legs q assignment roots) *
      ∏ b : Fin k, identityRoot (roots b) (selectedLegs legs (partitionBlock assignment b))
  else 0

/-- The identity-root normalization problem is coefficientwise: it is the
SAME finite graded partition sum at every coupling and loop order. -/
theorem meanFieldCompose_free_coefficients (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    meanFieldCompose A 0 s order loop legs q =
      ∑ k : Fin (legs.length+1), ∑ assignment : Fin legs.length → Fin k.val,
        ∑ roots : Fin k.val → ExternalLeg G,
          identityPartitionSummand A order loop legs q k.val assignment roots := by
  unfold meanFieldCompose
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.sum_congr rfl
  intro roots _
  rw [coefficient_assignments_collapse, substitutionSummand_corner]
  rfl

theorem selectedLegs_length (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length)) :
    (selectedLegs legs S).length = S.card := by
  simp [selectedLegs, selectedIndices]

theorem nonzero_root_singleton (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (S : Finset (Fin legs.length)) (hn : identityRoot root (selectedLegs legs S) ≠ 0) :
    S.card = 1 := by
  have heq : selectedLegs legs S = [root] := by
    by_contra h
    simp [identityRoot, h] at hn
  have hl := congrArg List.length heq
  simpa [selectedLegs_length] using hl

theorem identity_root_product_bijective (legs : List (ExternalLeg G)) {k : ℕ}
    (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (hn : (∏ b : Fin k, identityRoot (roots b)
      (selectedLegs legs (partitionBlock assignment b))) ≠ 0) :
    Function.Bijective assignment := by
  have hcard : ∀ b, (partitionBlock assignment b).card = 1 := by
    intro b
    apply nonzero_root_singleton (roots b) legs
    exact (Finset.prod_ne_zero_iff.mp hn) b (Finset.mem_univ b)
  constructor
  · intro i j hij
    apply Finset.card_le_one_iff.mp (le_of_eq (hcard (assignment i)))
    · simp [partitionBlock]
    · simp [partitionBlock, hij]
  · intro b
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (partitionBlock assignment b).card by rw [hcard]; decide)
    exact ⟨i, by simpa [partitionBlock] using hi⟩

theorem identity_root_product_arity (legs : List (ExternalLeg G)) {k : ℕ}
    (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (hn : (∏ b : Fin k, identityRoot (roots b)
      (selectedLegs legs (partitionBlock assignment b))) ≠ 0) : k = legs.length := by
  have h := Fintype.card_of_bijective (identity_root_product_bijective legs assignment roots hn)
  simpa using h.symm


theorem identityPartitionSummand_zero_nonbijective (A : FormalAmplitude G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    {k : ℕ} (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (h : ¬ Function.Bijective assignment) :
    identityPartitionSummand A order loop legs q k assignment roots = 0 := by
  have hz : (∏ b : Fin k, identityRoot (roots b)
      (selectedLegs legs (partitionBlock assignment b))) = 0 := by
    by_contra hn
    exact h (identity_root_product_bijective legs assignment roots hn)
  simp [identityPartitionSummand, hz]

theorem identityPartitionSummand_zero_arity (A : FormalAmplitude G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    {k : ℕ} (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (h : k ≠ legs.length) :
    identityPartitionSummand A order loop legs q k assignment roots = 0 := by
  have hz : (∏ b : Fin k, identityRoot (roots b)
      (selectedLegs legs (partitionBlock assignment b))) = 0 := by
    by_contra hn
    exact h (identity_root_product_arity legs assignment roots hn)
  simp [identityPartitionSummand, hz]

/-- All non-full arities vanish. Only permutations of the n external legs
can survive in the ACTUAL sum, uniformly in all coupling and loop orders. -/
theorem meanFieldCompose_free_full_arity (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    meanFieldCompose A 0 s order loop legs q =
      ∑ assignment : Fin legs.length → Fin legs.length,
        ∑ roots : Fin legs.length → ExternalLeg G,
          identityPartitionSummand A order loop legs q legs.length assignment roots := by
  rw [meanFieldCompose_free_coefficients]
  apply Finset.sum_eq_single (Fin.last legs.length)
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro assignment _
    apply Finset.sum_eq_zero
    intro roots _
    apply identityPartitionSummand_zero_arity
    intro h
    exact hk (Fin.ext h)
  · simp

/-- Reindex the surviving assignments by actual permutations. -/
theorem meanFieldCompose_free_permutations (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    meanFieldCompose A 0 s order loop legs q =
      ∑ e : Equiv.Perm (Fin legs.length), ∑ roots : Fin legs.length → ExternalLeg G,
        identityPartitionSummand A order loop legs q legs.length e roots := by
  rw [meanFieldCompose_free_full_arity]
  calc
    _ = ∑ a : Fin legs.length → Fin legs.length with Function.Bijective a,
        ∑ roots : Fin legs.length → ExternalLeg G,
          identityPartitionSummand A order loop legs q legs.length a roots := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro a _ hn
      apply Finset.sum_eq_zero
      intro roots _
      apply identityPartitionSummand_zero_nonbijective
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hn
    _ = _ := Finset.sum_bij
      (fun a h => Equiv.ofBijective a (Finset.mem_filter.mp h).2)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => by injection h)
      (fun e _ => ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.bijective⟩,
        Equiv.coe_fn_injective rfl⟩) (fun _ _ => rfl)

theorem partitionBlock_perm (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) (b : Fin legs.length) :
    partitionBlock e b = {e.symm b} := by
  ext i
  simp only [partitionBlock, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact e.apply_eq_iff_eq_symm_apply

theorem selectedLegs_singleton (legs : List (ExternalLeg G)) (i : Fin legs.length) :
    selectedLegs legs {i} = [legs.get i] := by
  simp [selectedLegs, selectedIndices]

theorem partitionSign_perm (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) :
    partitionSign legs e = permutationSign legs e.symm := by
  unfold partitionSign permutationSign
  congr 1
  let f : Fin legs.length → Fin legs.length → ℕ := fun i j =>
    if i<j ∧ e j<e i ∧ (legs.get i).parity=true ∧ (legs.get j).parity=true then 1 else 0
  change (∑ i, ∑ j, f i j) = _
  calc
    _ = ∑ i, ∑ j, f (e.symm i) j :=
      (e.symm.sum_comp (fun i => ∑ j, f i j)).symm
    _ = ∑ i, ∑ j, f (e.symm i) (e.symm j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (e.symm.sum_comp (fun j => f (e.symm i) j)).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp [f, and_assoc, and_comm, and_left_comm]

end YangMills.LegendreInsertionBridge
