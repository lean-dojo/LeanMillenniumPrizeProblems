import Problems.YangMills.LegendreOddSign

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
/-!
# Universal Koszul factorization for sorted Legendre blocks

For every parity assignment, block assignment and external permutation,
the new grouping sign times all induced within-block signs equals the global
external sign times the old grouping sign. Sorted fibre permutations are the
actual blockIndexPermutation; no arbitrary block bijection occurs.

The proof reindexes the old pair product, symmetrizes unordered pairs and
checks the two external orders and three block orders. Equal-block inversions
supply precisely the internal signs. Exact weighted inversion counts are then
transported through the actual increasing fibre enumerations and summed.
There is no adjacent-only hypothesis, nonempty-block assumption, or extra
root/field constraint. Conversion to permuted List lengths is left to the
separate actual block/root/momentum transport module.
-/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Legendre YangMills.PerturbativeFlow

/-- Reorganize a product over ordered pairs into products over unordered
pairs, retaining both orientations. Diagonal factors must be one. -/
lemma product_pairs_symmetrize {n : ℕ} (f : Fin n → Fin n → ℂ)
    (diagonal : ∀ i, f i i = 1) :
    (∏ i : Fin n, ∏ j : Fin n, f i j) = ∏ i : Fin n, ∏ j : Fin n, if i < j then f i j * f j i else 1 := by
  have split : (∏ i : Fin n, ∏ j : Fin n, f i j) =
      (∏ i : Fin n, ∏ j : Fin n, if i < j then f i j else 1) *
      (∏ i : Fin n, ∏ j : Fin n, if j < i then f i j else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij, not_lt_of_gt hij]
    · by_cases hji : j < i
      · simp [hij, hji]
      · have heq : i=j := by omega
        subst j
        simp [diagonal]
  rw [split]
  conv_lhs => rhs; rw [Finset.prod_comm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij]

def groupingPair {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k) (i j : Fin n) : ℂ :=
  if i < j ∧ a j < a i ∧ p i=true ∧ p j=true then -1 else 1

def externalPair {n : ℕ} (p : Fin n → Bool) (e : Equiv.Perm (Fin n)) (i j : Fin n) : ℂ :=
  if i < j ∧ e j < e i ∧ p (e i)=true ∧ p (e j)=true then -1 else 1

def internalPair {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (i j : Fin n) : ℂ :=
  if i < j ∧ e j < e i ∧ a (e i)=a (e j) ∧ p (e i)=true ∧ p (e j)=true then -1 else 1

lemma pair_sign_factorization {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i < j) :
    groupingPair (p ∘ e) (a ∘ e) i j * internalPair p a e i j =
      externalPair p e i j * groupingPair p a (e i) (e j) * groupingPair p a (e j) (e i) := by
  have hne : e i ≠ e j := by intro h; exact (ne_of_lt hij) (e.injective h)
  by_cases hp : p (e i)=true <;> by_cases hq : p (e j)=true
  · rcases lt_trichotomy (e i) (e j) with he | he | he
    · have hrev : ¬ e j < e i := not_lt_of_gt he
      simp [groupingPair, externalPair, internalPair, Function.comp_apply, hij, he, hrev, hp, hq]
    · exact False.elim (hne he)
    · have hrev : ¬ e i < e j := not_lt_of_gt he
      rcases lt_trichotomy (a (e i)) (a (e j)) with hb | hb | hb
      · simp [groupingPair, externalPair, internalPair, Function.comp_apply, hij, he, hrev,
          hb, not_lt_of_gt hb, ne_of_lt hb, hp, hq]
      · simp [groupingPair, externalPair, internalPair, Function.comp_apply, hij, he, hrev, hb, hp, hq]
      · simp [groupingPair, externalPair, internalPair, Function.comp_apply, hij, he, hrev,
          hb, not_lt_of_gt hb, ne_of_gt hb, hp, hq]
  · simp [groupingPair, externalPair, internalPair, Function.comp_apply, hp, hq]
  · simp [groupingPair, externalPair, internalPair, Function.comp_apply, hp, hq]
  · simp [groupingPair, externalPair, internalPair, Function.comp_apply, hp, hq]

/-- Universal weighted sign factorization before choosing any fibre
coordinates or field values. No parity-compatible root condition is needed. -/
theorem parity_sign_factorization {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) :
    (∏ i : Fin n, ∏ j : Fin n, groupingPair (p ∘ e) (a ∘ e) i j) *
      (∏ i : Fin n, ∏ j : Fin n, internalPair p a e i j) =
      (∏ i : Fin n, ∏ j : Fin n, externalPair p e i j) * (∏ i : Fin n, ∏ j : Fin n, groupingPair p a i j) := by
  have old_reindex : (∏ i : Fin n, ∏ j : Fin n, groupingPair p a i j) =
      ∏ i : Fin n, ∏ j : Fin n, groupingPair p a (e i) (e j) := by
    rw [← Equiv.prod_comp e (fun i => ∏ j, groupingPair p a i j)]
    apply Finset.prod_congr rfl
    intro i _
    exact (Equiv.prod_comp e (fun j => groupingPair p a (e i) j)).symm
  rw [old_reindex, product_pairs_symmetrize (fun i j => groupingPair p a (e i) (e j))
    (by intro i; simp [groupingPair])]
  have left : (∏ i : Fin n, ∏ j : Fin n, groupingPair (p ∘ e) (a ∘ e) i j) *
      (∏ i : Fin n, ∏ j : Fin n, internalPair p a e i j) =
      ∏ i : Fin n, ∏ j : Fin n, if i < j then externalPair p e i j *
        (groupingPair p a (e i) (e j) * groupingPair p a (e j) (e i)) else 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hij : i < j
    · simpa only [if_pos hij, mul_assoc] using pair_sign_factorization p a e i j hij
    · simp [groupingPair, internalPair, hij]
  rw [left, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i < j
  · simp [hij]
  · simp [hij, externalPair]

def parityGroupingSign {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k) : ℂ :=
  (-1:ℂ) ^ (∑ i, ∑ j, if i < j ∧ a j < a i ∧ p i=true ∧ p j=true then (1:ℕ) else 0)

def parityExternalSign {n : ℕ} (p : Fin n → Bool) (e : Equiv.Perm (Fin n)) : ℂ :=
  (-1:ℂ) ^ weightedInversionCount p e

def parityInternalSign {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) : ℂ :=
  (-1:ℂ) ^ (∑ i, ∑ j, if i < j ∧ e j < e i ∧ a (e i)=a (e j) ∧
    p (e i)=true ∧ p (e j)=true then (1:ℕ) else 0)

lemma parityGroupingSign_product {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k) :
    parityGroupingSign p a = ∏ i : Fin n, ∏ j : Fin n, groupingPair p a i j := by
  unfold parityGroupingSign
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  unfold groupingPair
  split_ifs <;> simp

lemma parityExternalSign_product {n : ℕ} (p : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    parityExternalSign p e = ∏ i : Fin n, ∏ j : Fin n, externalPair p e i j := by
  unfold parityExternalSign weightedInversionCount
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  unfold externalPair
  split_ifs <;> simp

lemma parityInternalSign_product {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) :
    parityInternalSign p a e = ∏ i : Fin n, ∏ j : Fin n, internalPair p a e i j := by
  unfold parityInternalSign
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  unfold internalPair
  split_ifs <;> simp

lemma scalar_parity_factorization {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) :
    parityGroupingSign (p ∘ e) (a ∘ e) * parityInternalSign p a e =
      parityExternalSign p e * parityGroupingSign p a := by
  rw [parityGroupingSign_product, parityInternalSign_product, parityExternalSign_product,
    parityGroupingSign_product]
  exact parity_sign_factorization p a e

lemma weighted_block_count {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (b : Fin k) :
    weightedInversionCount (fun i => p ((partitionBlock a b).orderEmbOfFin rfl i))
      (blockIndexPermutation a e b) =
      ∑ i ∈ partitionBlock (a ∘ e) b, ∑ j ∈ partitionBlock (a ∘ e) b,
        if i < j ∧ e j < e i ∧ p (e i)=true ∧ p (e j)=true then (1:ℕ) else 0 := by
  unfold weightedInversionCount
  symm
  rw [← sum_orderEmb (partitionBlock (a ∘ e) b) (blockCard_permutation a e b)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_orderEmb (partitionBlock (a ∘ e) b) (blockCard_permutation a e b)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 := ((partitionBlock (a ∘ e) b).orderEmbOfFin (blockCard_permutation a e b)).lt_iff_lt (a := i) (b := j)
  have h2 := ((partitionBlock a b).orderEmbOfFin rfl).lt_iff_lt (a := blockIndexPermutation a e b j) (b := blockIndexPermutation a e b i)
  simp only [h1, ← blockIndexPermutation_spec a e b i, ← blockIndexPermutation_spec a e b j, h2]

lemma sum_fibre_pairs {n k : ℕ} (a : Fin n → Fin k) (f : Fin n → Fin n → ℕ) :
    (∑ b : Fin k, ∑ i ∈ partitionBlock a b, ∑ j ∈ partitionBlock a b, f i j) =
      ∑ i : Fin n, ∑ j : Fin n, if a i=a j then f i j else 0 := by
  simp only [partitionBlock, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (a i)]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : a i=a j <;> simp [h, eq_comm]
  · intro b _ hb
    have h : a i ≠ b := Ne.symm hb
    simp [h]
  · simp

lemma sum_weighted_block_count {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) :
    (∑ b : Fin k, weightedInversionCount
      (fun i => p ((partitionBlock a b).orderEmbOfFin rfl i)) (blockIndexPermutation a e b)) =
      ∑ i, ∑ j, if i < j ∧ e j < e i ∧ a (e i)=a (e j) ∧
        p (e i)=true ∧ p (e j)=true then (1:ℕ) else 0 := by
  simp_rw [weighted_block_count]
  rw [sum_fibre_pairs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : a (e i)=a (e j) <;> simp [Function.comp_apply, same]

/-- Universal external/per-block Koszul chain rule in the exact sorted
fibre coordinates used by the Legendre substitution. -/
theorem partition_sign_factorization {n k : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) :
    parityGroupingSign (p ∘ e) (a ∘ e) *
      (∏ b : Fin k, parityExternalSign
        (fun i => p ((partitionBlock a b).orderEmbOfFin rfl i)) (blockIndexPermutation a e b)) =
      parityExternalSign p e * parityGroupingSign p a := by
  have local_product : (∏ b : Fin k, parityExternalSign
        (fun i => p ((partitionBlock a b).orderEmbOfFin rfl i)) (blockIndexPermutation a e b)) =
      parityInternalSign p a e := by
    unfold parityExternalSign parityInternalSign
    rw [Finset.prod_pow_eq_pow_sum, sum_weighted_block_count]
  rw [local_product]
  exact scalar_parity_factorization p a e

/-- The scalar wrapper is literally the grouping sign in meanFieldCompose. -/
theorem parityGroupingSign_actual {G : YangMills.CompactSimpleGaugeGroup}
    (legs : List (ExternalLeg G)) {k : ℕ} (a : Fin legs.length → Fin k) :
    parityGroupingSign (fun i => (legs.get i).parity) a = partitionSign legs a := rfl

/-- The external wrapper is literally the source's graded external sign. -/
theorem parityExternalSign_actual {G : YangMills.CompactSimpleGaugeGroup}
    (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length)) :
    parityExternalSign (fun i => (legs.get i).parity) e = permutationSign legs e := rfl

end YangMills.LegendreInsertionBridge
