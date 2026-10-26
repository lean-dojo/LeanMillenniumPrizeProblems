import YangMills.LegendreSignFactorization
import YangMills.FullBVBridge
import Mathlib.GroupTheory.Perm.Fin

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow

/-- Put j first and retain the increasing order on its complement before
applying the remaining permutation. Unlike swap-based decomposeFin this
matches the actual take/drop recursive Grassmann derivative. -/
def stableInsertPermutation {n : ℕ} (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' j).symm)

@[simp] theorem stableInsertPermutation_zero {n : ℕ} (j : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) : stableInsertPermutation j σ 0 = j := by
  simp [stableInsertPermutation]

@[simp] theorem stableInsertPermutation_succ {n : ℕ} (j : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    stableInsertPermutation j σ i.succ = j.succAbove (σ i) := by
  simp [stableInsertPermutation]

theorem stableInsertPermutation_injective (n : ℕ) :
    Function.Injective (fun x : Fin (n+1) × Equiv.Perm (Fin n) =>
      stableInsertPermutation x.1 x.2) := by
  intro ⟨j, σ⟩ ⟨k, τ⟩ h
  have hj : j = k := by
    simpa only [stableInsertPermutation_zero] using congrArg (fun π => π 0) h
  subst k
  apply congrArg (fun π : Equiv.Perm (Fin n) => (j, π))
  apply Equiv.ext
  intro i
  apply Fin.succAbove_right_injective
  simpa only [stableInsertPermutation_succ] using congrArg (fun π => π i.succ) h

/-- All n! source assignments in the functional derivative are enumerated
once by the first erased index and a permutation of its ordered complement. -/
def stablePermutationEquiv (n : ℕ) :
    (Fin (n+1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective (fun x => stableInsertPermutation x.1 x.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨stableInsertPermutation_injective n, by
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_perm]
        exact (Nat.factorial_succ n).symm⟩)

theorem sum_stableInsertPermutation (n : ℕ) (f : Equiv.Perm (Fin (n+1)) → ℂ) :
    (∑ π, f π) = ∑ j : Fin (n+1), ∑ σ : Equiv.Perm (Fin n),
      f (stableInsertPermutation j σ) := by
  rw [← (stablePermutationEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

open YangMills.LegendreInsertionBridge

def headCrossingCount {n : ℕ} (p : Fin (n+1) → Bool) (j : Fin (n+1)) : ℕ :=
  ∑ i : Fin (n+1), if i < j ∧ p j = true ∧ p i = true then 1 else 0

/-- Exact weighted inversion recursion for the actual head/take/drop
Grassmann derivative. This is equality of counts, not only signs. -/
theorem weightedInversionCount_stableInsert {n : ℕ} (p : Fin (n+1) → Bool)
    (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    weightedInversionCount p (stableInsertPermutation j σ) = headCrossingCount p j +
      weightedInversionCount (fun i => p (j.succAbove i)) σ := by
  have hlt (a b : Fin n) : j.succAbove a < j.succAbove b ↔ a < b :=
    (Fin.strictMono_succAbove j).lt_iff_lt
  have hhead := Fin.sum_univ_succAbove
    (fun i : Fin (n+1) => if i < j ∧ p j = true ∧ p i = true then (1 : ℕ) else 0) j
  simp only [lt_irrefl, false_and, if_false, zero_add] at hhead
  have hz (i : Fin n) : (0 : Fin (n+1)) < i.succ := by
    change 0 < i.val + 1
    omega
  have hn (i : Fin n) : ¬ i.succ < (0 : Fin (n+1)) := by
    change ¬ i.val + 1 < 0
    omega
  unfold weightedInversionCount
  simp only [Fin.sum_univ_succ, stableInsertPermutation_zero, stableInsertPermutation_succ,
    lt_self_iff_false, hz, hn, Fin.succ_lt_succ_iff,
    false_and, true_and, if_false, zero_add, hlt]
  have hs := Equiv.sum_comp σ (fun i : Fin n =>
    if j.succAbove i < j ∧ p j = true ∧ p (j.succAbove i) = true then (1 : ℕ) else 0)
  rw [hs, ← hhead]
  rfl

theorem parityExternalSign_stableInsert {n : ℕ} (p : Fin (n+1) → Bool)
    (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    parityExternalSign p (stableInsertPermutation j σ) =
      (-1 : ℂ)^headCrossingCount p j *
        parityExternalSign (fun i => p (j.succAbove i)) σ := by
  simp only [parityExternalSign, weightedInversionCount_stableInsert, pow_add]

/-- The ordered complement in the permutation decomposition is literally
the take/drop list used by localMonomialDerivative. -/
theorem ofFn_take_drop_succAbove {A : Type*} {n : ℕ} (source : Fin (n+1) → A)
    (j : Fin (n+1)) :
    (List.ofFn source).take j.val ++ (List.ofFn source).drop (j.val+1) =
      List.ofFn (fun i : Fin n => source (j.succAbove i)) := by
  have hmin : min j.val (n+1) = j.val := Nat.min_eq_left (Nat.le_of_lt j.isLt)
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_drop, List.length_ofFn, hmin]
    omega
  · intro i hi hi'
    have hin : i < n := by simpa only [List.length_ofFn] using hi'
    rw [List.getElem_append]
    by_cases hij : i < j.val
    · simp only [List.length_take, List.length_ofFn, hmin, hij, ↓reduceDIte,
        List.getElem_take, List.getElem_ofFn]
      rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hij)]
      rfl
    · simp only [List.length_take, List.length_ofFn, hmin, hij, ↓reduceDIte,
        List.getElem_drop, List.getElem_ofFn]
      rw [Fin.succAbove_of_le_castSucc _ _ (by change j.val ≤ i; omega)]
      congr 1
      apply Fin.ext
      change j.val + 1 + (i-j.val) = i+1
      omega

theorem ofFn_prefix_parity_count {A : Type*} (parity : A → Bool) (n : ℕ)
    (source : Fin n → A) (k : ℕ) :
    (((List.ofFn source).take k).filter parity).length =
      ∑ i : Fin n, if i.val < k ∧ parity (source i) = true then 1 else 0 := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.ofFn_succ, List.take_succ_cons]
      rw [Fin.sum_univ_succ]
      have ht := ih (fun i => source i.succ) k
      cases hp : parity (source 0) <;>
        simp [List.filter, hp, ht, Fin.val_succ, Nat.add_comm]

/-- Head crossing count is literally the prefix odd count in the actual
ordered recursive derivative, including mixed basic/antifield words. -/
theorem headCrossingCount_prefix {A : Type*} {n : ℕ} (source : Fin (n+1) → A)
    (parity : A → Bool) (j : Fin (n+1)) :
    headCrossingCount (fun i => parity (source i)) j =
      if parity (source j) then (((List.ofFn source).take j.val).filter parity).length else 0 := by
  rw [ofFn_prefix_parity_count]
  cases hp : parity (source j) with
  | false =>
    simp only [headCrossingCount, hp, Bool.false_eq_true, and_false, false_and, if_false,
      Finset.sum_const_zero]
  | true =>
    simp only [headCrossingCount, hp, true_and, if_true]
    rfl

end YangMills.IntegratedNormalization
