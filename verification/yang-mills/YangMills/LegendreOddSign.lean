import YangMills.LegendreBlockTransport
import Mathlib.GroupTheory.Perm.Fin
/-!
# Weighted Koszul signs as ordinary signs on odd-position subsequences

The restricted permutation is computed from the actual sorted fibres.
Inversion counts are exactly reindexed, not only compared modulo two.
Mathlib's ordinary permutation sign formula then supplies the group-theoretic
meaning of the actual external Koszul sign used by the flow and Legendre map.
-/
noncomputable section
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
variable {G : CompactSimpleGaugeGroup}

def complexPermutationSign {n : ℕ} (e : Equiv.Perm (Fin n)) : ℂ := ((e.sign : ℤ) : ℂ)

theorem complexPermutationSign_product {n : ℕ} (e : Equiv.Perm (Fin n)) :
    complexPermutationSign e = ∏ i, ∏ j ∈ Finset.Ioi i, (if e i<e j then 1 else (-1:ℂ)) := by
  have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) e.sign_eq_prod_prod_Ioi
  push_cast at h
  simpa [complexPermutationSign, apply_ite] using h

def inversionSign {n : ℕ} (e : Equiv.Perm (Fin n)) : ℂ :=
  (-1:ℂ) ^ (∑ i, ∑ j, if i<j ∧ e j<e i then (1:ℕ) else 0)

theorem inversionSign_eq_complexSign {n : ℕ} (e : Equiv.Perm (Fin n)) :
    inversionSign e = complexPermutationSign e := by
  rw [complexPermutationSign_product]
  unfold inversionSign
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [show Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i<j) by ext j; simp]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i<j
  · have hne : e i ≠ e j := by intro h; have := e.injective h; omega
    by_cases hlt : e i<e j
    · have hnot : ¬ e j<e i := by omega
      simp [hij, hlt, hnot]
    · have hgt : e j<e i := by omega
      simp [hij, hlt, hgt]
  · simp [hij]


theorem sum_orderEmb {n k : ℕ} (S : Finset (Fin n)) (h : S.card=k) (f : Fin n → ℕ) :
    (∑ i : Fin k, f (S.orderEmbOfFin h i)) = ∑ i ∈ S, f i := by
  have hh := (S.orderIsoOfFin h).toEquiv.sum_comp (fun i : S => f i.val)
  rw [Finset.univ_eq_attach, Finset.sum_attach] at hh
  simpa only [Finset.coe_orderIsoOfFin_apply] using hh

theorem blockInversionCount {n k : ℕ} (a : Fin n → Fin k) (e : Equiv.Perm (Fin n)) (b : Fin k) :
    (∑ i ∈ partitionBlock (a ∘ e) b, ∑ j ∈ partitionBlock (a ∘ e) b,
      if i<j ∧ e j<e i then (1:ℕ) else 0) =
    (∑ i : Fin (partitionBlock a b).card, ∑ j : Fin (partitionBlock a b).card,
      if i<j ∧ blockIndexPermutation a e b j < blockIndexPermutation a e b i then 1 else 0) := by
  rw [← sum_orderEmb (partitionBlock (a ∘ e) b) (blockCard_permutation a e b)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_orderEmb (partitionBlock (a ∘ e) b) (blockCard_permutation a e b)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 := ((partitionBlock (a ∘ e) b).orderEmbOfFin (blockCard_permutation a e b)).lt_iff_lt (a := i) (b := j)
  have h2 := ((partitionBlock a b).orderEmbOfFin rfl).lt_iff_lt (a := blockIndexPermutation a e b j) (b := blockIndexPermutation a e b i)
  simp only [h1, ← blockIndexPermutation_spec a e b i, ← blockIndexPermutation_spec a e b j, h2]


def parityAssignment {n : ℕ} (p : Fin n → Bool) (i : Fin n) : Fin 2 := if p i=true then 1 else 0

def oddPermutation {n : ℕ} (p : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (partitionBlock (parityAssignment p) 1).card) :=
  blockIndexPermutation (parityAssignment p) e 1

def weightedInversionCount {n : ℕ} (p : Fin n → Bool) (e : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i, ∑ j, if i<j ∧ e j<e i ∧ p (e i)=true ∧ p (e j)=true then 1 else 0

theorem weightedInversionCount_fibre {n : ℕ} (p : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    weightedInversionCount p e =
      ∑ i ∈ partitionBlock (parityAssignment p ∘ e) 1,
        ∑ j ∈ partitionBlock (parityAssignment p ∘ e) 1,
          if i<j ∧ e j<e i then (1:ℕ) else 0 := by
  have hm : ∀ i, (parityAssignment p ∘ e) i = 1 ↔ p (e i)=true := by
    intro i
    by_cases hi : p (e i)=true <;> simp [parityAssignment, Function.comp_apply, hi]
  unfold weightedInversionCount partitionBlock
  simp only [Finset.sum_filter, hm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p (e i)=true
  · simp only [hi, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : p (e j)=true <;> simp [hj]
  · simp [hi]

theorem weightedInversionCount_oddPermutation {n : ℕ} (p : Fin n → Bool)
    (e : Equiv.Perm (Fin n)) :
    weightedInversionCount p e =
      ∑ i, ∑ j, if i<j ∧ oddPermutation p e j < oddPermutation p e i then (1:ℕ) else 0 := by
  rw [weightedInversionCount_fibre, blockInversionCount]
  rfl

/-- The actual weighted Koszul sign is the ordinary sign on the canonical
odd-position subsequence, rather than an unproved parity heuristic. -/
theorem permutationSign_eq_oddSign (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) :
    permutationSign legs e =
      complexPermutationSign (oddPermutation (fun i => (legs.get i).parity) e) := by
  change (-1:ℂ) ^ weightedInversionCount (fun i => (legs.get i).parity) e = _
  rw [weightedInversionCount_oddPermutation]
  exact inversionSign_eq_complexSign _

end YangMills.LegendreInsertionBridge
