import Problems.YangMills.LegendreBackgroundBridge

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 300000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

def subsetAssignment {n : ℕ} (S : Finset (Fin n)) : Fin n → Fin 2 :=
  fun i => if i ∈ S then 0 else 1

@[simp] theorem subsetAssignment_zero {n : ℕ} (S : Finset (Fin n)) :
    partitionBlock (subsetAssignment S) 0 = S := by
  ext i
  simp [partitionBlock, subsetAssignment]

@[simp] theorem subsetAssignment_one {n : ℕ} (S : Finset (Fin n)) :
    partitionBlock (subsetAssignment S) 1 = Finset.univ \ S := by
  ext i
  simp [partitionBlock, subsetAssignment]

theorem splitSign_eq_partitionSign (legs : List (ExternalLeg G))
    (S : Finset (Fin legs.length)) :
    splitSign legs S = partitionSign legs (subsetAssignment S) := by
  unfold splitSign splitSignExponent partitionSign
  congr 1
  have to_univ (T : Finset (Fin legs.length)) (f : Fin legs.length → ℕ) :
      (∑ i ∈ T, f i) = ∑ i, if i ∈ T then f i else 0 := by
    symm
    simpa only [Finset.univ_inter] using! Finset.sum_ite_mem Finset.univ T f
  conv_rhs => rw [Finset.sum_comm]
  rw [to_univ S]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · rw [if_pos hi, to_univ (complementIndices legs S)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S <;> simp [complementIndices, subsetAssignment, hi, hj, and_comm]
  · rw [if_neg hi]
    symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ S <;> simp [subsetAssignment, hi, hj, and_comm]


def subsetTransport {m n : ℕ} (e : Fin m ≃ Fin n) (S : Finset (Fin n)) : Finset (Fin m) :=
  S.preimage e e.injective.injOn

theorem subsetAssignment_transport {m n : ℕ} (e : Fin m ≃ Fin n) (S : Finset (Fin n)) :
    subsetAssignment (subsetTransport e S) = subsetAssignment S ∘ e := by
  funext i
  simp [subsetAssignment, subsetTransport]

theorem subsetTransport_complement {m n : ℕ} (e : Fin m ≃ Fin n) (S : Finset (Fin n)) :
    subsetTransport e (Finset.univ \ S) = Finset.univ \ subsetTransport e S := by
  ext i
  simp [subsetTransport]

def subsetTransportEquiv {m n : ℕ} (e : Fin m ≃ Fin n) : Finset (Fin n) ≃ Finset (Fin m) where
  toFun := subsetTransport e
  invFun := subsetTransport e.symm
  left_inv S := by ext i; simp [subsetTransport]
  right_inv S := by ext i; simp [subsetTransport]

theorem amplitude_block_transport (A : OrderedAmplitude G)
    (graded : ∀ legs q (e : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs e) (permutedMomenta legs e q) = permutationSign legs e * A legs q)
    (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k) (q : Fin legs.length → Spacetime) :
    A (selectedLegs (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b))
      (selectedMomenta (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b)
        (permutedMomenta legs e q)) =
      permutationSign (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b) *
        A (selectedLegs legs (partitionBlock a b)) (selectedMomenta legs (partitionBlock a b) q) := by
  calc
    _ = A
      (permutedLegs (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b))
      (permutedMomenta (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b)
        (selectedMomenta legs (partitionBlock a b) q)) :=
      amplitude_congr_legs A (selectedLegs_transport legs e a b) (selectedMomenta_transport legs e a b q)
    _ = _ := graded _ _ _

theorem selectedEvaluation_congr (A : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (S T : Finset (Fin legs.length)) (h : S=T) (q : Fin legs.length → Spacetime) :
    A (selectedLegs legs S) (selectedMomenta legs S q) =
      A (selectedLegs legs T) (selectedMomenta legs T q) := by
  subst T
  rfl

def splitKernelTerm (A B : OrderedAmplitude G) (K : Spacetime → ℂ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (S : Finset (Fin legs.length)) : ℂ :=
  splitSign legs S * A (selectedLegs legs S) (selectedMomenta legs S q) *
    K (selectedMomentum legs S q) *
    B (selectedLegs legs (complementIndices legs S))
      (selectedMomenta legs (complementIndices legs S) q)

theorem splitKernelTerm_transport (A B : OrderedAmplitude G) (K : Spacetime → ℂ)
    (gradeA : ∀ legs q (e : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs e) (permutedMomenta legs e q) = permutationSign legs e * A legs q)
    (gradeB : ∀ legs q (e : Equiv.Perm (Fin legs.length)),
      B (permutedLegs legs e) (permutedMomenta legs e q) = permutationSign legs e * B legs q)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (S : Finset (Fin legs.length)) :
    splitKernelTerm A B K (permutedLegs legs e) (permutedMomenta legs e q)
      (subsetTransport (externalIndexEquiv legs e) S) =
      permutationSign legs e * splitKernelTerm A B K legs q S := by
  have hsign := actual_partition_sign_factorization legs e (subsetAssignment S)
  have ha := amplitude_block_transport A gradeA legs e (subsetAssignment S) 0 q
  have hb := amplitude_block_transport B gradeB legs e (subsetAssignment S) 1 q
  have hp := selectedMomentum_transport legs e (subsetAssignment S) 0 q
  have hz : partitionBlock (subsetAssignment S ∘ externalIndexEquiv legs e) 0 =
      subsetTransport (externalIndexEquiv legs e) S := by
    rw [← subsetAssignment_transport, subsetAssignment_zero]
  have ho : partitionBlock (subsetAssignment S ∘ externalIndexEquiv legs e) 1 =
      complementIndices (permutedLegs legs e) (subsetTransport (externalIndexEquiv legs e) S) := by
    rw [← subsetAssignment_transport, subsetAssignment_one]
    rfl
  rw [selectedEvaluation_congr A _ _ _ hz,
    selectedEvaluation_congr A _ _ _ (subsetAssignment_zero S)] at ha
  rw [selectedEvaluation_congr B _ _ _ ho,
    selectedEvaluation_congr B _ _ _ (subsetAssignment_one S)] at hb
  rw [hz, subsetAssignment_zero] at hp
  simp only [Fin.prod_univ_two] at hsign
  rw [← subsetAssignment_transport, ← splitSign_eq_partitionSign,
    ← splitSign_eq_partitionSign] at hsign
  unfold splitKernelTerm
  rw [ha, hp]
  change _ * _ * _ * B _ _ = _
  rw [hb]
  have hc := congrArg (fun z : ℂ => z *
    A (selectedLegs legs S) (selectedMomenta legs S q) * K (selectedMomentum legs S q) *
    B (selectedLegs legs (complementIndices legs S)) (selectedMomenta legs (complementIndices legs S) q)) hsign
  simp only [complementIndices] at hc ⊢
  linear_combination hc


def splitKernelSum (A B : OrderedAmplitude G) (K : Spacetime → ℂ) : OrderedAmplitude G :=
  fun legs q => ∑ S : Finset (Fin legs.length), splitKernelTerm A B K legs q S

theorem splitKernelSum_graded (A B : OrderedAmplitude G) (K : Spacetime → ℂ)
    (gradeA : ∀ legs q (e : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs e) (permutedMomenta legs e q) = permutationSign legs e * A legs q)
    (gradeB : ∀ legs q (e : Equiv.Perm (Fin legs.length)),
      B (permutedLegs legs e) (permutedMomenta legs e q) = permutationSign legs e * B legs q)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    splitKernelSum A B K (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * splitKernelSum A B K legs q := by
  unfold splitKernelSum
  rw [← (subsetTransportEquiv (externalIndexEquiv legs e)).sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  exact splitKernelTerm_transport A B K gradeA gradeB legs q e S

theorem sum_selectedMomenta (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length))
    (q : Fin legs.length → Spacetime) :
    (∑ i, selectedMomenta legs S q i) = selectedMomentum legs S q := by
  have h := (S.orderIsoOfFin (selectedLegs_length legs S).symm).toEquiv.sum_comp
    (fun i : {i // i ∈ S} => q i.val)
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) q] at h
  simpa only [selectedMomenta_orderEmb, selectedMomentum] using! h

theorem selectedMomentum_complement (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length))
    (q : Fin legs.length → Spacetime) (balanced : BalancedMomenta legs q) :
    -selectedMomentum legs (complementIndices legs S) q = selectedMomentum legs S q := by
  have h := Finset.sum_sdiff (s₁ := S) (s₂ := Finset.univ) (f := q) (Finset.subset_univ S)
  rw [show (∑ i : Fin legs.length, q i) = 0 from balanced] at h
  have hn := eq_neg_of_add_eq_zero_left h
  simp only [selectedMomentum, complementIndices, hn, neg_neg]

end YangMills.LegendreInsertionBridge
