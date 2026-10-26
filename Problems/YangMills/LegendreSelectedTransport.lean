import Problems.YangMills.LegendreBlockTransport
import Problems.YangMills.LegendreSignFactorization

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
variable {G : CompactSimpleGaugeGroup}

def blockFibreTransport {m n k : ℕ} (a : Fin n → Fin k) (e : Fin m ≃ Fin n) (b : Fin k) :
    {i // i ∈ partitionBlock (a ∘ e) b} ≃ {i // i ∈ partitionBlock a b} where
  toFun i := ⟨e i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp i.property).2⟩⟩
  invFun i := ⟨e.symm i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [Function.comp_apply, e.apply_symm_apply] using (Finset.mem_filter.mp i.property).2⟩⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i.val

theorem blockCard_transport {m n k : ℕ} (a : Fin n → Fin k) (e : Fin m ≃ Fin n) (b : Fin k) :
    (partitionBlock (a ∘ e) b).card = (partitionBlock a b).card := by
  have h := Fintype.card_congr (blockFibreTransport a e b)
  simpa using h

def transportedBlockPermutation {m n k l : ℕ} (a : Fin n → Fin k)
    (e : Fin m ≃ Fin n) (b : Fin k) (hl : (partitionBlock a b).card=l) : Equiv.Perm (Fin l) :=
  ((partitionBlock (a ∘ e) b).orderIsoOfFin ((blockCard_transport a e b).trans hl)).toEquiv |>.trans
    (blockFibreTransport a e b) |>.trans
    ((partitionBlock a b).orderIsoOfFin hl).toEquiv.symm

theorem transportedBlockPermutation_spec {m n k l : ℕ} (a : Fin n → Fin k)
    (e : Fin m ≃ Fin n) (b : Fin k) (hl : (partitionBlock a b).card=l) (i : Fin l) :
    (partitionBlock a b).orderEmbOfFin hl (transportedBlockPermutation a e b hl i) =
      e ((partitionBlock (a ∘ e) b).orderEmbOfFin ((blockCard_transport a e b).trans hl) i) := by
  let old := (partitionBlock a b).orderIsoOfFin hl
  let new := (partitionBlock (a ∘ e) b).orderIsoOfFin ((blockCard_transport a e b).trans hl)
  change (old (old.symm (blockFibreTransport a e b (new i)))).val = e (new i).val
  rw [OrderIso.apply_symm_apply]
  rfl

def externalIndexEquiv (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length)) :
    Fin (permutedLegs legs e).length ≃ Fin legs.length :=
  (finCongr (by simp [permutedLegs])).trans e

theorem permutedLegs_get (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    (i : Fin (permutedLegs legs e).length) :
    (permutedLegs legs e).get i = legs.get (externalIndexEquiv legs e i) := by
  simp [permutedLegs, externalIndexEquiv]
  congr 2

theorem permutedMomenta_get (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    (q : Fin legs.length → Spacetime) (i : Fin (permutedLegs legs e).length) :
    permutedMomenta legs e q i = q (externalIndexEquiv legs e i) := rfl

theorem selectedLegs_get (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length))
    (i : Fin (selectedLegs legs S).length) :
    (selectedLegs legs S).get i = legs.get (S.orderEmbOfFin (selectedLegs_length legs S).symm i) := by
  simp [selectedLegs, selectedIndices, Finset.orderEmbOfFin_apply]
  rfl

theorem orderEmb_index_value {n k l : ℕ} (S : Finset (Fin n)) (hk : S.card=k) (hl : S.card=l)
    (i : Fin k) (j : Fin l) (hij : i.val=j.val) :
    S.orderEmbOfFin hk i = S.orderEmbOfFin hl j := by
  simp only [Finset.orderEmbOfFin_apply, Fin.getElem_fin, hij]

def actualBlockPermutation (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k) :
    Equiv.Perm (Fin (selectedLegs legs (partitionBlock a b)).length) :=
  transportedBlockPermutation a (externalIndexEquiv legs e) b (selectedLegs_length legs _).symm


theorem selectedBlock_length (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k) :
    (selectedLegs (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b)).length =
      (selectedLegs legs (partitionBlock a b)).length := by
  rw [selectedLegs_length, selectedLegs_length]
  exact blockCard_transport a (externalIndexEquiv legs e) b

theorem actualBlockPermutation_spec (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k)
    (i : Fin (selectedLegs (permutedLegs legs e)
      (partitionBlock (a ∘ externalIndexEquiv legs e) b)).length) :
    (partitionBlock a b).orderEmbOfFin (selectedLegs_length legs _).symm
      (actualBlockPermutation legs e a b (Fin.cast (selectedBlock_length legs e a b) i)) =
    externalIndexEquiv legs e ((partitionBlock (a ∘ externalIndexEquiv legs e) b).orderEmbOfFin
      (selectedLegs_length (permutedLegs legs e) _).symm i) := by
  rw [actualBlockPermutation, transportedBlockPermutation_spec]
  congr 1

theorem selectedLegs_transport (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k) :
    selectedLegs (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b) =
      permutedLegs (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b) := by
  apply List.ext_get_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa [permutedLegs] using selectedBlock_length legs e a b
  · intro i hi hj
    rw [selectedLegs_get, permutedLegs_get, permutedLegs_get, selectedLegs_get]
    congr 1
    have h := actualBlockPermutation_spec legs e a b ⟨i, hi⟩
    rw [← h]
    congr 1


theorem selectedMomenta_transport (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k)
    (q : Fin legs.length → Spacetime) :
    HEq (selectedMomenta (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b)
      (permutedMomenta legs e q))
      (permutedMomenta (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b)
        (selectedMomenta legs (partitionBlock a b) q)) := by
  apply (Fin.heq_fun_iff (congrArg List.length (selectedLegs_transport legs e a b))).mpr
  intro i
  rw [selectedMomenta_orderEmb, permutedMomenta_get, permutedMomenta_get, selectedMomenta_orderEmb]
  congr 1
  rw [← actualBlockPermutation_spec legs e a b i]
  congr 1

theorem selectedMomentum_transport (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k)
    (q : Fin legs.length → Spacetime) :
    selectedMomentum (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b)
      (permutedMomenta legs e q) = selectedMomentum legs (partitionBlock a b) q := by
  unfold selectedMomentum
  apply Finset.sum_bij (fun i _ => externalIndexEquiv legs e i)
  · intro i hi
    exact (blockFibreTransport a (externalIndexEquiv legs e) b ⟨i, hi⟩).property
  · intro i hi j hj hij
    exact (externalIndexEquiv legs e).injective hij
  · intro j hj
    let i := (blockFibreTransport a (externalIndexEquiv legs e) b).symm ⟨j, hj⟩
    exact ⟨i.val, i.property, by simp [i, blockFibreTransport]⟩
  · intro i hi
    rfl


theorem rootMomenta_transport (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k)
    (roots : Fin k → ExternalLeg G) (q : Fin legs.length → Spacetime) :
    rootMomenta (permutedLegs legs e) (permutedMomenta legs e q)
      (a ∘ externalIndexEquiv legs e) roots = rootMomenta legs q a roots := by
  funext i
  exact selectedMomentum_transport legs e a _ q

theorem meanFieldRoot_block_transport (F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k)
    (q : Fin legs.length → Spacetime) :
    meanFieldRoot F s order loop root
      (selectedLegs (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b))
      (selectedMomenta (permutedLegs legs e) (partitionBlock (a ∘ externalIndexEquiv legs e) b)
        (permutedMomenta legs e q)) =
    permutationSign (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b) *
      meanFieldRoot F s order loop root (selectedLegs legs (partitionBlock a b))
        (selectedMomenta legs (partitionBlock a b) q) := by
  calc
    _ = meanFieldRoot F s order loop root
      (permutedLegs (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b))
      (permutedMomenta (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b)
        (selectedMomenta legs (partitionBlock a b) q)) :=
      amplitude_congr_legs (meanFieldRoot F s order loop root)
        (selectedLegs_transport legs e a b) (selectedMomenta_transport legs e a b q)
    _ = _ := meanFieldRoot_graded F s graded order loop root _ _ _


theorem transportedBlockPermutation_same {n k l : ℕ} (p : Fin n → Bool) (a : Fin n → Fin k)
    (e : Equiv.Perm (Fin n)) (b : Fin k) (hl : (partitionBlock a b).card=l) :
    parityExternalSign (fun i => p ((partitionBlock a b).orderEmbOfFin hl i))
      (transportedBlockPermutation a e b hl) =
    parityExternalSign (fun i => p ((partitionBlock a b).orderEmbOfFin rfl i))
      (blockIndexPermutation a e b) := by
  subst l
  rfl


theorem transportedBlockPermutation_cast {m n k l : ℕ} (h : m=n)
    (a : Fin n → Fin k) (e : Equiv.Perm (Fin n)) (b : Fin k)
    (hl : (partitionBlock a b).card=l) :
    transportedBlockPermutation a ((finCongr h).trans e) b hl =
      transportedBlockPermutation a e b hl := by
  subst m
  rfl

theorem parityGroupingSign_cast {m n k : ℕ} (h : m=n) (p : Fin n → Bool)
    (a : Fin n → Fin k) (e : Equiv.Perm (Fin n)) :
    parityGroupingSign (p ∘ ((finCongr h).trans e)) (a ∘ ((finCongr h).trans e)) =
      parityGroupingSign (p ∘ e) (a ∘ e) := by
  subst m
  rfl

theorem blockPermutationSign (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    {k : ℕ} (a : Fin legs.length → Fin k) (b : Fin k) :
    permutationSign (selectedLegs legs (partitionBlock a b)) (actualBlockPermutation legs e a b) =
      parityExternalSign (fun i => (legs.get ((partitionBlock a b).orderEmbOfFin rfl i)).parity)
        (blockIndexPermutation a e b) := by
  change parityExternalSign (fun i => ((selectedLegs legs (partitionBlock a b)).get i).parity)
    (actualBlockPermutation legs e a b) = _
  simp_rw [selectedLegs_get]
  unfold actualBlockPermutation externalIndexEquiv
  rw [transportedBlockPermutation_cast]
  exact transportedBlockPermutation_same (fun i => (legs.get i).parity) a e b
    (selectedLegs_length legs _).symm

theorem partitionSign_permuted (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length))
    {k : ℕ} (a : Fin legs.length → Fin k) :
    partitionSign (permutedLegs legs e) (a ∘ externalIndexEquiv legs e) =
      parityGroupingSign ((fun i => (legs.get i).parity) ∘ e) (a ∘ e) := by
  change parityGroupingSign (fun i => ((permutedLegs legs e).get i).parity)
    (a ∘ externalIndexEquiv legs e) = _
  simp_rw [permutedLegs_get]
  exact parityGroupingSign_cast (by simp [permutedLegs]) (fun i => (legs.get i).parity) a e

theorem actual_partition_sign_factorization (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) :
    partitionSign (permutedLegs legs e) (a ∘ externalIndexEquiv legs e) *
      (∏ b : Fin k, permutationSign (selectedLegs legs (partitionBlock a b))
        (actualBlockPermutation legs e a b)) =
      permutationSign legs e * partitionSign legs a := by
  rw [partitionSign_permuted]
  simp_rw [blockPermutationSign]
  exact partition_sign_factorization _ a e

end YangMills.LegendreInsertionBridge
