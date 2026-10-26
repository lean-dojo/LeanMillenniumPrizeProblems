import Problems.YangMills.LegendreSelectedTransport

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

theorem block_nonempty_transport (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) {k : ℕ} (a : Fin legs.length → Fin k) :
    (∀ b, (partitionBlock (a ∘ externalIndexEquiv legs e) b).Nonempty) ↔
      ∀ b, (partitionBlock a b).Nonempty := by
  simp only [← Finset.card_pos, blockCard_transport]

theorem substitutionSummand_transport (A F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (k : ℕ) (a : Fin legs.length → Fin k)
    (roots : Fin k → ExternalLeg G) (go : Fin (k+1) → Fin (order+1))
    (ho : Fin (k+1) → Fin (loop+1)) :
    substitutionSummand A F s order loop (permutedLegs legs e) (permutedMomenta legs e q)
      k (a ∘ externalIndexEquiv legs e) roots go ho =
    permutationSign legs e * substitutionSummand A F s order loop legs q k a roots go ho := by
  simp only [substitutionSummand, block_nonempty_transport]
  split
  · rw [rootMomenta_transport]
    simp_rw [meanFieldRoot_block_transport F s graded]
    rw [Finset.prod_mul_distrib]
    calc
      _ = (Nat.factorial k : ℂ)⁻¹ *
        (partitionSign (permutedLegs legs e) (a ∘ externalIndexEquiv legs e) *
          ∏ b : Fin k, permutationSign (selectedLegs legs (partitionBlock a b))
            (actualBlockPermutation legs e a b)) *
        A (go 0).val (ho 0).val (rootLegs roots) (rootMomenta legs q a roots) *
        ∏ b : Fin k, meanFieldRoot F s (go b.succ).val (ho b.succ).val (roots b)
          (selectedLegs legs (partitionBlock a b)) (selectedMomenta legs (partitionBlock a b) q) := by ring
      _ = _ := by rw [actual_partition_sign_factorization]; ring
  · simp

/-- Actual external assignment reindexing retains every block label. -/
def assignmentTransport {m n k : ℕ} (e : Fin m ≃ Fin n) :
    (Fin n → Fin k) ≃ (Fin m → Fin k) where
  toFun a := a ∘ e
  invFun a := a ∘ e.symm
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp


/-- A common finite sum for full composition and its lower-order part. -/
def weightedPartitionSum (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (weight : (Fin (k+1) → Fin (order+1)) → ℂ) : ℂ :=
  ∑ a : Fin legs.length → Fin k, ∑ roots : Fin k → ExternalLeg G,
    ∑ go : Fin (k+1) → Fin (order+1), ∑ ho : Fin (k+1) → Fin (loop+1),
      weight go * substitutionSummand A F s order loop legs q k a roots go ho

theorem weightedPartitionSum_transport (A F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (weight : (Fin (k+1) → Fin (order+1)) → ℂ) :
    weightedPartitionSum A F s order loop (permutedLegs legs e) (permutedMomenta legs e q) k weight =
      permutationSign legs e * weightedPartitionSum A F s order loop legs q k weight := by
  unfold weightedPartitionSum
  rw [← (assignmentTransport (k := k) (externalIndexEquiv legs e)).sum_comp]
  simp only [assignmentTransport, Equiv.coe_fn_mk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro roots _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro go _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ho _
  rw [substitutionSummand_transport A F s graded]
  ring

theorem sum_fin_transport {m n : ℕ} (h : m=n) (f g : ℕ → ℂ)
    (agree : ∀ i : Fin m, f i.val = g i.val) :
    (∑ i : Fin m, f i.val) = ∑ i : Fin n, g i.val := by
  subst n
  exact Finset.sum_congr rfl (fun i _ => agree i)

theorem meanFieldCompose_eq_weighted (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    meanFieldCompose A F s order loop legs q =
      ∑ k : Fin (legs.length+1), weightedPartitionSum A F s order loop legs q k.val (fun _ => 1) := by
  simp only [meanFieldCompose, weightedPartitionSum, one_mul]

theorem lowerComposition_eq_weighted (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    lowerComposition A F s order loop legs q =
      ∑ k : Fin (legs.length+1), weightedPartitionSum A F s order loop legs q k.val
        (fun go => if (go 0).val < order then 1 else 0) := by
  simp only [lowerComposition, weightedPartitionSum, ite_mul, one_mul, zero_mul]

theorem meanFieldCompose_graded (A F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    meanFieldCompose A F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * meanFieldCompose A F s order loop legs q := by
  rw [meanFieldCompose_eq_weighted, meanFieldCompose_eq_weighted, Finset.mul_sum]
  refine sum_fin_transport (m := (permutedLegs legs e).length+1) (n := legs.length+1)
    (by simp [permutedLegs])
    (fun k => weightedPartitionSum A F s order loop (permutedLegs legs e)
      (permutedMomenta legs e q) k (fun _ => 1))
    (fun k => permutationSign legs e * weightedPartitionSum A F s order loop legs q k (fun _ => 1)) ?_
  intro k
  exact weightedPartitionSum_transport A F s graded order loop legs q e k.val _


/-- Lower composition is graded even for an arbitrary outer coefficient
family. The outer roots and block labels remain fixed under transport. -/
theorem lowerComposition_graded (A F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    lowerComposition A F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * lowerComposition A F s order loop legs q := by
  rw [lowerComposition_eq_weighted, lowerComposition_eq_weighted, Finset.mul_sum]
  refine sum_fin_transport (m := (permutedLegs legs e).length+1) (n := legs.length+1)
    (by simp [permutedLegs])
    (fun k => weightedPartitionSum A F s order loop (permutedLegs legs e)
      (permutedMomenta legs e q) k (fun go => if (go 0).val < order then 1 else 0))
    (fun k => permutationSign legs e * weightedPartitionSum A F s order loop legs q k (fun go => if (go 0).val < order then 1 else 0)) ?_
  intro k
  exact weightedPartitionSum_transport A F s graded order loop legs q e k.val _

/-- The computed local-insertion inverse has the actual graded symmetry,
from balanced background symmetry and independent-momentum insertion
symmetry. No symmetry assumption on the unknown inverse is required. -/
theorem insertionGammaCoeff_graded (F I : FormalAmplitude G) (s : CutoffScales)
    (backgroundGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (insertionGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      I order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * I order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    insertionGammaCoeff F I s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * insertionGammaCoeff F I s order loop legs q := by
  rw [insertionGammaCoeff_recurrence, insertionGammaCoeff_recurrence,
    insertionGraded, lowerComposition_graded _ F s backgroundGraded]
  ring

/-- All-order deterministic local insertion inversion with source-level
hypotheses only. Both finite graded substitution and the free identity-root
normalization are proved, removing the directional Legendre fidelity guard. -/
theorem insertion_inverse_from_source (F I : FormalAmplitude G) (s : CutoffScales)
    (free : ∀ loop legs q, F 0 loop legs q = 0)
    (backgroundGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (insertionGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      I order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * I order loop legs q) :
    meanFieldCompose (insertionGammaCoeff F I s) F s = I := by
  apply insertion_inverse_of_graded F I s free
  exact insertionGammaCoeff_graded F I s backgroundGraded insertionGraded


/-- Independent-momentum insertion symmetry passes through the actual
real coupling-jet extraction. -/
theorem flowJet_insertion_graded (I : ℝ → FlowFamily G) (s : CutoffScales)
    (graded : ∀ g loop legs q (e : Equiv.Perm (Fin legs.length)),
      I g loop s.infrared s.ultraviolet (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * I g loop s.infrared s.ultraviolet legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    flowJet I s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * flowJet I s order loop legs q := by
  have hf : (fun g : ℝ => I g loop s.infrared s.ultraviolet
      (permutedLegs legs e) (permutedMomenta legs e q)) =
      (fun g : ℝ => permutationSign legs e * I g loop s.infrared s.ultraviolet legs q) :=
    funext (fun g => graded g loop legs q e)
  unfold flowJet
  rw [hf]
  obtain hs | hs := neg_one_pow_eq_or ℂ
    (∑ i : Fin legs.length, ∑ j : Fin legs.length,
      if i<j ∧ e j<e i ∧ (legs.get (e i)).parity=true ∧ (legs.get (e j)).parity=true then 1 else 0)
  · change permutationSign legs e = 1 at hs
    simp [hs]
  · change permutationSign legs e = -1 at hs
    simp [hs, iteratedDeriv_fun_neg]

/-- The CS directional Legendre equation follows from the actual source
flow symmetry and free normalization, at every independent local-insertion
momentum tuple, to all coupling and loop orders. -/
theorem directionalLegendreCompatible_from_source (A I : ℝ → FlowFamily G) (s : CutoffScales)
    (free : ∀ loop legs q, A 0 loop s.infrared s.ultraviolet legs q = 0)
    (backgroundGraded : ∀ g loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      A g loop s.infrared s.ultraviolet (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * A g loop s.infrared s.ultraviolet legs q)
    (insertionGraded : ∀ g loop legs q (e : Equiv.Perm (Fin legs.length)),
      I g loop s.infrared s.ultraviolet (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * I g loop s.infrared s.ultraviolet legs q) :
    DirectionalLegendreCompatible A I s := by
  apply directionalLegendreCompatible_of_graded A I s free
  exact insertionGammaCoeff_graded (flowJet A s) (flowJet I s) s
    (flowJet_graded A s backgroundGraded) (flowJet_insertion_graded I s insertionGraded)

end YangMills.LegendreInsertionBridge
