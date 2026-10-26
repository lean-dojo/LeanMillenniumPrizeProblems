import Problems.YangMills.FlowScaleConstancy

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

/-- Strict loop/arity order of the actual perturbative background recursion. -/
def LowerFlowAgreement (A C : FlowFamily G) (loop n : ℕ) (Λ UV : ℝ) : Prop :=
  ∀ l legs q, (l < loop ∨ (l = loop ∧ legs.length < n)) →
    A l Λ UV legs q = C l Λ UV legs q

lemma selectedLegs_length_flow (legs : List (ExternalLeg G))
    (s : Finset (Fin legs.length)) : (selectedLegs legs s).length = s.card := by
  simp [selectedLegs, selectedIndices]

lemma selectedLegs_lengths_partition (legs : List (ExternalLeg G))
    (s : Finset (Fin legs.length)) :
    (selectedLegs legs s).length + (selectedLegs legs (complementIndices legs s)).length =
      legs.length := by
  classical
  simp only [selectedLegs_length_flow, complementIndices]
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  exact Nat.add_sub_of_le (by simpa using Finset.card_le_card (Finset.subset_univ s))

/-- The two-point-free tree condition makes the apparently same-loop
quadratic terms strictly lower in arity. This uses the actual partitions. -/
theorem quadraticSplit_congr_lower {A C : FlowFamily G} (loop l : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (s : Finset (Fin legs.length)) (hle : l ≤ loop)
    (lower : LowerFlowAgreement A C loop legs.length Λ UV)
    (freeA : ∀ legs q, legs.length ≤ 2 → A 0 Λ UV legs q = 0)
    (freeC : ∀ legs q, legs.length ≤ 2 → C 0 Λ UV legs q = 0) :
    quadraticSplit A A loop l Λ UV legs q s = quadraticSplit C C loop l Λ UV legs q s := by
  classical
  have hlen := selectedLegs_lengths_partition legs s
  unfold quadraticSplit
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro N _
  by_cases hl : l < loop ∨ (l = loop ∧ (.inl N :: selectedLegs legs s).length < legs.length)
  · by_cases hr : loop-l < loop ∨
        (loop-l = loop ∧ (.inl M :: selectedLegs legs (complementIndices legs s)).length < legs.length)
    · rw [lower _ _ _ hl, lower _ _ _ hr]
    · have lzero : l = 0 := by omega
      have small : (.inl N :: selectedLegs legs s).length ≤ 2 := by
        simp only [List.length_cons] at hr ⊢
        omega
      simp only [lzero, freeA _ _ small, freeC _ _ small, mul_zero, zero_mul]
  · have rzero : loop-l = 0 := by omega
    have small : (.inl M :: selectedLegs legs (complementIndices legs s)).length ≤ 2 := by
      simp only [List.length_cons] at hl ⊢
      omega
    simp only [rzero, freeA _ _ small, freeC _ _ small, mul_zero]

/-- Equality of strictly lower actual amplitudes implies equality of the
actual nonlinear flow right-hand sides at this loop and arity. -/
theorem backgroundFlowRHS_congr_lower {A C : FlowFamily G} (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (lower : LowerFlowAgreement A C loop legs.length Λ UV)
    (freeA : ∀ legs q, legs.length ≤ 2 → A 0 Λ UV legs q = 0)
    (freeC : ∀ legs q, legs.length ≤ 2 → C 0 Λ UV legs q = 0) :
    backgroundFlowRHS A loop Λ UV legs q = backgroundFlowRHS C loop Λ UV legs q := by
  have lin : linearFlowRHS A loop Λ UV legs q = linearFlowRHS C loop Λ UV legs q := by
    unfold linearFlowRHS
    apply integral_congr_ae
    filter_upwards [] with p
    unfold linearFlowIntegrand
    split_ifs with hz
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro N _
      rw [lower _ _ _ (Or.inl (by omega))]
  have quad : quadraticFlowRHS A A loop Λ UV legs q = quadraticFlowRHS C C loop Λ UV legs q := by
    unfold quadraticFlowRHS
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro s _
    exact quadraticSplit_congr_lower loop l.val Λ UV legs q s (by omega) lower freeA freeC
  simp only [backgroundFlowRHS, lin, quad]

end YangMills.PerturbativeFlow
