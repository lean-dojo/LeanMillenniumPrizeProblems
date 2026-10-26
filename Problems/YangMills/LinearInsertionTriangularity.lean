import Problems.YangMills.FlowTriangularity
import Problems.YangMills.CoordinateJetDeterminacy

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

/-- For the SAME background, the actual linear insertion equation is
strictly triangular in insertion loop/arity. -/
theorem insertionHomogeneousRHS_congr_lower {A F H : FlowFamily G} (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (lower : LowerFlowAgreement F H loop legs.length Λ UV)
    (freeA : ∀ ls p, ls.length ≤ 2 → A 0 Λ UV ls p = 0) :
    insertionHomogeneousRHS A F loop Λ UV legs q =
      insertionHomogeneousRHS A H loop Λ UV legs q := by
  classical
  have lin : linearFlowRHS F loop Λ UV legs q = linearFlowRHS H loop Λ UV legs q := by
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
  have quad : quadraticFlowRHS A F loop Λ UV legs q = quadraticFlowRHS A H loop Λ UV legs q := by
    unfold quadraticFlowRHS
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro s _
    unfold quadraticSplit
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro N _
    by_cases hr : loop-l.val < loop ∨
        (loop-l.val = loop ∧ (.inl M :: selectedLegs legs (complementIndices legs s)).length < legs.length)
    · rw [lower _ _ _ hr]
    · have hlen := selectedLegs_lengths_partition legs s
      have lzero : l.val = 0 := by omega
      have small : (.inl N :: selectedLegs legs s).length ≤ 2 := by
        simp only [List.length_cons] at hr ⊢
        omega
      simp only [lzero, freeA _ _ small, mul_zero, zero_mul]
  simp only [insertionHomogeneousRHS,lin,quad]

end YangMills.PerturbativeFlow
