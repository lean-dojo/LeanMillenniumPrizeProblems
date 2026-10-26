import Problems.YangMills.OversubtractedFlow

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Products only read amplitudes at their actual two cutoffs. -/
theorem flowProduct_congr_at {A B A' B' : FlowFamily G} {scale UV : ℝ}
    (hA : ∀ r legs q, A r scale UV legs q = A' r scale UV legs q)
    (hB : ∀ r legs q, B r scale UV legs q = B' r scale UV legs q)
    (loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    flowProduct A B loop scale UV legs q = flowProduct A' B' loop scale UV legs q := by
  simp only [flowProduct, amplitudeProduct, hA, hB]

/-- No multiple-insertion values of L enter its product of single insertions. -/
theorem singleInsertionProduct_congr_at {L L' : InsertedFlowFamily G} {scale UV : ℝ}
    (hL : ∀ a r legs q, L [a] r scale UV legs q = L' [a] r scale UV legs q)
    (input : List (PositionedInsertion G)) (loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    singleInsertionProduct L input loop scale UV legs q =
      singleInsertionProduct L' input loop scale UV legs q := by
  induction input generalizing loop legs with
  | nil => rfl
  | cons a rest ih =>
      exact flowProduct_congr_at (hL a) (fun r ls p => ih r ls p) loop legs q

theorem independentContractionRHS_congr_at {A B A' B' : FlowFamily G} {scale UV : ℝ}
    (hA : ∀ r legs q, A r scale UV legs q = A' r scale UV legs q)
    (hB : ∀ r legs q, B r scale UV legs q = B' r scale UV legs q)
    (parity : Bool) (loop : ℕ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    independentContractionRHS parity A B loop scale UV legs q =
      independentContractionRHS parity A' B' loop scale UV legs q := by
  simp only [independentContractionRHS, independentContractionIntegrand, hA, hB]

theorem insertionPairSource_congr_at {L L' : InsertedFlowFamily G} {scale UV : ℝ}
    (hL : ∀ a r legs q, L [a] r scale UV legs q = L' [a] r scale UV legs q)
    (input : List (PositionedInsertion G)) (k l : Fin input.length)
    (loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    insertionPairSource L input k l loop scale UV legs q =
      insertionPairSource L' input k l loop scale UV legs q := by
  unfold insertionPairSource
  apply congrArg (fun z : ℂ => insertionPairSign input k l * z)
  apply flowProduct_congr_at
  · exact fun r ls p => independentContractionRHS_congr_at (hL _) (hL _) _ r ls p
  · exact fun r ls p => singleInsertionProduct_congr_at hL _ r ls p

theorem oversubtractionSource_congr_at {L L' : InsertedFlowFamily G} {scale UV : ℝ}
    (hL : ∀ a r legs q, L [a] r scale UV legs q = L' [a] r scale UV legs q)
    (input : List (PositionedInsertion G)) (loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    oversubtractionSource L input loop scale UV legs q =
      oversubtractionSource L' input loop scale UV legs q := by
  simp only [oversubtractionSource, insertionPairSource_congr_at hL]

theorem disconnectedFunctional_congr_at {L L' : InsertedFlowFamily G}
    {F F' : OversubtractedFamily G} {scale UV : ℝ}
    (hL : ∀ a r legs q, L [a] r scale UV legs q = L' [a] r scale UV legs q)
    (D : ℕ) (input : List (PositionedInsertion G))
    (hF : ∀ r legs q, F D input r scale UV legs q = F' D input r scale UV legs q)
    (loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    disconnectedFunctional L F D input loop scale UV legs q =
      disconnectedFunctional L' F' D input loop scale UV legs q := by
  simp only [disconnectedFunctional, singleInsertionProduct_congr_at hL, hF]

/-- Triangular extraction reads only single L and F on the given nonempty
cluster, at the actual positive readout scale; arbitrary other L values are unused. -/
theorem regulatedOPECoefficient_congr_at {L L' : InsertedFlowFamily G}
    {F F' : OversubtractedFamily G} {mu UV : ℝ}
    (hL : ∀ a r legs q, L [a] r mu UV legs q = L' [a] r mu UV legs q)
    (input : InsertionCluster G)
    (hF : ∀ r legs q, F 0 input.insertions r mu UV legs q =
      F' 0 input.insertions r mu UV legs q)
    (loop : ℕ) (output : LocalMonomial G) :
    regulatedOPECoefficient L F mu UV input loop output =
      regulatedOPECoefficient L' F' mu UV input loop output := by
  generalize hd : output.dimension = degree
  induction degree using Nat.strong_induction_on generalizing loop output with
  | h degree ih =>
      classical
      conv_lhs => rw [regulatedOPECoefficient]
      conv_rhs => rw [regulatedOPECoefficient]
      by_cases hz : output = 0
      · simp only [hz, ite_true, disconnectedFunctional_congr_at hL 0 input.insertions hF]
      · simp only [hz, ite_false]
        by_cases ha : output.Admissible
        · simp only [ha, not_true_eq_false, ite_false]
          apply congrArg (fun A : OrderedAmplitude G => extractCoefficient output A 0)
          funext legs q
          rw [disconnectedFunctional_congr_at hL 0 input.insertions hF]
          apply congrArg (fun z : ℂ => disconnectedFunctional L' F' 0 input.insertions loop mu UV legs q - z)
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro r _
          rw [ih c.val.dimension (by
            have hc := dimension_lt_of_mem_monomialsBelow c.property
            omega) r c.val rfl, hL]
        · simp only [ha, not_false_eq_true, ite_true]

end YangMills.PerturbativeFlow
