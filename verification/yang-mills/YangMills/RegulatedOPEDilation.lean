import YangMills.FixedSystemDilation

noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

lemma extractCoefficient_scaledAmplitude (a : ℝ) (positive : 0 < a) (degree : ℕ)
    (A : OrderedAmplitude G) (m : LocalMonomial G) (q : Fin m.legs.length → Spacetime) :
    extractCoefficient m (fun legs p => (a : ℂ)^((totalDimension legs : ℤ)-degree) * A legs (a • p)) q =
      (a : ℂ)^((m.dimension : ℤ)-degree) * extractCoefficient m A (a • q) := by
  have actual := extractCoefficient_rescaleDegree a positive degree (fun _ _ _ => A) 0 0 0 m q
  change extractCoefficient m (fun legs p => ((a ^ ((totalDimension legs : ℤ)-degree) : ℝ) : ℂ) * A legs (a • p)) q = _ at actual
  simpa only [Complex.ofReal_zpow] using actual

lemma disconnectedFunctional_rescale (a : ℝ) (positive : 0 < a)
    (L : InsertedFlowFamily G) (F : OversubtractedFamily G) (D : ℕ)
    (input : List (PositionedInsertion G)) :
    disconnectedFunctional (rescaleInsertedFlow a L) (rescaleOversubtractions a F) D input =
      rescaleDegree a (positionedInsertionDegreeSum input)
        (disconnectedFunctional L F D (dilateInsertionPoints a input)) := by
  unfold disconnectedFunctional
  rw [singleInsertionProduct_rescale a positive]
  funext loop Λ UV legs q
  simp only [rescaleOversubtractions,rescaleDegree]
  split_ifs <;> ring

set_option linter.constructorNameAsVariable false in
/-- Canonical scaling of the actual all-loop, triangular OPE extraction.
The output projector and every recursively subtracted lower-degree channel
are the fixed ones; no coefficient family is chosen as input. -/
theorem regulatedOPECoefficient_rescale (a : ℝ) (positive : 0 < a)
    (L : InsertedFlowFamily G) (F : OversubtractedFamily G) (mu UV : ℝ)
    (input : InsertionCluster G) (loop : ℕ) (output : LocalMonomial G) :
    regulatedOPECoefficient (rescaleInsertedFlow a L) (rescaleOversubtractions a F)
      mu UV input loop output =
      (a : ℂ)^((output.dimension : ℤ)-positionedInsertionDegreeSum input.insertions) *
        regulatedOPECoefficient L F (a*mu) (a*UV) (dilateInsertionCluster a input) loop output := by
  generalize dimension_eq : output.dimension = degree
  induction degree using Nat.strong_induction_on generalizing loop output with
  | h degree ih =>
      classical
      rw [← dimension_eq]
      have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
      conv_lhs => rw [regulatedOPECoefficient]
      conv_rhs => arg 2; rw [regulatedOPECoefficient]
      by_cases identity_output : output = 0
      · subst output
        simp only [ite_true,LocalMonomial.dimension,Finsupp.sum_zero_index,Int.natCast_zero,
          disconnectedFunctional_rescale a positive,dilateInsertionCluster_insertions,
          rescaleDegree,Complex.ofReal_zpow,totalDimension,List.map_nil,List.sum_nil]
        congr 2
        funext i
        exact Fin.elim0 i
      · simp only [identity_output,ite_false]
        by_cases invalid : ¬ output.Admissible
        · simp only [invalid,not_false_eq_true,ite_true,mul_zero]
        · have admissible : output.Admissible := not_not.mp invalid
          simp only [admissible,not_true_eq_false,ite_false]
          let old : OrderedAmplitude G := fun legs q =>
            disconnectedFunctional L F 0 (dilateInsertionPoints a input.insertions) loop (a*mu) (a*UV) legs q -
              ∑ c ∈ (monomialsBelow G output.dimension).attach, ∑ r ∈ Finset.range (loop+1),
                regulatedOPECoefficient L F (a*mu) (a*UV) (dilateInsertionCluster a input) r c.val *
                  L [⟨c.val,a⁻¹ • input.last.position⟩] (loop-r) (a*mu) (a*UV) legs q
          have remainder :
              (fun legs q =>
                disconnectedFunctional (rescaleInsertedFlow a L) (rescaleOversubtractions a F) 0 input.insertions
                  loop mu UV legs q -
                  ∑ c ∈ (monomialsBelow G output.dimension).attach, ∑ r ∈ Finset.range (loop+1),
                    regulatedOPECoefficient (rescaleInsertedFlow a L) (rescaleOversubtractions a F)
                      mu UV input r c.val * rescaleInsertedFlow a L [⟨c.val,input.last.position⟩]
                        (loop-r) mu UV legs q) =
              (fun legs q => (a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input.insertions) * old legs (a • q)) := by
            funext legs q
            rw [disconnectedFunctional_rescale a positive]
            simp only [rescaleDegree,Complex.ofReal_zpow,old,mul_sub]
            apply congrArg (fun z : ℂ =>
              (a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input.insertions) *
                disconnectedFunctional L F 0 (dilateInsertionPoints a input.insertions)
                  loop (a*mu) (a*UV) legs (a • q) - z)
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro r _
            have smaller := ih c.val.dimension
              (by have lt := dimension_lt_of_mem_monomialsBelow c.property; omega) r c.val rfl
            rw [smaller,rescaleInsertedFlow_single]
            simp only [rescaleDegree,Complex.ofReal_zpow]
            have weight : (a : ℂ)^((c.val.dimension : ℤ)-positionedInsertionDegreeSum input.insertions) *
                (a : ℂ)^((totalDimension legs : ℤ)-c.val.dimension) =
                (a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input.insertions) := by
              rw [← zpow_add₀ nonzero]
              apply congrArg (fun z : ℤ => (a : ℂ)^z)
              omega
            rw [mul_mul_mul_comm,weight]
          rw [remainder,extractCoefficient_scaledAmplitude a positive,smul_zero]
          simp only [old]
          rw [dilateInsertionCluster_insertions]
          rfl

end YangMills.PerturbativeFlow
