import Problems.YangMills.GeneratedMixingMeaning

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Intrinsic filtration of actual finite renormalization mixtures

The least degree modulo identities on smooth connections is stable under
finite linear combinations. Thus the fixed finite mixing table really acts
within each intrinsic filtered slice of the same local observable algebra.
-/
noncomputable section
namespace YangMills
variable {G : CompactSimpleGaugeGroup}

namespace CurvatureJetPolynomial

theorem dimension_smul {d : ℕ} {p : CurvatureJetPolynomial G}
    (h : HasDimensionAtMost d p) (c : ℝ) : HasDimensionAtMost d (c • p) := by
  classical
  intro m hm
  exact h m (Finsupp.support_smul hm)

end CurvatureJetPolynomial

/-- Every intrinsic bound is realized by an invariant polynomial of that
actual degree with exactly the same values on all smooth connections. -/
theorem intrinsicEngineeringDimension_representative
    (p : CurvatureJetPolynomial.invariantAlgebra G) (d : ℕ)
    (bound : intrinsicEngineeringDimension p ≤ d) :
    ∃ q : CurvatureJetPolynomial.invariantAlgebra G,
      CurvatureJetPolynomial.sameOnConnections (q : CurvatureJetPolynomial G) p ∧
      CurvatureJetPolynomial.HasDimensionAtMost d (q : CurvatureJetPolynomial G) := by
  obtain ⟨q, hq, hd⟩ := (intrinsicEngineeringDimension_le_iff p d).mp bound
  refine ⟨q, ?_, hd⟩
  have relation := Quotient.exact hq
  exact fun A x => congrFun (congrFun relation A) x

/-- An actual bounded representative bounds the intrinsic degree. -/
theorem intrinsicEngineeringDimension_le_of_representative
    (p q : CurvatureJetPolynomial.invariantAlgebra G) (d : ℕ)
    (same : CurvatureJetPolynomial.sameOnConnections (q : CurvatureJetPolynomial G) p)
    (bound : CurvatureJetPolynomial.HasDimensionAtMost d (q : CurvatureJetPolynomial G)) :
    intrinsicEngineeringDimension p ≤ d := by
  apply (intrinsicEngineeringDimension_le_iff p d).mpr
  exact ⟨q, Quotient.sound (funext fun A => funext fun x => same A x), bound⟩

theorem intrinsicEngineeringDimension_zero :
    intrinsicEngineeringDimension (0 : CurvatureJetPolynomial.invariantAlgebra G) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply intrinsicEngineeringDimension_le_of_representative 0 0 0
  · intro A x; rfl
  · intro m hm; simp at hm

theorem intrinsicEngineeringDimension_add_le
    (p q : CurvatureJetPolynomial.invariantAlgebra G) (d : ℕ)
    (hp : intrinsicEngineeringDimension p ≤ d) (hq : intrinsicEngineeringDimension q ≤ d) :
    intrinsicEngineeringDimension (p+q) ≤ d := by
  obtain ⟨p', hp', hpd⟩ := intrinsicEngineeringDimension_representative p d hp
  obtain ⟨q', hq', hqd⟩ := intrinsicEngineeringDimension_representative q d hq
  apply intrinsicEngineeringDimension_le_of_representative (p+q) (p'+q') d
  · intro A x
    simpa [CurvatureJetPolynomial.onConnection, CurvatureJetPolynomial.evaluate] using
      congrArg₂ (· + ·) (hp' A x) (hq' A x)
  · exact CurvatureJetPolynomial.dimension_add hpd hqd

theorem intrinsicEngineeringDimension_smul_le
    (p : CurvatureJetPolynomial.invariantAlgebra G) (c : ℝ) (d : ℕ)
    (hp : intrinsicEngineeringDimension p ≤ d) :
    intrinsicEngineeringDimension (c • p) ≤ d := by
  obtain ⟨p', hp', hpd⟩ := intrinsicEngineeringDimension_representative p d hp
  apply intrinsicEngineeringDimension_le_of_representative (c • p) (c • p') d
  · intro A x
    simpa [CurvatureJetPolynomial.onConnection, CurvatureJetPolynomial.evaluate] using
      congrArg (c * ·) (hp' A x)
  · exact CurvatureJetPolynomial.dimension_smul hpd c

theorem intrinsicEngineeringDimension_sum_le {I : Type*} (s : Finset I)
    (f : I → CurvatureJetPolynomial.invariantAlgebra G) (d : ℕ)
    (bound : ∀ i ∈ s, intrinsicEngineeringDimension (f i) ≤ d) :
    intrinsicEngineeringDimension (∑ i ∈ s, f i) ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intrinsicEngineeringDimension_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply intrinsicEngineeringDimension_add_le
    · exact bound i (Finset.mem_insert_self i s)
    · exact ih (fun j hj => bound j (Finset.mem_insert_of_mem hj))

end YangMills
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual generated local mixing insertion stays within the intrinsic
input degree. No new filtration assumption is supplied by a proof author. -/
theorem GeneratedScaleNormalization.mixingLabel_dimension
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (mu : RenormalizationScale) (order loop : ℕ) (p : InvariantInsertionLabel G) :
    intrinsicEngineeringDimension (N.mixingLabel mu order loop p) ≤
      intrinsicEngineeringDimension p := by
  classical
  apply intrinsicEngineeringDimension_sum_le
  intro q hq
  apply intrinsicEngineeringDimension_smul_le
  exact N.mixing.filtered mu.val order loop p q (Finsupp.mem_support_iff.mp hq)

end YangMills.PerturbativeFlow
