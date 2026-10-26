import YangMills.MultiWardRestoration
import YangMills.PartialDiagonalSupport

/-!
# Separated-support consequence of the full contact Ward identity

The full Ward identity is imposed across contact diagonals. This theorem
then removes its actual contact maps only for separated tests. With no
elementary external legs, the free Ward operation is literally zero; the
remaining generated single-insertion Ward sum vanishes. Arbitrary external
gauge/ghost tests are not declared to annihilate Q-images.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem multiWardPairTerm_eq_zero {n : ℕ} (C : ConnectedWardData G)
    (Q2 : ℝ → ContactAnomalyLimit G) (labels : Fin (n + 2) → LocalMonomial G)
    (order loop : ℕ) (legs : List (ExternalLeg G))
    (test : JointMomentumTest (n + 2) legs) (htest : OffInsertionDiagonals test) :
    multiWardPairTerm C Q2 labels order loop legs test = 0 := by
  classical
  simp only [multiWardPairTerm]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with h
  · have hz : ∀ w, firstPairContactTest i j h w legs test = 0 :=
      fun w => firstPairContactTest_eq_zero i j h w legs test htest
    simp [hz]
  · rfl

theorem nonexceptionalSupport_empty_insertions {n : ℕ}
    (test : JointMomentumTest (n + 2) ([] : List (ExternalLeg G))) :
    NonexceptionalSupport .single test := by
  simp only [NonexceptionalSupport, NonexceptionalMomenta]
  intro x hx S hS
  obtain ⟨i, _⟩ := hS
  exact Fin.elim0 i

/-- Actual raw connected Ward identity on invariant-state type tests.
Finite expansion through corrected invariant spectators is the additional
algebraic step needed for InvariantPhysicalNullIdentity. -/
theorem FullMultiWardRestoration.separated_empty_external
    {B : InvariantForm G} {e : ColorFrame B} {L : ℝ → InsertedFlowFamily G}
    {F : ℝ → OversubtractedFamily G} {W : WardContinuumData G} {C : ConnectedWardData G}
    {singleTransport : SameTheoryWardTransportData e L}
    {pairCoeff : ℝ → ContactAnomalyCoefficients G} {Q1 : QuantumWardLimit G}
    {Q2 : ℝ → ContactAnomalyLimit G} {lift : QuantumObservableLift G}
    (h : FullMultiWardRestoration e L F W C singleTransport pairCoeff Q1 Q2 lift)
    (n : ℕ) (labels : Fin (n + 2) → LocalMonomial G) (order loop : ℕ)
    (test : JointMomentumTest (n + 2) ([] : List (ExternalLeg G)))
    (hlabels : ∀ i, (labels i).Admissible) (hcompact : HasCompactSupport test)
    (hseparated : OffInsertionDiagonals test) :
    multiWardSingleTerm C Q1 labels order loop [] test = 0 := by
  have hw := h.multiple n labels order loop [] test hlabels hcompact
    (nonexceptionalSupport_empty_insertions test)
  unfold connectedMultiWardRemainder at hw
  rw [h.same_connected.ward_empty_external, LinearMap.zero_apply,
    multiWardPairTerm_eq_zero C Q2 labels order loop [] test hseparated] at hw
  exact neg_eq_zero.mp (by simpa using hw)

end YangMills.PerturbativeFlow
