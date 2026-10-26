import YangMills.MomentumConservationProjection
import YangMills.LegendreSplitTransport
import YangMills.IntegratedVacuumSubtraction

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.LegendreInsertionBridge
variable {G : CompactSimpleGaugeGroup}

/-- Restriction to balanced momenta is an actual fixed projection, not a
new freely chosen amplitude extension. -/
def conservingFlowExtension (F : FlowFamily G) : FlowFamily G :=
  fun loop Λ UV labels q => F loop Λ UV labels (conservingMomenta labels q)

theorem linearResponseMomenta_balanced (labels : List (ExternalLeg G))
    (q : Fin labels.length → Spacetime) (hq : BalancedMomenta labels q)
    (M N : BasicField G) (p : Spacetime) :
    BalancedMomenta (.inl M :: .inl N :: labels)
      (prependMomenta (.inl M) p (prependMomenta (.inl N) (-p) q)) := by
  simp only [BalancedMomenta, prependMomenta, List.length_cons, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ]
  change p + (-p + ∑ i, q i) = 0
  rw [hq]
  simp

theorem quadraticResponseMomenta_balanced (labels : List (ExternalLeg G))
    (q : Fin labels.length → Spacetime) (hq : BalancedMomenta labels q)
    (M : BasicField G) (s : Finset (Fin labels.length)) :
    BalancedMomenta (.inl M :: selectedLegs labels (complementIndices labels s))
      (prependMomenta (.inl M) (selectedMomentum labels s q)
        (selectedMomenta labels (complementIndices labels s) q)) := by
  simp only [BalancedMomenta, prependMomenta, List.length_cons, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ]
  change selectedMomentum labels s q +
    (∑ i, selectedMomenta labels (complementIndices labels s) q i) = 0
  rw [sum_selectedMomenta, ← selectedMomentum_complement labels s q hq]
  exact neg_add_cancel _

theorem linearFlowIntegrand_conserving (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (labels : List (ExternalLeg G))
    (q : Fin labels.length → Spacetime) (hq : BalancedMomenta labels q) (p : Spacetime) :
    linearFlowIntegrand (conservingFlowExtension F) loop Λ UV labels q p =
      linearFlowIntegrand F loop Λ UV labels q p := by
  classical
  unfold linearFlowIntegrand
  split_ifs
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro M hM
    apply Finset.sum_congr rfl
    intro N hN
    unfold conservingFlowExtension
    rw [conservingMomenta_of_balanced _ _ (linearResponseMomenta_balanced labels q hq M N p)]

theorem quadraticSplit_conserving (A F : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (labels : List (ExternalLeg G))
    (q : Fin labels.length → Spacetime) (hq : BalancedMomenta labels q)
    (s : Finset (Fin labels.length)) :
    quadraticSplit A (conservingFlowExtension F) loop leftLoop Λ UV labels q s =
      quadraticSplit A F loop leftLoop Λ UV labels q s := by
  unfold quadraticSplit
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro M hM
  apply Finset.sum_congr rfl
  intro N hN
  unfold conservingFlowExtension
  rw [conservingMomenta_of_balanced _ _ (quadraticResponseMomenta_balanced labels q hq M s)]

/-- Every internal response slot is balanced when the external momenta are
balanced. Hence the SAME fixed flow RHS commutes with this restriction. -/
theorem insertionHomogeneousRHS_conserving (A F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (labels : List (ExternalLeg G))
    (q : Fin labels.length → Spacetime) (hq : BalancedMomenta labels q) :
    insertionHomogeneousRHS A (conservingFlowExtension F) loop Λ UV labels q =
      insertionHomogeneousRHS A F loop Λ UV labels q := by
  unfold insertionHomogeneousRHS linearFlowRHS quadraticFlowRHS
  simp_rw [linearFlowIntegrand_conserving F loop Λ UV labels q hq,
    quadraticSplit_conserving A F loop _ Λ UV labels q hq]

end YangMills.IntegratedNormalization
