import Problems.YangMills.PartialDiagonalContact

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Contact terms vanish on separated invariant-state tests

This is the distributional support step needed when deriving physical exact
state nulls from the full insertion Ward hierarchy. It concerns actual test
maps, not an additional assumption that contact terms can be discarded.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem jointPositionDerivative_tsupport {n : ℕ} (j : Fin n) (mu : Fin 4)
    (legs : List (ExternalLeg G)) (f : JointMomentumTest n legs) :
    tsupport (jointPositionDerivative j mu legs f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  apply hx
  change fderiv ℝ f x (Pi.single j (Pi.single mu 1), 0) = 0
  rw [fderiv_of_notMem_tsupport ℝ h]
  rfl

theorem jointPositionDerivatives_tsupport {n : ℕ} (j : Fin n)
    (legs : List (ExternalLeg G)) (directions : List (Fin 4))
    (f : JointMomentumTest n legs) :
    tsupport (jointPositionDerivatives j legs directions f) ⊆ tsupport f := by
  induction directions with
  | nil => exact Set.Subset.rfl
  | cons mu rest ih =>
    exact (jointPositionDerivative_tsupport j mu legs _).trans ih

/-- The proper embedding is literally on the pair coincidence diagonal. -/
theorem pairJointEmbedding_coincident {n : ℕ} (i j : Fin (n + 2)) (h : i < j)
    (legs : List (ExternalLeg G))
    (xq : (Fin (n + 1) → Spacetime) × (Fin legs.length → Spacetime)) :
    (pairJointEmbedding i j legs xq).1 i = (pairJointEmbedding i j legs xq).1 j := by
  simp [pairJointEmbedding, pairDiagonalPositions, ne_of_lt h]

/-- Every actual first-centered delta derivative vanishes on tests separated
from insertion coincidences, regardless of its order. This justifies dropping
Ward contact terms only in this separated-support situation. -/
theorem firstPairContactTest_eq_zero {n : ℕ} (i j : Fin (n + 2)) (h : i < j)
    (w : ContactDerivativeIndex) (legs : List (ExternalLeg G))
    (f : JointMomentumTest (n + 2) legs) (hf : OffInsertionDiagonals f) :
    firstPairContactTest i j h w legs f = 0 := by
  ext xq
  change (jointPositionDerivatives j legs (orderedMultiindex w) f)
    (pairJointEmbedding i j legs xq) = 0
  by_contra hx
  have hsupport : pairJointEmbedding i j legs xq ∈
      tsupport (jointPositionDerivatives j legs (orderedMultiindex w) f) :=
    subset_tsupport _ hx
  have hsupport' := jointPositionDerivatives_tsupport j legs (orderedMultiindex w) f hsupport
  exact hf _ hsupport' i j (ne_of_lt h) (pairJointEmbedding_coincident i j h legs xq)

end YangMills.PerturbativeFlow
