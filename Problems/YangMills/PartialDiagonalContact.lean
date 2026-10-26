import Problems.YangMills.WardContinuum
import Problems.YangMills.ContactTaylorProjection

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Actual partial-diagonal test maps for insertion Ward contacts

For i<j the local field stays at the FIRST point i, point j is deleted, and
all other insertion indices retain their original order. An ordinary
partial_x delta(x_i-x_j), with coefficient at x_i, acts by the POSITIVE
partial_{x_j} derivative of the joint test before diagonal restriction.
External momenta are preserved. No independent contact distribution is
chosen by these maps.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Inverse of the order-preserving enumeration of the surviving indices.
Its value at the deleted index is immaterial and is never used there. -/
def survivingIndex {n : ℕ} (j : Fin (n + 2)) : Fin (n + 2) → Fin (n + 1) :=
  Function.invFun j.succAbove

@[simp] theorem survivingIndex_succAbove {n : ℕ} (j : Fin (n + 2))
    (k : Fin (n + 1)) : survivingIndex j (j.succAbove k) = k :=
  Function.leftInverse_invFun Fin.succAbove_right_injective k

/-- All surviving positions are copied; the removed point j is set to the
first contact position i. This is a proper linear embedding. -/
def pairDiagonalPositions {n : ℕ} (i j : Fin (n + 2)) :
    (Fin (n + 1) → Spacetime) →L[ℝ] (Fin (n + 2) → Spacetime) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj
    (survivingIndex j (if k = j then i else k))

@[simp] theorem pairDiagonalPositions_survivor {n : ℕ} (i j : Fin (n + 2))
    (x : Fin (n + 1) → Spacetime) (k : Fin (n + 1)) :
    pairDiagonalPositions i j x (j.succAbove k) = x k := by
  simp [pairDiagonalPositions, Fin.succAbove_ne]

@[simp] theorem pairDiagonalPositions_contact {n : ℕ} (i j : Fin (n + 2))
    (x : Fin (n + 1) → Spacetime) :
    pairDiagonalPositions i j x j = x (survivingIndex j i) := by
  simp [pairDiagonalPositions]

/-- The diagonal pullback also copies every external momentum. -/
def pairJointEmbedding {n : ℕ} (i j : Fin (n + 2)) (legs : List (ExternalLeg G)) :
    ((Fin (n + 1) → Spacetime) × (Fin legs.length → Spacetime)) →L[ℝ]
      ((Fin (n + 2) → Spacetime) × (Fin legs.length → Spacetime)) :=
  (pairDiagonalPositions i j).prodMap (ContinuousLinearMap.id ℝ _)

theorem pairJointEmbedding_norm {n : ℕ} (i j : Fin (n + 2)) (legs : List (ExternalLeg G))
    (xq : (Fin (n + 1) → Spacetime) × (Fin legs.length → Spacetime)) :
    ‖xq‖ ≤ ‖pairJointEmbedding i j legs xq‖ := by
  have hx : ‖xq.1‖ ≤ ‖pairDiagonalPositions i j xq.1‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro k
    simpa only [pairDiagonalPositions_survivor] using
      norm_le_pi_norm (pairDiagonalPositions i j xq.1) (j.succAbove k)
  change max ‖xq.1‖ ‖xq.2‖ ≤ max ‖pairDiagonalPositions i j xq.1‖ ‖xq.2‖
  exact max_le_max hx le_rfl

def pairDiagonalRestriction {n : ℕ} (i j : Fin (n + 2)) (legs : List (ExternalLeg G)) :
    JointMomentumTest (n + 2) legs →L[ℂ] JointMomentumTest (n + 1) legs :=
  SchwartzMap.compCLM ℂ (pairJointEmbedding i j legs).hasTemperateGrowth
    ⟨1, 1, by
      intro xq
      simp only [pow_one, one_mul]
      linarith [pairJointEmbedding_norm i j legs xq]⟩

/-- Position derivatives hold all other positions and momenta fixed. -/
def jointPositionDerivative {n : ℕ} (j : Fin n) (mu : Fin 4)
    (legs : List (ExternalLeg G)) : JointMomentumTest n legs →L[ℂ] JointMomentumTest n legs :=
  LineDeriv.lineDerivOpCLM (V := (Fin n → Spacetime) × (Fin legs.length → Spacetime)) ℂ (JointMomentumTest n legs) (Pi.single j (Pi.single mu 1), 0)

def jointPositionDerivatives {n : ℕ} (j : Fin n) (legs : List (ExternalLeg G)) :
    List (Fin 4) → JointMomentumTest n legs →L[ℂ] JointMomentumTest n legs
  | [] => ContinuousLinearMap.id ℂ _
  | mu :: rest => (jointPositionDerivative j mu legs).comp
      (jointPositionDerivatives j legs rest)

/-- Fixed first-centered delta derivative action used in the full Ward sum.
There is no (-1)^|w| here: the removed SECOND coordinate is differentiated. -/
def firstPairContactTest {n : ℕ} (i j : Fin (n + 2)) (_h : i < j)
    (w : ContactDerivativeIndex) (legs : List (ExternalLeg G)) :
    JointMomentumTest (n + 2) legs →L[ℂ] JointMomentumTest (n + 1) legs :=
  (pairDiagonalRestriction i j legs).comp
    (jointPositionDerivatives j legs (orderedMultiindex w))

/-- The same output field replaces i; j is removed, and surviving labels
retain their order. No new insertion-field family enters a contact term. -/
def pairMergedLabels {n : ℕ} (labels : Fin (n + 2) → LocalMonomial G)
    (i j : Fin (n + 2)) (_h : i < j) (output : LocalMonomial G) :
    Fin (n + 1) → LocalMonomial G :=
  fun k => if j.succAbove k = i then output else labels (j.succAbove k)

end YangMills.PerturbativeFlow
