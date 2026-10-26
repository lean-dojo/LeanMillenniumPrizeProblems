import Problems.YangMills.ConnectedInsertionFlow
import Problems.YangMills.PartialDiagonalContact

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Proper test collapse for arbitrary insertion partitions

Every block is replaced by one local insertion at its least original index.
A fixed finite enumeration supplies the lower-arity position slots. The
collapse copies all external momenta and is a proper linear embedding, so
restriction of a Schwartz test is an actual continuous Schwartz map. Normal
derivatives act before restriction, with the first-centered positive sign.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

abbrev CanonicalInsertionPartition {n : ℕ} (p : Fin n → Fin n) : Prop :=
  ∀ i, p i ≤ i ∧ p (p i) = p i
abbrev PartitionRoot {n : ℕ} (p : Fin n → Fin n) := {i : Fin n // p i = i}
def partitionRootCount {n : ℕ} (p : Fin n → Fin n) : ℕ := Fintype.card (PartitionRoot p)
def partitionRootEnumeration {n : ℕ} (p : Fin n → Fin n) :
    Fin (partitionRootCount p) ≃ PartitionRoot p := (Fintype.equivFin _).symm

def partitionRootCenter {n : ℕ} (p : Fin n → Fin n)
    (b : Fin (partitionRootCount p)) : Fin n := (partitionRootEnumeration p b).val

def partitionBlockIndex {n : ℕ} (p : Fin n → Fin n) (hp : CanonicalInsertionPartition p)
    (i : Fin n) : Fin (partitionRootCount p) :=
  Fintype.equivFin (PartitionRoot p) ⟨p i, (hp i).2⟩

@[simp] theorem partitionBlockIndex_center {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) (b : Fin (partitionRootCount p)) :
    partitionBlockIndex p hp (partitionRootCenter p b) = b := by
  have he : (⟨p (partitionRootCenter p b), (hp (partitionRootCenter p b)).2⟩ : PartitionRoot p) =
      partitionRootEnumeration p b := by
    apply Subtype.ext
    exact (partitionRootEnumeration p b).property
  simp only [partitionBlockIndex, he, partitionRootEnumeration]
  exact (Fintype.equivFin (PartitionRoot p)).apply_symm_apply b

/-- Coordinates of every original block coincide at its selected center. -/
def partitionDiagonalPositions {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) :
    (Fin (partitionRootCount p) → Spacetime) →L[ℝ] (Fin n → Spacetime) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (partitionBlockIndex p hp i)

@[simp] theorem partitionDiagonalPositions_center {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) (x : Fin (partitionRootCount p) → Spacetime)
    (b : Fin (partitionRootCount p)) :
    partitionDiagonalPositions p hp x (partitionRootCenter p b) = x b := by
  simp [partitionDiagonalPositions]

def partitionJointEmbedding {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) (legs : List (ExternalLeg G)) :
    ((Fin (partitionRootCount p) → Spacetime) × (Fin legs.length → Spacetime)) →L[ℝ]
      ((Fin n → Spacetime) × (Fin legs.length → Spacetime)) :=
  (partitionDiagonalPositions p hp).prodMap (ContinuousLinearMap.id ℝ _)

theorem partitionJointEmbedding_norm {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) (legs : List (ExternalLeg G))
    (xq : (Fin (partitionRootCount p) → Spacetime) × (Fin legs.length → Spacetime)) :
    ‖xq‖ ≤ ‖partitionJointEmbedding p hp legs xq‖ := by
  have hx : ‖xq.1‖ ≤ ‖partitionDiagonalPositions p hp xq.1‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro b
    simpa only [partitionDiagonalPositions_center] using
      norm_le_pi_norm (partitionDiagonalPositions p hp xq.1) (partitionRootCenter p b)
  change max ‖xq.1‖ ‖xq.2‖ ≤ max ‖partitionDiagonalPositions p hp xq.1‖ ‖xq.2‖
  exact max_le_max hx le_rfl

def partitionDiagonalRestriction {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) (legs : List (ExternalLeg G)) :
    JointMomentumTest n legs →L[ℂ] JointMomentumTest (partitionRootCount p) legs :=
  SchwartzMap.compCLM ℂ (partitionJointEmbedding p hp legs).hasTemperateGrowth
    ⟨1, 1, by intro xq; simp only [pow_one, one_mul]
              linarith [partitionJointEmbedding_norm p hp legs xq]⟩

abbrev ClusterDerivativeIndex (n : ℕ) := Fin n → Fin 4 → ℕ

def clusterDerivativeOrder {n : ℕ} (w : ClusterDerivativeIndex n) : ℕ :=
  ∑ i : Fin n, ∑ mu : Fin 4, w i mu

def clusterDerivativeDirections {n : ℕ} (w : ClusterDerivativeIndex n) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap fun i => (orderedMultiindex (w i)).map fun mu => (i, mu)

def jointMixedPositionDerivatives {n : ℕ} (legs : List (ExternalLeg G)) :
    List (Fin n × Fin 4) → JointMomentumTest n legs →L[ℂ] JointMomentumTest n legs
  | [] => ContinuousLinearMap.id ℂ _
  | (i, mu) :: rest => (jointPositionDerivative i mu legs).comp
      (jointMixedPositionDerivatives legs rest)

/-- Normal first-centered delta derivatives for a whole partition.
Applications require w=0 at all block centers. -/
def partitionContactTest {n : ℕ} (p : Fin n → Fin n)
    (hp : CanonicalInsertionPartition p) (w : ClusterDerivativeIndex n)
    (legs : List (ExternalLeg G)) :
    JointMomentumTest n legs →L[ℂ] JointMomentumTest (partitionRootCount p) legs :=
  (partitionDiagonalRestriction p hp legs).comp
    (jointMixedPositionDerivatives legs (clusterDerivativeDirections w))

/-- The finite block label list retains the original insertion order. -/
def partitionBlockMembers {n : ℕ} (p : Fin n → Fin n)
    (b : Fin (partitionRootCount p)) : List (Fin n) :=
  selectedIndices (Finset.univ.filter fun i => p i = partitionRootCenter p b)

def partitionBlockLabels {n : ℕ} (p : Fin n → Fin n)
    (labels : Fin n → LocalMonomial G) (b : Fin (partitionRootCount p)) :
    Fin (partitionBlockMembers p b).length → LocalMonomial G :=
  fun i => labels ((partitionBlockMembers p b).get i)

def partitionBlockDerivatives {n : ℕ} (p : Fin n → Fin n)
    (w : ClusterDerivativeIndex n) (b : Fin (partitionRootCount p)) :
    ClusterDerivativeIndex (partitionBlockMembers p b).length :=
  fun i => w ((partitionBlockMembers p b).get i)

/-- Koszul grouping sign for the actual fixed enumeration of block outputs. -/
def partitionContactSign {n : ℕ} (p : Fin n → Fin n) (hp : CanonicalInsertionPartition p)
    (labels : Fin n → LocalMonomial G) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ partitionBlockIndex p hp j < partitionBlockIndex p hp i ∧
      (labels i).parity = true ∧ (labels j).parity = true then 1 else 0)

end YangMills.PerturbativeFlow
