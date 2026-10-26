import Problems.YangMills.PartitionContact
import Problems.YangMills.PerturbativeCoefficientLimits

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Local, same-field contact extensions from the finite-cutoff flow

A contact counterterm is a finite jet map for ONE input block. Its scalar
coefficients depend on the normalization scale and UV cutoff, never on any
spectator position or momentum. For a whole insertion partition, those maps
are multiplied and applied to the SAME lower-arity finite G_0, via actual
proper diagonal test collapse. The UV limit is imposed on this finite-cutoff
sum itself. An arbitrary bulk-compatible reference extension is not used.

This is the local extension interface; construction, source/forest equivalence,
normalization freedom and its compatibility with all Ward identities remain
mathematical obligations. Coefficientwise loop/coupling sums are finite.
-/
noncomputable section
open scoped ContDiff
set_option maxHeartbeats 1200000
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative Filter
variable {G : CompactSimpleGaugeGroup}

def insertionDegreeSum {n : ℕ} (labels : Fin n → LocalMonomial G) : ℕ :=
  ∑ i : Fin n, (labels i).dimension

def insertionLegSum {n : ℕ} (labels : Fin n → LocalMonomial G) : ℕ :=
  ∑ i : Fin n, (labels i).legs.length

/-- Genuine local block counterterms. The type has no spectator arguments.
Singleton blocks are the identity, since L's individual insertion fields have
already been renormalized by the fixed single-insertion normalization. -/
structure LocalContactCounterterms (G : CompactSimpleGaugeGroup) where
  coefficient : ℝ → ℝ → {n : ℕ} → (Fin n → LocalMonomial G) →
    LocalMonomial G → ClusterDerivativeIndex n → ℕ → ℕ → ℂ
  empty : ∀ mu UV labels output w order loop,
    coefficient mu UV (n := 0) labels output w order loop = 0
  singleton : ∀ mu UV (labels : Fin 1 → LocalMonomial G) output w order loop,
    coefficient mu UV labels output w order loop =
      if order = 0 ∧ loop = 0 ∧ output = labels 0 ∧ w = 0 then 1 else 0
  quantum : ∀ mu UV n (labels : Fin n → LocalMonomial G) output w order,
    2 ≤ n → coefficient mu UV labels output w order 0 = 0
  support : ∀ mu UV n (labels : Fin n → LocalMonomial G) output w order loop,
    0 < mu → mu < UV → (∀ i, (labels i).Admissible) →
    coefficient mu UV labels output w order loop ≠ 0 →
      output.Admissible ∧
      output.dimension + clusterDerivativeOrder w + 4 * (n - 1) ≤ insertionDegreeSum labels ∧
      output.ghostNumber = ∑ i : Fin n, (labels i).ghostNumber ∧
      output.parity = decide ((∑ i : Fin n, (labels i).oddMultiplicity) % 2 = 1) ∧
      order + insertionLegSum labels = output.legs.length + 2 * loop
  scale_smooth : ∀ UV n (labels : Fin n → LocalMonomial G) output w order loop,
    ContDiffOn ℝ ∞ (fun mu : ℝ => coefficient mu UV labels output w order loop)
      (Set.Ioo 0 UV)

/-- A fixed finite normal-derivative grid. The total-degree restriction and
zero directions at block centers avoid spurious tangential channels. -/
def partitionNormalDerivativeIndices {n : ℕ} (p : Fin n → Fin n)
    (degree : ℕ) : Finset (Fin n → Fin 4 → Fin (degree + 1)) := by
  classical
  exact Finset.univ.filter fun w =>
    (∑ i : Fin n, ∑ mu : Fin 4, (w i mu).val) ≤ degree ∧
      ∀ i : Fin n, p i = i → ∀ mu : Fin 4, (w i mu).val = 0

def normalDerivativeIndex {n degree : ℕ}
    (w : Fin n → Fin 4 → Fin (degree + 1)) : ClusterDerivativeIndex n :=
  fun i mu => (w i mu).val

/-- One partition's exact coupling/loop Cauchy coefficient. Each block
coefficient sees only that block's input labels and normal derivatives.
The resulting local outputs are inserted through the original L/F engine. -/
def localPartitionPairing (Z : LocalContactCounterterms G)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G)
    (mu Λ UV : ℝ) {n : ℕ} (labels : Fin n → LocalMonomial G)
    (p : Fin n → Fin n) (hp : CanonicalInsertionPartition p)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest n legs) : ℂ := by
  classical
  let degree := insertionDegreeSum labels
  let rows := monomialsBelow G (degree + 1)
  letI : Fintype rows := Finset.fintypeCoeSort rows
  letI : DecidableEq rows := Classical.decEq rows
  exact partitionContactSign p hp labels *
    ∑ outputs : Fin (partitionRootCount p) → rows,
      ∑ w ∈ partitionNormalDerivativeIndices p degree,
        ∑ a : Fin (partitionRootCount p) → Fin (order + 1),
          ∑ b : Fin (partitionRootCount p) → Fin (loop + 1),
            if (∑ i, (a i).val) ≤ order ∧ (∑ i, (b i).val) ≤ loop then
              (∏ i : Fin (partitionRootCount p),
                Z.coefficient mu UV (partitionBlockLabels p labels i) (outputs i).val
                  (partitionBlockDerivatives p (normalDerivativeIndex w) i) (a i).val (b i).val) *
                finiteJointPairing (.disconnected 0) L F
                  (order - ∑ i, (a i).val) (loop - ∑ i, (b i).val) Λ UV
                  (fun i => (outputs i).val) legs
                  (partitionContactTest p hp (normalDerivativeIndex w) legs test)
            else 0

/-- The extension is computed from the finite cutoff expression, including
its identity partition. There is no arbitrary already-extended W_ref term. -/
def locallyRenormalizedJointPairing (Z : LocalContactCounterterms G)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G)
    (mu Λ UV : ℝ) {n : ℕ} (labels : Fin n → LocalMonomial G)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest n legs) : ℂ := by
  classical
  exact ∑ p ∈ canonicalInsertionPartitions n,
    if hp : CanonicalInsertionPartition p then
      localPartitionPairing Z L F mu Λ UV labels p hp order loop legs test
    else 0

/-- Actual all-contact UV removal followed by IR removal. Local counterterms
are independent of Λ, so a different finite prescription cannot be selected
for every IR cutoff. Nonexceptional support is retained at the IR endpoint.
The full Ward/cumulant and power-counting bundles must constrain the same W. -/
structure LocalContactExtensionCompatible (Z : LocalContactCounterterms G)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G)
    (mu : RenormalizationScale) (W : WardContinuumData G) : Prop where
  same_bulk : W.BulkCompatible L F
  ultraviolet : ∀ order loop Λ, 0 < Λ →
    ∀ n (labels : Fin n → LocalMonomial G) legs (test : JointMomentumTest n legs),
      (∀ i, (labels i).Admissible) → HasCompactSupport test →
      Tendsto (fun UV : ℝ => locallyRenormalizedJointPairing Z L F mu.val Λ UV
        labels order loop legs test) atTop
        (nhds (W.ultraviolet (.disconnected 0) order loop Λ labels legs test))
  infrared : ∀ order loop n (labels : Fin n → LocalMonomial G) legs
      (test : JointMomentumTest n legs),
    (∀ i, (labels i).Admissible) → HasCompactSupport test →
    NonexceptionalSupport (.disconnected 0) test →
    Tendsto (fun Λ : ℝ => W.ultraviolet (.disconnected 0) order loop Λ labels legs test)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W.physical (.disconnected 0) order loop labels legs test))

end YangMills.PerturbativeFlow
