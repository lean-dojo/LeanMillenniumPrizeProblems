import Problems.YangMills.ConnectedWardContinuum

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Canonical distributional cumulants on compact tests

Products of local distributions are formed here ONLY on disjoint variable
blocks, via compact-mollifier tensor regularization. The factors evaluated
pointwise are smooth regularizations of actual connected distributions.
Their finite graded cumulant sum is integrated against the original compact
joint test, and its actual epsilon limit must equal the SAME G_0 distribution.
Thus contact extensions of connected and disconnected amplitudes cannot be
chosen independently. No global temperedness or pointwise product of
singular distributions is assumed. Existence/independence of the analytic
regularizer are supporting tensor-product theorems, not asserted here.
-/
noncomputable section
open Filter MeasureTheory
namespace YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

abbrev JointVariableSpace (n m : ℕ) := (Fin n → Spacetime) × (Fin m → Spacetime)

/-- A purely analytic compact approximate identity, with no physical
prediction coefficients. Any such choice has the same tensor-product limit
when the standard local-distribution theorem is established. -/
structure CompactJointMollifier where
  kernel : (n m : ℕ) → SchwartzMap (JointVariableSpace n m) ℂ
  support : ∀ n m, tsupport (kernel n m) ⊆ Metric.closedBall 0 1
  real_nonnegative : ∀ n m x, 0 ≤ (kernel n m x).re ∧ (kernel n m x).im = 0
  mass : ∀ n m, (∫ x, kernel n m x) = 1

/-- Translated/scaled COMPACT Schwartz observation of a local distribution.
The exponent is the actual real dimension 4(n+m) of all block variables. -/
def localizedJointMollifier (R : CompactJointMollifier) (n m : ℕ)
    (epsilon : ℝ) (center : JointVariableSpace n m) :
    SchwartzMap (JointVariableSpace n m) ℂ := by
  classical
  by_cases positive : 0 < epsilon
  · let affine : JointVariableSpace n m → JointVariableSpace n m :=
      fun y => epsilon⁻¹ • (center - y)
    have growth : Function.HasTemperateGrowth affine :=
      (Function.HasTemperateGrowth.const epsilon⁻¹).smul
        ((Function.HasTemperateGrowth.const center).sub
          (ContinuousLinearMap.id ℝ (JointVariableSpace n m)).hasTemperateGrowth)
    have proper : ∃ k C, ∀ y, ‖y‖ ≤ C * (1 + ‖affine y‖) ^ k := by
      refine ⟨1, 1 + ‖center‖ + |epsilon|, ?_⟩
      intro y
      have nonzero : epsilon ≠ 0 := ne_of_gt positive
      have reconstruction : center - epsilon • affine y = y := by
        dsimp [affine]
        rw [smul_smul]
        simp [nonzero]
      have estimate : ‖y‖ ≤ ‖center‖ + |epsilon| * ‖affine y‖ := by
        calc
          ‖y‖ = ‖center - epsilon • affine y‖ := congrArg norm reconstruction.symm
          _ ≤ ‖center‖ + ‖epsilon • affine y‖ := norm_sub_le _ _
          _ = ‖center‖ + |epsilon| * ‖affine y‖ := by rw [norm_smul, Real.norm_eq_abs]
      simp only [pow_one]
      nlinarith [norm_nonneg (affine y), norm_nonneg center,
        mul_nonneg (norm_nonneg center) (norm_nonneg (affine y)), abs_nonneg epsilon]
    exact (((epsilon : ℂ) ^ (4 * (n + m)))⁻¹) •
      (SchwartzMap.compCLM ℂ growth proper (R.kernel n m))
  · exact 0

abbrev ConnectedDistributionHierarchy (G : CompactSimpleGaugeGroup) :=
  ℕ → ℕ → {n : ℕ} → (Fin n → LocalMonomial G) →
    (legs : List (ExternalLeg G)) → JointMomentumDistribution n legs

def cumulantPositionIndices {n : ℕ} (partition : Fin n → Fin n) (root : Fin n) : List (Fin n) :=
  selectedIndices (Finset.univ.filter (fun i => partition i = root))

def cumulantExternalIndices {n : ℕ} (legs : List (ExternalLeg G))
    (assignment : Fin legs.length → Fin n) (root : Fin n) : Finset (Fin legs.length) :=
  Finset.univ.filter (fun i => assignment i = root)

/-- One connected block, smoothed in its own positions AND momenta. No
variables are shared between distinct blocks of the final tensor product. -/
def smoothedConnectedBlock (R : CompactJointMollifier) (H : ConnectedDistributionHierarchy G)
    {n : ℕ} (labels : Fin n → LocalMonomial G) (partition : Fin n → Fin n) (root : Fin n)
    (legs : List (ExternalLeg G)) (assignment : Fin legs.length → Fin n)
    (order loop : ℕ) (epsilon : ℝ) (xq : JointVariableSpace n legs.length) : ℂ :=
  let indices := cumulantPositionIndices partition root
  let external := cumulantExternalIndices legs assignment root
  let blockLegs := selectedLegs legs external
  H order loop (fun i : Fin indices.length => labels (indices.get i)) blockLegs
    (localizedJointMollifier R indices.length blockLegs.length epsilon
      ((fun i : Fin indices.length => xq.1 (indices.get i)), selectedMomenta legs external xq.2))

def cumulantExternalAssignments {n : ℕ} (partition : Fin n → Fin n)
    (legs : List (ExternalLeg G)) : Finset (Fin legs.length → Fin n) := by
  classical
  exact Finset.univ.filter (fun f => ∀ i, partition (f i) = f i)

/-- Nonroots carry zero formal order, so allocation is counted exactly once. -/
def cumulantOrderAllocations {n : ℕ} (partition : Fin n → Fin n) (bound : ℕ) :
    Finset (Fin n → Fin (bound + 1)) := by
  classical
  exact Finset.univ.filter (fun f => ∀ i, partition i ≠ i → (f i).val = 0)

def cumulantAllocationSum {n bound : ℕ} (partition : Fin n → Fin n)
    (allocation : Fin n → Fin (bound + 1)) : ℕ :=
  ∑ i ∈ partitionRoots partition, (allocation i).val

def cumulantInputSign {n : ℕ} (labels : Fin n → LocalMonomial G)
    (partition : Fin n → Fin n) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ partition j < partition i ∧ (labels i).parity = true ∧
      (labels j).parity = true then 1 else 0)

def cumulantExternalSign {n : ℕ} (legs : List (ExternalLeg G))
    (assignment : Fin legs.length → Fin n) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin legs.length, ∑ j : Fin legs.length,
    if i < j ∧ assignment j < assignment i ∧ (legs.get i).parity = true ∧
      (legs.get j).parity = true then 1 else 0)

/-- The complete finite graded moment/cumulant kernel, with all insertion
partitions, external unshuffles, and independent coupling/loop allocations.
The hbar^(n-blocks) shift is the connected normalization from FHH(85). -/
def smoothedCumulantMoment (R : CompactJointMollifier) (H : ConnectedDistributionHierarchy G)
    {n : ℕ} (labels : Fin n → LocalMonomial G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (epsilon : ℝ) (xq : JointVariableSpace n legs.length) : ℂ :=
  ∑ partition ∈ canonicalInsertionPartitions n,
    ∑ assignment ∈ cumulantExternalAssignments partition legs,
      ∑ ga ∈ cumulantOrderAllocations partition order,
        ∑ la ∈ cumulantOrderAllocations partition loop,
          let shift := n - (partitionRoots partition).card
          if cumulantAllocationSum partition ga = order ∧
              cumulantAllocationSum partition la + shift = loop then
            cumulantInputSign labels partition * cumulantExternalSign legs assignment *
              (-1 : ℂ) ^ shift * ∏ root ∈ partitionRoots partition,
                smoothedConnectedBlock R H labels partition root legs assignment
                  (ga root).val (la root).val epsilon xq
          else 0

/-- A canonical tensor-product moment at a fixed UV/IR level. The target is
an already specified same-engine G_0 distribution, not a new free product.
The limit is required on all compact tests in the source nonexceptional
region, INCLUDING tests meeting any insertion diagonal. -/
structure CumulantAtLevel (R : CompactJointMollifier) (H : ConnectedDistributionHierarchy G)
    (target : ConnectedDistributionHierarchy G) : Prop where
  integrable : ∀ {n : ℕ} (labels : Fin n → LocalMonomial G) order loop legs epsilon
      (test : JointMomentumTest n legs), 0 < epsilon → HasCompactSupport test →
      Integrable (fun xq => smoothedCumulantMoment R H labels order loop legs epsilon xq * test xq)
  moment_limit : ∀ {n : ℕ} (labels : Fin n → LocalMonomial G) order loop legs
      (test : JointMomentumTest n legs), HasCompactSupport test →
      NonexceptionalSupport (.disconnected 0) test →
      Tendsto (fun epsilon : ℝ => ∫ xq,
        smoothedCumulantMoment R H labels order loop legs epsilon xq * test xq)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (target order loop labels legs test))

/-- All compact-contact connected/moment compatibility at BOTH limiting
levels. It supplements, rather than replaces, actual finite-flow/bulk limits.
Only standard tensor-product regularization is used; no extra contact values
are supplied independently of C and the already specified W hierarchy. -/
def DistributionalCumulantCompatibility (R : CompactJointMollifier)
    (C : ConnectedWardData G) (W : WardContinuumData G) : Prop :=
  CumulantAtLevel R (C.physical false) (W.physical (.disconnected 0)) ∧
  ∀ Λ : ℝ, 0 < Λ → CumulantAtLevel R
    (fun order loop => C.ultraviolet false order loop Λ)
    (fun order loop => W.ultraviolet (.disconnected 0) order loop Λ)

end YangMills.PerturbativeFlow
