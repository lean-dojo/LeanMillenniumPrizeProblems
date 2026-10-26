import Problems.YangMills.MultiOperatorProductExpansion

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Transverse scaling at every partial coincidence diagonal

The final insertion is anchored at zero. A collision cluster contracts only
its internal relative positions about one of its members, keeping its center
and all outside insertions fixed. Normalization uses the transverse dimension
4(cardinality-1), not the dimension of the whole configuration space.
These bounds constrain possible local contact extensions. Equivalence to the
full renormalization/contact prescription requires its Ward identities and the
extension/classification theorem; bounds alone are not that prescription.
-/
noncomputable section
open Filter
namespace YangMills.OPE

/-- Coordinates of all n+1 insertions, with the last fixed at zero. -/
def anchoredPosition {n : ℕ} (r : RelativeSpace n) (i : Fin (n + 1)) : Spacetime :=
  if h : i.val < n then r ⟨i.val, h⟩ else 0

@[simp] theorem anchoredPosition_castSucc {n : ℕ} (r : RelativeSpace n) (i : Fin n) :
    anchoredPosition r i.castSucc = r i := by simp [anchoredPosition]

@[simp] theorem anchoredPosition_last {n : ℕ} (r : RelativeSpace n) :
    anchoredPosition r (Fin.last n) = 0 := by simp [anchoredPosition]

/-- Every member subset of size at least two is a possible collision.
If it contains the anchored insertion its center must be that anchor. -/
structure CollisionCluster (n : ℕ) where
  members : Finset (Fin (n + 1))
  center : Fin (n + 1)
  center_mem : center ∈ members
  cardinality : 2 ≤ members.card
  anchored : Fin.last n ∈ members → center = Fin.last n

def clusterScale {n : ℕ} (S : CollisionCluster n) (t : ℝ) (r : RelativeSpace n) : RelativeSpace n :=
  fun i => if i.castSucc ∈ S.members then
    anchoredPosition r S.center + t • (r i - anchoredPosition r S.center) else r i

theorem anchoredPosition_clusterScale {n : ℕ} (S : CollisionCluster n) (t : ℝ)
    (r : RelativeSpace n) (i : Fin (n + 1)) :
    anchoredPosition (clusterScale S t r) i =
      if i ∈ S.members then anchoredPosition r S.center +
        t • (anchoredPosition r i - anchoredPosition r S.center) else anchoredPosition r i := by
  by_cases hi : i.val < n
  · have heq : (⟨i.val, hi⟩ : Fin n).castSucc = i := by ext; rfl
    simp [anchoredPosition, hi, clusterScale, heq]
  · have heq : i = Fin.last n := by ext; simp only [Fin.val_last]; omega
    subst i
    by_cases hm : Fin.last n ∈ S.members
    · simp [hm, S.anchored hm]
    · simp [hm]

@[simp] theorem clusterScale_center {n : ℕ} (S : CollisionCluster n) (t : ℝ)
    (r : RelativeSpace n) :
    anchoredPosition (clusterScale S t r) S.center = anchoredPosition r S.center := by
  rw [anchoredPosition_clusterScale]
  simp [S.center_mem]

theorem clusterScale_mul {n : ℕ} (S : CollisionCluster n) (s t : ℝ)
    (r : RelativeSpace n) : clusterScale S s (clusterScale S t r) = clusterScale S (s * t) r := by
  funext i
  simp only [clusterScale, clusterScale_center]
  split_ifs <;> simp [smul_sub, smul_smul]

@[simp] theorem clusterScale_one {n : ℕ} (S : CollisionCluster n) (r : RelativeSpace n) :
    clusterScale S 1 r = r := by
  funext i
  simp [clusterScale]

def clusterDilation {n : ℕ} (S : CollisionCluster n) (t : ℝ) (ht : t ≠ 0) :
    RelativeSpace n ≃ₗ[ℝ] RelativeSpace n where
  toFun := clusterScale S t
  invFun := clusterScale S t⁻¹
  left_inv := by intro r; rw [clusterScale_mul, inv_mul_cancel₀ ht, clusterScale_one]
  right_inv := by intro r; rw [clusterScale_mul, mul_inv_cancel₀ ht, clusterScale_one]
  map_add' := by
    intro r s
    funext i
    have hp : anchoredPosition (r + s) S.center =
        anchoredPosition r S.center + anchoredPosition s S.center := by
      simp only [anchoredPosition]; split_ifs <;> simp
    simp only [clusterScale, hp, Pi.add_apply]
    split_ifs <;> module
  map_smul' := by
    intro a r
    change clusterScale S t (a • r) = a • clusterScale S t r
    funext i
    have hp : anchoredPosition (a • r) S.center = a • anchoredPosition r S.center := by
      simp only [anchoredPosition]; split_ifs <;> simp
    simp only [clusterScale, hp, Pi.smul_apply]
    split_ifs <;> module

/-- The actual number of collapsed real directions. -/
def CollisionCluster.codimension {n : ℕ} (S : CollisionCluster n) : ℕ :=
  4 * (S.members.card - 1)

def dilateCollisionTest {n : ℕ} (S : CollisionCluster n) (t : ℝ) (f : RelativeTest n) :
    RelativeTest n :=
  if ht : t ≠ 0 then ((t⁻¹ ^ S.codimension : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (clusterDilation S t ht).symm.toContinuousLinearEquiv f
  else 0

/-- Only the selected collision is probed; spectators and distinct outside
insertions have a positive uniform separation from the collapsed center. -/
def OutsideClusterSeparated {n : ℕ} (S : CollisionCluster n) (f : RelativeTest n) : Prop :=
  HasCompactSupport f ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ r ∈ tsupport f,
    (∀ j, j ∉ S.members → ρ ≤ ‖anchoredPosition r S.center - anchoredPosition r j‖) ∧
    (∀ i j, i ∉ S.members → j ∉ S.members → i ≠ j →
      ρ ≤ ‖anchoredPosition r i - anchoredPosition r j‖)

/-- Total collisions have the fixed output degree subtracted. Proper
subclusters use the conservative minimum-intermediate-degree zero bound. -/
def clusterDegree {n : ℕ} (S : CollisionCluster n)
    (inputDegrees : Fin (n + 1) → ℕ) (outputDegree : ℕ) : ℤ :=
  if S.members = Finset.univ then
    (∑ i : Fin (n + 1), (inputDegrees i : ℤ)) - outputDegree
  else ∑ i ∈ S.members, (inputDegrees i : ℤ)

/-- Fixed power counting for contact extensions at every collision stratum.
Tests may cross inner collision diagonals. The +epsilon leaves logarithms
unrestricted; no convergence of an infinite OPE is demanded. -/
def PartialScalingBounds {n : ℕ} (E : MultiDistribution n)
    (inputDegrees : Fin (n + 1) → ℕ) (outputDegree : ℕ) (wardShift : ℤ := 0) : Prop :=
  ∀ S : CollisionCluster n, ∀ f : RelativeTest n, OutsideClusterSeparated S f →
    ∀ δ : ℝ, 0 < δ →
    Tendsto (fun t : ℝ =>
      ((Real.rpow t ((clusterDegree S inputDegrees outputDegree + wardShift : ℤ) + δ) : ℝ) : ℂ) *
        E (dilateCollisionTest S t f))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

end YangMills.OPE
