import Problems.YangMills.CollisionScaling
import Problems.YangMills.WardContinuum

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Partial-collision power counting for the same insertion distributions

All insertion positions and all external momenta remain joint test variables.
Only differences within the selected cluster shrink. The cluster center,
outside positions and momenta are held fixed; the normalized test dilation
uses exactly 4(|S|-1) collapsed real directions. Bounds hold across inner
diagonals and therefore constrain the local extensions, not merely bulk data.
-/
noncomputable section
open Filter
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def scaleInsertionCluster {n : ℕ} (S : OPE.CollisionCluster n) (t : ℝ)
    (x : Fin (n + 1) → Spacetime) : Fin (n + 1) → Spacetime :=
  fun i => if i ∈ S.members then x S.center + t • (x i - x S.center) else x i

@[simp] theorem scaleInsertionCluster_center {n : ℕ} (S : OPE.CollisionCluster n)
    (t : ℝ) (x : Fin (n + 1) → Spacetime) :
    scaleInsertionCluster S t x S.center = x S.center := by
  simp [scaleInsertionCluster]

theorem scaleInsertionCluster_mul {n : ℕ} (S : OPE.CollisionCluster n) (s t : ℝ)
    (x : Fin (n + 1) → Spacetime) :
    scaleInsertionCluster S s (scaleInsertionCluster S t x) = scaleInsertionCluster S (s * t) x := by
  funext i
  simp only [scaleInsertionCluster]
  split_ifs <;> simp [smul_sub, smul_smul]

@[simp] theorem scaleInsertionCluster_one {n : ℕ} (S : OPE.CollisionCluster n)
    (x : Fin (n + 1) → Spacetime) : scaleInsertionCluster S 1 x = x := by
  funext i
  simp [scaleInsertionCluster]

def insertionClusterDilation {n : ℕ} (S : OPE.CollisionCluster n) (t : ℝ) (ht : t ≠ 0) :
    (Fin (n + 1) → Spacetime) ≃ₗ[ℝ] (Fin (n + 1) → Spacetime) where
  toFun := scaleInsertionCluster S t
  invFun := scaleInsertionCluster S t⁻¹
  left_inv := by intro x; rw [scaleInsertionCluster_mul, inv_mul_cancel₀ ht, scaleInsertionCluster_one]
  right_inv := by intro x; rw [scaleInsertionCluster_mul, mul_inv_cancel₀ ht, scaleInsertionCluster_one]
  map_add' := by
    intro x y
    funext i
    simp only [scaleInsertionCluster, Pi.add_apply]
    split_ifs <;> module
  map_smul' := by
    intro a x
    change scaleInsertionCluster S t (a • x) = a • scaleInsertionCluster S t x
    funext i
    simp only [scaleInsertionCluster, Pi.smul_apply]
    split_ifs <;> module

def dilateJointCollisionTest {n : ℕ} (S : OPE.CollisionCluster n) (t : ℝ)
    (legs : List (ExternalLeg G)) (f : JointMomentumTest (n + 1) legs) :
    JointMomentumTest (n + 1) legs :=
  if ht : t ≠ 0 then
    let E := (insertionClusterDilation S t ht).prodCongr
      (LinearEquiv.refl ℝ (Fin legs.length → Spacetime))
    ((t⁻¹ ^ S.codimension : ℝ) : ℂ) •
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm.toContinuousLinearEquiv f
  else 0

/-- Outside insertion points remain uniformly apart from each other and
from the selected cluster center. No inner-coincidence exclusion is imposed. -/
def OutsideJointClusterSeparated {n : ℕ} (S : OPE.CollisionCluster n)
    {legs : List (ExternalLeg G)} (f : JointMomentumTest (n + 1) legs) : Prop :=
  HasCompactSupport f ∧ ∃ rho : ℝ, 0 < rho ∧ ∀ xq ∈ tsupport f,
    (∀ j, j ∉ S.members → rho ≤ ‖xq.1 S.center - xq.1 j‖) ∧
    (∀ i j, i ∉ S.members → j ∉ S.members → i ≠ j → rho ≤ ‖xq.1 i - xq.1 j‖)

/-- Minimum intermediate degree zero gives the conservative cluster bound.
The Ward branch has degree shift +1. Logarithms are allowed by every δ>0. -/
def JointPartialScalingBounds {n : ℕ} {legs : List (ExternalLeg G)}
    (T : JointMomentumDistribution (n + 1) legs)
    (labels : Fin (n + 1) → LocalMonomial G) (wardShift : ℤ := 0) : Prop :=
  ∀ S : OPE.CollisionCluster n, ∀ f : JointMomentumTest (n + 1) legs,
    OutsideJointClusterSeparated S f → NonexceptionalSupport .single f →
    ∀ delta : ℝ, 0 < delta →
    Tendsto (fun t : ℝ =>
      ((Real.rpow t (((∑ i ∈ S.members, ((labels i).dimension : ℤ)) + wardShift : ℤ) + delta) : ℝ) : ℂ) *
        T (dilateJointCollisionTest S t legs f))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

end YangMills.PerturbativeFlow
