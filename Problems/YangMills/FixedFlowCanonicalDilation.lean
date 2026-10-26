import Problems.YangMills.FixedFlowUniqueness
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative Filter
open scoped Topology
variable {G : CompactSimpleGaugeGroup}

/-- Exact canonical scaling of the same actual background family. -/
theorem CoefficientFlowConditions.canonical_scaling {B : InvariantForm G}
    {e : ColorFrame B} {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A) (a : ℝ) (ha : 0 < a)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (hΛUV : Λ ≤ UV)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    A (a*μ) g loop (a*Λ) (a*UV) legs (a • q) =
      ((a ^ (4-(totalDimension legs : ℤ)) : ℝ) : ℂ) * A μ g loop Λ UV legs q := by
  have h := hA.dimensional_covariance a ha μ g UV hμ hUV loop Λ hΛ hΛUV legs q
  change A μ g loop Λ UV legs q =
    ((a ^ ((totalDimension legs : ℤ)-4) : ℝ) : ℂ) *
      A (a*μ) g loop (a*Λ) (a*UV) legs (a • q) at h
  have weight : ((a ^ (4-(totalDimension legs : ℤ)) : ℝ) : ℂ) *
      ((a ^ ((totalDimension legs : ℤ)-4) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← zpow_add₀ (ne_of_gt ha)]
    simp
  rw [h, ← mul_assoc, weight, one_mul]

/-- The infinitesimal canonical dilation acts on the actual simultaneous
scale/momentum path. Its differentiability follows from proved covariance;
separate differentiability in mu or UV is not silently assumed. -/
theorem CoefficientFlowConditions.canonical_dilation_derivative {B : InvariantForm G}
    {e : ColorFrame B} {scheme : LocalMarginalData G} {A : ScaleCouplingFamily G}
    (hA : CoefficientFlowConditions e scheme A)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (hΛUV : Λ ≤ UV)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    HasDerivAt (fun a : ℝ => A (a*μ) g loop (a*Λ) (a*UV) legs (a • q))
      (((4-(totalDimension legs : ℤ) : ℤ) : ℂ) * A μ g loop Λ UV legs q) 1 := by
  have hd := ((hasDerivAt_zpow (4-(totalDimension legs : ℤ)) (1 : ℝ)
    (Or.inl one_ne_zero)).ofReal_comp).mul_const (A μ g loop Λ UV legs q)
  have hd' : HasDerivAt
      (fun a : ℝ => ((a ^ (4-(totalDimension legs : ℤ)) : ℝ) : ℂ) * A μ g loop Λ UV legs q)
      (((4-(totalDimension legs : ℤ) : ℤ) : ℂ) * A μ g loop Λ UV legs q) 1 := by
    simpa using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
  exact hA.canonical_scaling a ha μ g UV hμ hUV loop Λ hΛ hΛUV legs q

end YangMills.PerturbativeFlow
