import YangMills.StressTensor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology
namespace YangMills
namespace ChargeSmearing

/-- Actual inverse dilation on the three spatial coordinates. -/
def halfSpatialCoordinate : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num))⁻¹

@[simp] theorem halfSpatialCoordinate_apply (x : Fin 3 → ℝ) :
    halfSpatialCoordinate x = (1/2 : ℝ) • x := by
  simp [halfSpatialCoordinate,ContinuousLinearEquiv.smulLeft,Units.smul_def]

/-- A concrete change of charge profile. It preserves its value one near
spatial infinity's rescaled origin, but its spatial integral is zero. -/
def zeroMassProfile (s : ChargeSmearing) : ChargeSmearing where
  temporal := s.temporal
  spatial := (1/7 : ℂ) • ((8 : ℂ) • s.spatial -
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ halfSpatialCoordinate s.spatial)
  test R := (1/7 : ℂ) • ((8 : ℂ) • s.test R - s.test (2*R))

@[simp] theorem zeroMassProfile_spatial (s : ChargeSmearing) (x : Fin 3 → ℝ) :
    s.zeroMassProfile.spatial x = (1/7 : ℂ) * (8 * s.spatial x - s.spatial ((1/2 : ℝ) • x)) := by
  simp [zeroMassProfile,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,smul_eq_mul]

@[simp] theorem zeroMassProfile_test (s : ChargeSmearing) (R : ℝ) (x : Spacetime) :
    s.zeroMassProfile.test R x = (1/7 : ℂ) * (8 * s.test R x - s.test (2*R) x) := by
  simp [zeroMassProfile,smul_eq_mul]

theorem Admissible.zeroMassProfile {s : ChargeSmearing} (h : s.Admissible) :
    s.zeroMassProfile.Admissible := by
  refine {
    temporal_real := h.temporal_real
    spatial_real := ?_
    temporal_compact := h.temporal_compact
    spatial_compact := ?_
    unit_integral := h.unit_integral
    equals_one := ?_
    temporal_integrable := h.temporal_integrable
    factorization := ?_
  }
  · intro x
    rw [zeroMassProfile_spatial]
    simp [Complex.mul_im, h.spatial_real]
  · have hc : HasCompactSupport (s.spatial : (Fin 3 → ℝ) → ℂ) := h.spatial_compact
    have hh := hc.comp_homeomorph halfSpatialCoordinate.toHomeomorph
    have h8 : HasCompactSupport (fun x => (8 : ℂ) * s.spatial x) :=
      hc.comp_left (show (8 : ℂ) * 0 = 0 by simp)
    have hd := h8.sub hh
    exact hd.comp_left (show (1/7 : ℂ) * 0 = 0 by simp)
  · intro x hx
    rw [zeroMassProfile_spatial, h.equals_one x hx]
    have halfnorm : ‖(1/2 : ℝ) • x‖ ≤ 1 := by
      rw [norm_smul]
      norm_num
      linarith
    rw [h.equals_one _ halfnorm]
    norm_num
  · intro R hR x
    rw [zeroMassProfile_test, h.factorization R hR,
      h.factorization (2*R) (by positivity)]
    change (1/7 : ℂ) * (8 * (s.temporal (x 0) * s.spatial (fun i => x i.succ/R)) -
      s.temporal (x 0) * s.spatial (fun i => x i.succ/(2*R))) =
      s.temporal (x 0) * s.zeroMassProfile.spatial (fun i => x i.succ/R)
    rw [zeroMassProfile_spatial]
    have args : ((1/2 : ℝ) • (fun i : Fin 3 => x i.succ/R)) =
        (fun i : Fin 3 => x i.succ/(2*R)) := by
      ext i
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [args]
    ring

/-- The cutoff test has its actual three-dimensional volume factor. -/
theorem Admissible.test_integral {s : ChargeSmearing} (h : s.Admissible)
    (R : ℝ) (hR : 0 < R) :
    (∫ x : Spacetime, s.test R x) = (R^3 : ℝ) • (∫ y : Fin 3 → ℝ, s.spatial y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hm := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hp := hm.integral_comp e.measurableEmbedding
    (fun z : ℝ × (Fin 3 → ℝ) => s.temporal z.1 * s.spatial (fun i => z.2 i/R))
  have first : (∫ x : Spacetime, s.test R x) =
      ∫ z : ℝ × (Fin 3 → ℝ), s.temporal z.1 * s.spatial (fun i => z.2 i/R) := by
    convert hp using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [h.factorization R hR]
    rfl
  rw [first]
  change (∫ z : ℝ × (Fin 3 → ℝ), s.temporal z.1 * s.spatial (fun i => z.2 i/R)
    ∂(volume.prod volume)) = _
  rw [integral_prod_mul (s.temporal : ℝ → ℂ)
    (fun y : Fin 3 → ℝ => s.spatial (fun i => y i/R)), h.unit_integral, one_mul]
  have hs := Measure.integral_comp_inv_smul_of_nonneg volume
    (s.spatial : (Fin 3 → ℝ) → ℂ) hR.le
  change (∫ x : Fin 3 → ℝ, s.spatial (fun i => R⁻¹ * x i)) = _ at hs
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs

theorem zeroMassProfile_spatial_integral (s : ChargeSmearing) :
    (∫ x : Fin 3 → ℝ, s.zeroMassProfile.spatial x) = 0 := by
  have hc := s.spatial.integrable (μ := volume)
  have hh := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ halfSpatialCoordinate s.spatial).integrable (μ := volume)
  have haar := Measure.integral_comp_inv_smul_of_nonneg volume
    (s.spatial : (Fin 3 → ℝ) → ℂ) (show (0 : ℝ) ≤ 2 by norm_num)
  have hhalf : (∫ x : Fin 3 → ℝ, s.spatial ((1/2 : ℝ) • x)) =
      (8 : ℂ) * ∫ x : Fin 3 → ℝ, s.spatial x := by
    norm_num [smul_eq_mul] at haar
    exact haar
  have hh' : Integrable (fun x : Fin 3 → ℝ => s.spatial ((1/2 : ℝ) • x)) volume := by
    change Integrable (fun x => s.spatial (halfSpatialCoordinate x)) volume at hh
    simpa only [halfSpatialCoordinate_apply] using hh
  simp only [zeroMassProfile_spatial]
  rw [integral_const_mul, integral_sub (hc.const_mul 8) hh', integral_const_mul, hhalf]
  ring

theorem Admissible.zeroMassProfile_test_integral {s : ChargeSmearing} (h : s.Admissible)
    (R : ℝ) (hR : 0 < R) : (∫ x : Spacetime, s.zeroMassProfile.test R x) = 0 := by
  rw [h.zeroMassProfile.test_integral R hR, zeroMassProfile_spatial_integral, smul_zero]

end ChargeSmearing
end YangMills
