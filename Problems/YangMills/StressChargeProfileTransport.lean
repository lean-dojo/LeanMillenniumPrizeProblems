import Problems.YangMills.StressChargeProfileNormalization

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
variable {C : RenormalizedCompositeMap Q G}
namespace StressTensorData

/-- The labels, fields, Hilbert space and physical generators are literally
the same. Only the explicit spatial charge cutoff is changed. -/
def withZeroMassProfile (T : StressTensorData Q G C) : StressTensorData Q G C :=
  { T with smearing := T.smearing.zeroMassProfile }

theorem Compatible.withZeroMassProfile {T : StressTensorData Q G C} (hT : T.Compatible) :
    T.withZeroMassProfile.Compatible := by
  refine {
    correspondence := hT.correspondence
    generators := hT.generators
    admissible_smearing := hT.admissible_smearing.zeroMassProfile
    dimension_four := hT.dimension_four
    symmetry := hT.symmetry
    conservation := hT.conservation
    covariance := hT.covariance
    core_domain := hT.core_domain
    graph_core := hT.graph_core
    charge_limit := ?_
  }
  intro μ u v
  let z := inner ℂ (v : H)
    ((metricSign μ : ℂ) • (T.translations.operator μ).toLinearMap
      ⟨((u : Q.domain) : H), hT.core_domain μ u⟩)
  have lim := hT.charge_limit μ u v
  have lim2 := lim.comp
    ((tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 2 by norm_num)).mpr tendsto_id)
  have combination := ((lim.const_mul (8 : ℂ)).sub lim2).const_mul (1/7 : ℂ)
  have value : (1/7 : ℂ) * (8*z-z) = z := by ring
  change Tendsto _ atTop (nhds z)
  rw [← value]
  convert combination using 1
  funext R
  change inner ℂ (v : H)
    (T.field 0 μ ((1/7 : ℂ) • ((8 : ℂ) • T.smearing.test R - T.smearing.test (2*R)))
      (u : Q.domain) : H) = _
  simp only [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply,
    Submodule.coe_smul, Submodule.coe_sub, inner_smul_right, inner_sub_right, Function.comp_apply, id_eq]

/-- A constant scalar identity density contributes exactly zero to these
actual charge tests. The limit is the SAME original translation generator. -/
theorem Compatible.constant_identity_shift_charge_limit {T : StressTensorData Q G C}
    (hT : T.Compatible) (c : ℂ) (μ : Fin 4) (u : T.chargeCore) (v : Q.domain) :
    Tendsto (fun R : ℝ => inner ℂ (v : H)
      ((T.field 0 μ (T.smearing.zeroMassProfile.test R) (u : Q.domain) : H) +
        (c * ∫ x : Spacetime, T.smearing.zeroMassProfile.test R x) • (u : H)))
      atTop (nhds (inner ℂ (v : H)
        ((metricSign μ : ℂ) • (T.translations.operator μ).toLinearMap
          ⟨((u : Q.domain) : H), hT.core_domain μ u⟩))) := by
  have hlim := hT.withZeroMassProfile.charge_limit μ u v
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [hT.admissible_smearing.zeroMassProfile_test_integral R hR]
  simp only [mul_zero, zero_smul, add_zero]
  rfl

end StressTensorData
end YangMills
