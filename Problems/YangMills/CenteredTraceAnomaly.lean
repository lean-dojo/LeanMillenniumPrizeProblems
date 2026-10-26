import Problems.YangMills.VacuumCenteredTraceMeaning

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
The trace anomaly fixes the nonidentity operator content. Both fields are
centered by their actual SAME-vacuum onepoints. No absolute local vacuum
energy or freely chosen subtraction distribution is imposed.
-/
noncomputable section
namespace YangMills
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H}

/-- Exact algebraic form of centering: the scalar remainder is COMPUTED
from the same two fields and the same vacuum, not supplied as data. -/
theorem centered_equation_iff_computed_scalar (left right : ActualCompositeField Q) (c : ℂ) :
    vacuumCenteredField left = c • vacuumCenteredField right ↔
      left = c • right + scalarIdentityField
        (actualVacuumOnePoint left - c • actualVacuumOnePoint right) := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun A : ActualCompositeField Q => A f v) h
    change left f v - actualVacuumOnePoint left f • v =
      c • (right f v - actualVacuumOnePoint right f • v) at hv
    change left f v = c • right f v +
      (actualVacuumOnePoint left f - c * actualVacuumOnePoint right f) • v
    rw [sub_eq_iff_eq_add] at hv
    rw [hv]
    module
  · intro h
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun A : ActualCompositeField Q => A f v) h
    change left f v = c • right f v +
      (actualVacuumOnePoint left f - c * actualVacuumOnePoint right f) • v at hv
    change left f v - actualVacuumOnePoint left f • v =
      c • (right f v - actualVacuumOnePoint right f • v)
    rw [hv]
    module

/-- The usual anomaly modulo scalar identity is exactly the centered
relation, with no zero-vacuum-energy assumption. -/
theorem centered_equation_iff_mod_identity (hQ : WightmanAxioms H Q)
    (left right : ActualCompositeField Q) (c : ℂ) :
    vacuumCenteredField left = c • vacuumCenteredField right ↔
      ∃ scalar : TestFunction →ₗ[ℂ] ℂ, left = c • right + scalarIdentityField scalar := by
  constructor
  · intro h
    exact ⟨_, (centered_equation_iff_computed_scalar left right c).mp h⟩
  · rintro ⟨scalar,h⟩
    rw [h,vacuumCenteredField_identity_shift hQ,vacuumCenteredField_smul]

/-- Finite scalar shifts of EITHER side preserve precisely the same
nonidentity field equation, on the actual common operator domain. -/
theorem centered_equation_identity_shifts (hQ : WightmanAxioms H Q)
    (left right : ActualCompositeField Q) (c : ℂ)
    (a b : TestFunction →ₗ[ℂ] ℂ) :
    vacuumCenteredField (left + scalarIdentityField a) =
        c • vacuumCenteredField (right + scalarIdentityField b) ↔
      vacuumCenteredField left = c • vacuumCenteredField right := by
  rw [vacuumCenteredField_identity_shift hQ,vacuumCenteredField_identity_shift hQ]

variable {G : CompactSimpleGaugeGroup} {C : RenormalizedCompositeMap Q G}
namespace StressTensorData

/-- The SAME actual trace and curvature-square fields, modulo their actual
vacuum identity parts. The classical curvature contraction remains fixed. -/
def HasCenteredTraceAnomaly (T : StressTensorData Q G C) (betaValue : ℝ)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  (∀ (A : Connection G) x,
    curvatureSquare.val.onConnection A x = classicalCurvatureSquare T.traceForm A x) ∧
  vacuumCenteredField T.actualTraceField =
    ((betaValue / (2*T.coupling.val^3) : ℝ) : ℂ) •
      vacuumCenteredField (C.field T.scale curvatureSquare)

theorem hasCenteredTraceAnomaly_iff_mod_identity (hQ : WightmanAxioms H Q)
    (T : StressTensorData Q G C) (betaValue : ℝ)
    (p : CurvatureJetPolynomial.invariantAlgebra G) :
    T.HasCenteredTraceAnomaly betaValue p ↔
      (∀ (A : Connection G) x, p.val.onConnection A x = classicalCurvatureSquare T.traceForm A x) ∧
      ∃ scalar : TestFunction →ₗ[ℂ] ℂ,
        T.actualTraceField = ((betaValue / (2*T.coupling.val^3) : ℝ) : ℂ) •
          C.field T.scale p + scalarIdentityField scalar := by
  exact and_congr_right (fun _ => centered_equation_iff_mod_identity hQ _ _ _)

theorem hasCenteredTraceAnomaly_iff_computed_scalar (T : StressTensorData Q G C)
    (betaValue : ℝ) (p : CurvatureJetPolynomial.invariantAlgebra G) :
    T.HasCenteredTraceAnomaly betaValue p ↔
      (∀ (A : Connection G) x, p.val.onConnection A x = classicalCurvatureSquare T.traceForm A x) ∧
      T.actualTraceField = ((betaValue / (2*T.coupling.val^3) : ℝ) : ℂ) • C.field T.scale p +
        scalarIdentityField (actualVacuumOnePoint T.actualTraceField -
          ((betaValue / (2*T.coupling.val^3) : ℝ) : ℂ) • actualVacuumOnePoint (C.field T.scale p)) := by
  exact and_congr_right (fun _ => centered_equation_iff_computed_scalar _ _ _)

/-- The earlier one-sided centering is recovered exactly when the actual
stress trace has zero vacuum onepoint. That convention is not required by
the broader same-field trace relation. -/
theorem hasCenteredTraceAnomaly_iff_one_sided (T : StressTensorData Q G C)
    (betaValue : ℝ) (p : CurvatureJetPolynomial.invariantAlgebra G)
    (zero : ∀ f, actualVacuumOnePoint T.actualTraceField f = 0) :
    T.HasCenteredTraceAnomaly betaValue p ↔ T.HasVacuumCenteredTraceAnomaly betaValue p := by
  unfold HasCenteredTraceAnomaly HasVacuumCenteredTraceAnomaly
  rw [vacuumCenteredField_eq_of_onePoint_zero _ zero]
  apply and_congr_right
  intro _
  constructor
  · intro h f v
    have hv := congrArg (fun A : ActualCompositeField Q => A f v) h
    simpa only [actualTraceField_apply,LinearMap.smul_apply] using hv
  · intro h
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    simpa only [actualTraceField_apply,LinearMap.smul_apply] using h f v

end StressTensorData
end YangMills
