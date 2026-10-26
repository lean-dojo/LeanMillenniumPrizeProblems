import Problems.YangMills.StressTensor

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Actual vacuum centering of the trace-anomaly composite

Centering is fixed by the SAME physical vacuum and field, with no freely
chosen vacuum subtraction constant. This removes dependence of the trace
statement on scalar identity mixing of the curvature-square operator.
Source equivalence uses the normalized vacuum-energy convention: the stress
vacuum expectation must vanish, which still needs to follow from the actual
charge/generator normalization (not merely conservation).
-/
noncomputable section
namespace YangMills
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H}

abbrev ActualCompositeField (Q : WightmanData H) :=
  TestFunction →ₗ[ℂ] Q.domain →ₗ[ℂ] Q.domain

/-- The actual vacuum functional of this smeared field. -/
def actualVacuumOnePoint (A : ActualCompositeField Q) : TestFunction →ₗ[ℂ] ℂ where
  toFun f := inner ℂ (Q.vacuum : H) (A f Q.vacuum : H)
  map_add' f g := by simp [map_add,inner_add_right]
  map_smul' c f := by simp [map_smul,inner_smul_right]

/-- Scalar identity mixing as an actual operator-valued distribution. -/
def scalarIdentityField (scalar : TestFunction →ₗ[ℂ] ℂ) : ActualCompositeField Q where
  toFun f := scalar f • LinearMap.id
  map_add' f g := by simp [map_add,add_smul]
  map_smul' c f := by simp [map_smul,smul_smul]

/-- No subtraction datum: the vacuum expectation is computed from A itself. -/
def vacuumCenteredField (A : ActualCompositeField Q) : ActualCompositeField Q :=
  A - scalarIdentityField (actualVacuumOnePoint A)

@[simp] theorem vacuumCenteredField_apply (A : ActualCompositeField Q)
    (f : TestFunction) (v : Q.domain) :
    vacuumCenteredField A f v = A f v - actualVacuumOnePoint A f • v := rfl

/-- All scalar-identity distributions cancel exactly in the normalized
physical vacuum, not only to perturbative order or in a UV germ. -/
theorem vacuumCenteredField_identity_shift (hQ : WightmanAxioms H Q)
    (A : ActualCompositeField Q) (scalar : TestFunction →ₗ[ℂ] ℂ) :
    vacuumCenteredField (A + scalarIdentityField scalar) = vacuumCenteredField A := by
  have normalized : inner ℂ (Q.vacuum : H) (Q.vacuum : H) = 1 := by
    rw [inner_self_eq_norm_sq_to_K,hQ.vacuum_norm]
    norm_num
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  change (A f v + scalar f • v) -
      (inner ℂ (Q.vacuum : H) ((A f Q.vacuum + scalar f • Q.vacuum : Q.domain) : H)) • v =
    A f v - (inner ℂ (Q.vacuum : H) (A f Q.vacuum : H)) • v
  simp only [Submodule.coe_add,Submodule.coe_smul,inner_add_right,inner_smul_right,
    normalized,mul_one]
  module

/-- The computed centered field has zero actual vacuum one-point function. -/
theorem vacuumCenteredField_onePoint_zero (hQ : WightmanAxioms H Q)
    (A : ActualCompositeField Q) (f : TestFunction) :
    actualVacuumOnePoint (vacuumCenteredField A) f = 0 := by
  have normalized : inner ℂ (Q.vacuum : H) (Q.vacuum : H) = 1 := by
    rw [inner_self_eq_norm_sq_to_K,hQ.vacuum_norm]
    norm_num
  change inner ℂ (Q.vacuum : H)
    ((A f Q.vacuum - actualVacuumOnePoint A f • Q.vacuum : Q.domain) : H) = 0
  simp only [Submodule.coe_sub,Submodule.coe_smul,inner_sub_right,inner_smul_right,
    normalized,mul_one]
  exact sub_self _

theorem vacuumCenteredField_eq_of_onePoint_zero (A : ActualCompositeField Q)
    (zero : ∀ f, actualVacuumOnePoint A f = 0) : vacuumCenteredField A = A := by
  ext f v
  simp [vacuumCenteredField_apply,zero]

variable {G : CompactSimpleGaugeGroup} {C : RenormalizedCompositeMap Q G}
namespace StressTensorData

/-- The trace uses the SAME curvature-square label/field/vacuum. A finite
identity shift of that field cannot select a different anomaly meaning. -/
def HasVacuumCenteredTraceAnomaly (T : StressTensorData Q G C) (betaValue : ℝ)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  (∀ (A : Connection G) x,
    curvatureSquare.val.onConnection A x = classicalCurvatureSquare T.traceForm A x) ∧
  (∀ f v, ∑ mu : Fin 4, (metricSign mu : ℂ) • T.field mu mu f v =
    ((betaValue / (2 * T.coupling.val ^ 3) : ℝ) : ℂ) •
      vacuumCenteredField (C.field T.scale curvatureSquare) f v)

/-- At an actually vacuum-subtracted curvature square, this is exactly the
previous trace predicate. This is a proved reduction, not a new assumption
of zero one-point function in the general centered definition. -/
theorem hasVacuumCenteredTraceAnomaly_iff_old (T : StressTensorData Q G C)
    (betaValue : ℝ) (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G)
    (zero : ∀ f, actualVacuumOnePoint (C.field T.scale curvatureSquare) f = 0) :
    T.HasVacuumCenteredTraceAnomaly betaValue curvatureSquare ↔
      T.HasTraceAnomaly betaValue curvatureSquare := by
  unfold HasVacuumCenteredTraceAnomaly HasTraceAnomaly
  rw [vacuumCenteredField_eq_of_onePoint_zero _ zero]

/-- An explicitly shifted RHS gives exactly the same anomaly equation. The
actual candidate always uses C.field; this theorem verifies scheme covariance. -/
theorem centered_trace_rhs_identity_shift (hQ : WightmanAxioms H Q)
    (T : StressTensorData Q G C) (betaValue : ℝ)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G)
    (scalar : TestFunction →ₗ[ℂ] ℂ) (f : TestFunction) (v : Q.domain) :
    ((betaValue / (2 * T.coupling.val ^ 3) : ℝ) : ℂ) •
      vacuumCenteredField (C.field T.scale curvatureSquare + scalarIdentityField scalar) f v =
    ((betaValue / (2 * T.coupling.val ^ 3) : ℝ) : ℂ) •
      vacuumCenteredField (C.field T.scale curvatureSquare) f v := by
  rw [vacuumCenteredField_identity_shift hQ]

end StressTensorData
end YangMills
