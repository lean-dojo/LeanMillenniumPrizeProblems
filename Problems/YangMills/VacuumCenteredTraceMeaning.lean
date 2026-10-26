import Problems.YangMills.VacuumCenteredTrace

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H}

lemma vacuumCenteredField_smul (c : ℂ) (A : ActualCompositeField Q) :
    vacuumCenteredField (c • A) = c • vacuumCenteredField A := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  change c • A f v - (inner ℂ (Q.vacuum : H) ((c • A f Q.vacuum : Q.domain) : H)) • v =
    c • (A f v - actualVacuumOnePoint A f • v)
  simp only [Submodule.coe_smul,inner_smul_right,actualVacuumOnePoint,smul_sub,smul_smul]
  rfl

/-- Centering precisely removes the scalar ambiguity in a normalized
vacuum-zero observable equation. The scalar distribution is arbitrary in
this theorem; the actual centered field contains no such choice. -/
theorem eq_centered_of_scalar_ambiguity (hQ : WightmanAxioms H Q)
    (left right : ActualCompositeField Q) (c : ℂ) (scalar : TestFunction →ₗ[ℂ] ℂ)
    (equation : left = c • right + scalarIdentityField scalar)
    (zero : ∀ f, actualVacuumOnePoint left f = 0) :
    left = c • vacuumCenteredField right := by
  calc
    left = vacuumCenteredField left := (vacuumCenteredField_eq_of_onePoint_zero _ zero).symm
    _ = vacuumCenteredField (c • right + scalarIdentityField scalar) := congrArg vacuumCenteredField equation
    _ = vacuumCenteredField (c • right) := vacuumCenteredField_identity_shift hQ _ scalar
    _ = c • vacuumCenteredField right := vacuumCenteredField_smul c right

variable {G : CompactSimpleGaugeGroup} {C : RenormalizedCompositeMap Q G}
namespace StressTensorData

def actualTraceField (T : StressTensorData Q G C) : ActualCompositeField Q :=
  ∑ mu : Fin 4, (metricSign mu : ℂ) • T.field mu mu

@[simp] theorem actualTraceField_apply (T : StressTensorData Q G C)
    (f : TestFunction) (v : Q.domain) :
    T.actualTraceField f v = ∑ mu : Fin 4, (metricSign mu : ℂ) • T.field mu mu f v := by
  simp [actualTraceField]

/-- Standard anomaly modulo scalar identity, together with normalized
stress vacuum energy, implies the concrete centered anomaly predicate. -/
theorem hasVacuumCenteredTraceAnomaly_of_mod_identity (hQ : WightmanAxioms H Q)
    (T : StressTensorData Q G C) (betaValue : ℝ)
    (p : CurvatureJetPolynomial.invariantAlgebra G)
    (classical : ∀ (A : Connection G) x,
      p.val.onConnection A x = classicalCurvatureSquare T.traceForm A x)
    (scalar : TestFunction →ₗ[ℂ] ℂ)
    (anomaly : T.actualTraceField =
      ((betaValue / (2*T.coupling.val^3) : ℝ) : ℂ) • C.field T.scale p + scalarIdentityField scalar)
    (vacuum_zero : ∀ f, actualVacuumOnePoint T.actualTraceField f = 0) :
    T.HasVacuumCenteredTraceAnomaly betaValue p := by
  refine ⟨classical,?_⟩
  intro f v
  have exact_anomaly := eq_centered_of_scalar_ambiguity hQ T.actualTraceField
    (C.field T.scale p) ((betaValue / (2*T.coupling.val^3) : ℝ) : ℂ) scalar anomaly vacuum_zero
  have value := congrArg (fun A : ActualCompositeField Q => A f v) exact_anomaly
  simpa only [actualTraceField_apply,LinearMap.smul_apply] using value

end StressTensorData
end YangMills
