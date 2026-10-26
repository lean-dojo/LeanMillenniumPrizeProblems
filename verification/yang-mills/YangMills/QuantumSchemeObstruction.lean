import YangMills.RenormalizationGroup

/-!
# A dimensionful identity shift is not homogeneous scale transport

This elementary counterexample concerns presentations, not existence of a
Yang--Mills candidate. It shows why availability of a homogeneous CLASSICAL
basis does not establish invariance of the chosen QUANTUM scheme restriction
under allowed dimension-filtered identity mixing. A nonzero correction can
be assigned positive loop/coupling order without changing this obstruction.
-/
noncomputable section
namespace YangMills.QuantumSchemeAudit

abbrev TwoOperators := Fin 2 → ℝ

def operatorUnit : TwoOperators := Pi.single 1 1

def shiftedOperator (correction mu : ℝ) (degree : ℕ) : TwoOperators :=
  Pi.single 0 1 + (correction * mu ^ degree) • operatorUnit

/-- A genuine invertible triangular label change; it fixes the unit. -/
def identityShift (a : ℝ) : TwoOperators ≃ₗ[ℝ] TwoOperators where
  toFun v i := if i = 0 then v 0 else v i + a * v 0
  invFun v i := if i = 0 then v 0 else v i - a * v 0
  left_inv v := by funext i; by_cases h : i=0 <;> simp [h]
  right_inv v := by funext i; by_cases h : i=0 <;> simp [h]
  map_add' v w := by funext i; by_cases h : i=0 <;> simp [h]; ring
  map_smul' c v := by funext i; by_cases h : i=0 <;> simp [h]; ring

@[simp] theorem identityShift_unit (a : ℝ) : identityShift a operatorUnit = operatorUnit := by
  ext i
  fin_cases i <;> simp [identityShift,operatorUnit]

@[simp] theorem identityShift_operator (correction mu : ℝ) (degree : ℕ) :
    identityShift (correction * mu ^ degree) (Pi.single 0 1) =
      shiftedOperator correction mu degree := by
  ext i
  fin_cases i <;> simp [identityShift,shiftedOperator,operatorUnit]

/-- With distinct engineering degrees for O and 1, homogeneous transport
can only multiply O by a scalar. A dimensionful identity shift at two scales
cannot be implemented by such transport, even though the shift is invertible. -/
theorem shiftedOperator_no_scalar_transport (correction mu nu : ℝ) (degree : ℕ)
    (nonzero : correction ≠ 0) (different : mu ^ degree ≠ nu ^ degree) :
    ¬ ∃ r : ℝ, shiftedOperator correction mu degree = r • shiftedOperator correction nu degree := by
  rintro ⟨r,equal⟩
  have first := congrFun equal 0
  have second := congrFun equal 1
  simp [shiftedOperator,operatorUnit] at first second
  have rone : r=1 := first.symm
  rw [rone,one_mul] at second
  exact different (mul_left_cancel₀ nonzero second)

/-- Already the degree-four identity mixing relevant to scalar curvature
observables obstructs exact homogeneous transport between positive RG scales. -/
theorem degreeFourShift_no_rg_transport (correction mu t : ℝ)
    (nonzero : correction ≠ 0) (positive : 0 < mu) (time_positive : 0 < t) :
    ¬ ∃ r : ℝ, shiftedOperator correction mu 4 =
      r • shiftedOperator correction (mu * Real.exp t) 4 := by
  apply shiftedOperator_no_scalar_transport correction mu (mu * Real.exp t) 4 nonzero
  have growth : mu < mu * Real.exp t := by
    have ex := Real.one_lt_exp_iff.mpr time_positive
    nlinarith
  have both : 0 < mu * Real.exp t := mul_pos positive (Real.exp_pos t)
  have squares : mu^2 < (mu*Real.exp t)^2 := by nlinarith
  nlinarith [sq_nonneg (mu^2),sq_nonneg ((mu*Real.exp t)^2)]

/-- The corrected order transports first and canonically scales the
EXTERNAL label afterwards. The running-scale identity shift is finite and
has exactly its reference-scale value, including its dimensionful factor. -/
theorem identityShift_filtered_scaling (correction mu scale : ℝ) (degree : ℕ)
    (nonzero_scale : scale ≠ 0) :
    scale ^ degree • (shiftedOperator correction mu degree +
      (correction * ((mu / scale)^degree - mu^degree)) • operatorUnit) =
      scale ^ degree • (Pi.single 0 1 : TwoOperators) + (correction * mu^degree) • operatorUnit := by
  ext i
  simp only [shiftedOperator,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  have denominator : scale^degree ≠ 0 := pow_ne_zero _ nonzero_scale
  rw [div_pow]
  field_simp
  ring

end YangMills.QuantumSchemeAudit
