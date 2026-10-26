import Problems.YangMills.RenormalizationGroup
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed extraction of RG jets from bare normalization coordinates

IZ (12-125), printed p.593, fixes g0=g Z1 Z3^(-3/2). Square roots
below have constant coefficient +1, so the formal branch is unambiguous.
The scale derivative holds the UV cutoff fixed. The bare scale identity
then fixes beta rather than allowing unrelated beta data. These operations
must be applied to the Ward-restored local action and insertion coordinates
extracted from the SAME flow system. An arbitrary pair of series Z1,Z3 is
not thereby a Yang--Mills prescription.
-/
noncomputable section
namespace YangMills.FormalRG

abbrev Series := PowerSeries ℝ

/-- The unique constant-one square root is determined degree by degree.
No analytic summation or choice of branch is used. -/
def unitSqrtCoeff (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (z (n + 1) - ∑ k : Fin n,
      unitSqrtCoeff z (k.val + 1) * unitSqrtCoeff z (n - k.val)) / 2
termination_by n => n

def unitSqrt (z : Series) : Series := PowerSeries.mk (unitSqrtCoeff (fun n => PowerSeries.coeff n z))

@[simp] theorem unitSqrt_constant (z : Series) :
    PowerSeries.constantCoeff (unitSqrt z) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [unitSqrt, unitSqrtCoeff]

/-- The recursion really squares to the prescribed series; it is not just
a symbol named square root. -/
theorem unitSqrtCoeff_square (z : ℕ → ℝ) (hz : z 0 = 1) (n : ℕ) :
    (∑ k : Fin (n + 1), unitSqrtCoeff z k.val * unitSqrtCoeff z (n - k.val)) = z n := by
  cases n with
  | zero => simp [unitSqrtCoeff, hz]
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, unitSqrtCoeff.eq_1, one_mul]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, Nat.add_sub_add_right,
      Nat.sub_self, unitSqrtCoeff.eq_1, mul_one]
    have hr := unitSqrtCoeff.eq_2 z n
    rw [hr]
    ring

theorem unitSqrt_square (z : Series) (hz : PowerSeries.constantCoeff z = 1) :
    unitSqrt z * unitSqrt z = z := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [unitSqrt, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  exact unitSqrtCoeff_square _ (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hz) n

/-- Gauge coupling in canonical bare fields. Wavefunction normalization is
essential: the cubic coefficient g Z1 alone is not the bare coupling. -/
def bareCoupling (Z1 Z3 : Series) : Series :=
  PowerSeries.X * Z1 * (unitSqrt Z3)⁻¹ ^ 3

theorem bareCoupling_constant (Z1 Z3 : Series) :
    PowerSeries.constantCoeff (bareCoupling Z1 Z3) = 0 := by
  simp [bareCoupling, PowerSeries.constantCoeff_X]

/-- The formal denominator in beta extraction is a unit with constant 1,
provided the multiplicative vertex coordinate has its fixed tree value. -/
theorem bareCoupling_derivative_constant (Z1 Z3 : Series)
    (hZ1 : PowerSeries.constantCoeff Z1 = 1) :
    PowerSeries.constantCoeff (PowerSeries.derivative ℝ (bareCoupling Z1 Z3)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp [bareCoupling, PowerSeries.coeff_one_mul, hZ1, PowerSeries.constantCoeff_X,
    unitSqrt_constant, PowerSeries.constantCoeff_inv]

/-- Coefficientwise scale derivative, with the UV cutoff held fixed by its
caller. This is an actual derivative, not an extra series parameter. -/
def scaleDerivative (f : ℝ → Series) (μ : ℝ) : Series :=
  PowerSeries.mk (fun k => μ * deriv (fun s => PowerSeries.coeff k (f s)) μ)

/-- −(μ ∂μ g0)/(∂g g0), as forced by fixed bare coupling.
The derivative denominator must have constant coefficient 1 before this
can be used as RG extraction; no formal division by a zero series is allowed. -/
def betaAtCutoff (g0 : ℝ → Series) (μ : ℝ) : Series :=
  -(scaleDerivative g0 μ) * (PowerSeries.derivative ℝ (g0 μ))⁻¹

/-- Exact UV-limit meaning of the extracted beta coefficients. The defining
right-hand side is supplied by the actual action normalization coordinates. -/
def IsBetaLimit (g0 : ℝ → ℝ → Series) (μ : ℝ) (beta : ℕ → ℝ) : Prop :=
  0 < μ ∧
  (∀ Λ0 s k, 0 < s → s < Λ0 →
    DifferentiableAt ℝ (fun t => PowerSeries.coeff k (g0 Λ0 t)) s) ∧
  (∀ Λ0, μ < Λ0 →
    PowerSeries.constantCoeff (PowerSeries.derivative ℝ (g0 Λ0 μ)) = 1) ∧
  ∀ k, Filter.Tendsto (fun Λ0 => PowerSeries.coeff k (betaAtCutoff (g0 Λ0) μ))
    Filter.atTop (nhds (beta k))

/-- Matrix inverse of a constant-identity formal insertion normalization.
The recursion uses finite matrix products and fixes all higher coefficients. -/
def inverseMatrixCoeff {n : ℕ} (Z : ℕ → Matrix (Fin n) (Fin n) ℂ) :
    ℕ → Matrix (Fin n) (Fin n) ℂ
  | 0 => 1
  | k + 1 => -∑ j : Fin (k + 1), Z (j.val + 1) * inverseMatrixCoeff Z (k - j.val)
termination_by k => k

/-- (μ∂μ + beta∂g) Z, coefficientwise. This uses the SAME extracted beta
as the action, and the SAME composite normalization matrix at both scales. -/
def normalizationScaleJet {n : ℕ}
    (Z : ℝ → ℕ → Matrix (Fin n) (Fin n) ℂ) (beta : Series) (μ : ℝ)
    (k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.of (fun i j => (μ : ℂ) * deriv (fun s => Z s k i j) μ)) +
    ∑ a : Fin (k + 1), ((PowerSeries.coeff a.val beta : ℝ) : ℂ) •
      (((k - a.val + 1 : ℕ) : ℂ) • Z μ (k - a.val + 1))

/-- Label transport Q_mu(v)=Q_bare(Z_mu v) gives Gamma=−Z⁻¹ D Z.
This sign matches Q_mu(v)=Q_(mu exp t)(R_t v) in RG.Realizes. -/
def gammaAtCutoff {n : ℕ}
    (Z : ℝ → ℕ → Matrix (Fin n) (Fin n) ℂ) (beta : Series) (μ : ℝ)
    (k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  -∑ a : Fin (k + 1), inverseMatrixCoeff (Z μ) a.val *
      normalizationScaleJet Z beta μ (k - a.val)

/-- Actual coefficientwise UV limits, not a second freely chosen gamma
series. The constant matrix must be identity for every scale and cutoff. -/
def IsGammaLimit {n : ℕ}
    (Z : ℝ → ℝ → ℕ → Matrix (Fin n) (Fin n) ℂ)
    (g0 : ℝ → ℝ → Series) (μ : ℝ)
    (gamma : ℕ → Fin n → Fin n → ℂ) : Prop :=
  0 < μ ∧
  (∀ Λ0 s k, 0 < s → s < Λ0 →
    DifferentiableAt ℝ (fun t => PowerSeries.coeff k (g0 Λ0 t)) s) ∧
  (∀ Λ0 s k i j, 0 < s → s < Λ0 →
    DifferentiableAt ℝ (fun t => Z Λ0 t k i j) s) ∧
  (∀ Λ0, μ < Λ0 →
    PowerSeries.constantCoeff (PowerSeries.derivative ℝ (g0 Λ0 μ)) = 1) ∧
  (∀ Λ0 s, 0 < s → s < Λ0 → Z Λ0 s 0 = 1) ∧
  ∀ k i j, Filter.Tendsto (fun Λ0 =>
    gammaAtCutoff (Z Λ0) (betaAtCutoff (g0 Λ0) μ) μ k i j)
      Filter.atTop (nhds (gamma k i j))

/-- Fixed bare coordinates cannot authorize two different beta predictions. -/
theorem IsBetaLimit.unique {g0 : ℝ → ℝ → Series} {μ : ℝ} {a b : ℕ → ℝ}
    (ha : IsBetaLimit g0 μ a) (hb : IsBetaLimit g0 μ b) : a = b := by
  funext k
  exact tendsto_nhds_unique (ha.2.2.2 k) (hb.2.2.2 k)

end YangMills.FormalRG
