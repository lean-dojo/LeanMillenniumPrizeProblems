import YangMills.QuantumCorrelations

/-!
# Short-distance quantities on the actual quantum fields

These definitions fix normalized four-dimensional smearing, finite subtraction,
and a testwise remainder estimate. They are NOT the prescribed Yang--Mills
expansion: no perturbative coefficient algorithm or OPE is asserted here.
In particular `TestwiseExpansion` is a relation to a *given* expansion, not
permission for a proof submitter to select predictions. A final specification
must fix the group-dependent perturbative calculation and justify the required
(topologically stronger, if needed) distributional remainder condition.
-/

noncomputable section
open Filter
namespace YangMills

/-- Normalized dilation f_lambda(x) = lambda^(-4) f(x/lambda).
The zero extension is irrelevant to limits through strictly positive scales.
The exponent is the spacetime dimension, not a field scaling dimension. -/
def dilateTest (scale : ℝ) (f : TestFunction) : TestFunction :=
  if h : scale ≠ 0 then
    ((scale⁻¹ ^ 4 : ℝ) : ℂ) •
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.smulLeft (Units.mk0 scale h)⁻¹) f
  else 0

@[simp] theorem dilateTest_apply {scale : ℝ} (h : scale ≠ 0)
    (f : TestFunction) (x : Spacetime) :
    dilateTest scale f x = ((scale⁻¹ ^ 4 : ℝ) : ℂ) * f (scale⁻¹ • x) := by
  simp [dilateTest, h, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.smulLeft, Units.smul_def]

@[simp] theorem dilateTest_one (f : TestFunction) : dilateTest 1 f = f := by
  ext x
  simp [dilateTest_apply one_ne_zero]

namespace WightmanData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- All insertions approach the same origin, using the same fields and vacuum
as the physical Hamiltonian. There is no independent correlation datum. -/
def scaledVacuumNPoint (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction)) (scale : ℝ) : ℂ :=
  Q.vacuumNPoint (word.map fun p => (p.1, dilateTest scale p.2))

@[simp] theorem scaledVacuumNPoint_one (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction)) :
    Q.scaledVacuumNPoint word 1 = Q.vacuumNPoint word := by
  simp [scaledVacuumNPoint]

/-- A finite prescribed subtraction, with no convergence of infinite series
assumed. The coefficient terms can contain powers and logarithms of scale. -/
def expansionRemainder (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction))
    (terms : ℕ → ℝ → ℂ) (order : ℕ) (scale : ℝ) : ℂ :=
  Q.scaledVacuumNPoint word scale - ∑ k ∈ Finset.range order, terms k scale

/-- Explicit testwise asymptotics at scale -> 0+, including all epsilon and
delta quantifiers. `rate` is the prescribed remainder scale. Nonzero rate near
zero is needed when using a ratio formulation, but not in this inequality.
This is not a bounded-set estimate, a point-field OPE, or YM identification. -/
def TestwiseExpansion (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction))
    (terms : ℕ → ℝ → ℂ) (order : ℕ) (rate : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ scale : ℝ,
    0 < scale → scale < δ →
      ‖Q.expansionRemainder word terms order scale‖ ≤ ε * ‖rate scale‖

/-- Adversarial negative control: freely choosing expansion terms makes this
relation vacuous as a definition of Yang--Mills predictions. The first term
can simply be the correlation itself, for any theory and any requested rate.
A final target must therefore fix the coefficients independently of Q. -/
theorem selfSelectedExpansion (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction)) (rate : ℝ → ℝ) :
    Q.TestwiseExpansion word
      (fun k scale => if k = 0 then Q.scaledVacuumNPoint word scale else 0) 1 rate := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro scale _ _
  simp only [expansionRemainder, Finset.range_one, Finset.sum_singleton, if_true,
    sub_self, norm_zero]
  exact mul_nonneg hε.le (norm_nonneg _)

end WightmanData
end YangMills
