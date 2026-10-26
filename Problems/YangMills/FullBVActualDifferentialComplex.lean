import Problems.YangMills.FullBVActualNilpotency

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2600000
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual SAME-action differential on the full pointwise jet algebra. -/
def classicalLocalSTLinear {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    JetAlgebra G →ₗ[ℂ] JetAlgebra G := localSTLinear (masterActionDensity e g)

@[simp] theorem classicalLocalSTLinear_apply {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (P : JetAlgebra G) :
    classicalLocalSTLinear e g P = classicalLocalSTDensity e g P := rfl

theorem classicalLocalSTLinear_comp_self {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    (classicalLocalSTLinear e g).comp (classicalLocalSTLinear e g) = 0 := by
  apply LinearMap.ext
  intro P
  exact classicalLocalST_square e g P

/-- SAME actual pointwise differential induced on integrated local functionals. -/
def classicalLocalSTFunctional {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    LocalFunctional G →ₗ[ℂ] LocalFunctional G := localSTFunctional (masterActionDensity e g)

@[simp] theorem classicalLocalSTFunctional_localClass {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (P : JetAlgebra G) :
    classicalLocalSTFunctional e g (localClass P) = localClass (classicalLocalSTDensity e g P) := rfl

/-- Nilpotency descends through the actual divergence quotient. -/
theorem classicalLocalSTFunctional_square {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : LocalFunctional G) :
    classicalLocalSTFunctional e g (classicalLocalSTFunctional e g P) = 0 := by
  induction P using Submodule.Quotient.induction_on with
  | _ P =>
    change localClass (classicalLocalSTDensity e g (classicalLocalSTDensity e g P)) = 0
    rw [classicalLocalST_square]
    rfl

theorem classicalLocalSTFunctional_comp_self {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    (classicalLocalSTFunctional e g).comp (classicalLocalSTFunctional e g) = 0 := by
  apply LinearMap.ext
  intro P
  exact classicalLocalSTFunctional_square e g P

/-- Exact pointwise polynomials are closed by the proved interacting identity. -/
theorem classicalLocalST_exact_closed {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) : LocalClassicalCocycle e g (classicalLocalSTDensity e g P) :=
  classicalLocalST_square e g P

/-- The SAME actual pointwise range is contained in its kernel. -/
theorem classicalLocalST_range_le_ker {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    LinearMap.range (classicalLocalSTLinear e g) ≤ LinearMap.ker (classicalLocalSTLinear e g) := by
  rintro P ⟨Q,rfl⟩
  exact classicalLocalST_square e g Q

/-- The integrated range/kernel inclusion uses the actual induced map. -/
theorem classicalLocalSTFunctional_range_le_ker {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    LinearMap.range (classicalLocalSTFunctional e g) ≤ LinearMap.ker (classicalLocalSTFunctional e g) := by
  rintro P ⟨Q,rfl⟩
  exact classicalLocalSTFunctional_square e g Q

end YangMills.FullBV
