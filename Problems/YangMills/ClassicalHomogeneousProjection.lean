import Problems.YangMills.ClassicalDilation
import Mathlib.Algebra.Polynomial.Roots

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace YangMills.CurvatureJetPolynomial
variable {G : CompactSimpleGaugeGroup}

def engineeringPart (degree : ℕ) (p : CurvatureJetPolynomial G) : CurvatureJetPolynomial G := by
  classical
  exact Finsupp.filter (fun m => monomialDimension m = degree) p

lemma engineeringPart_coeff (degree : ℕ) (p : CurvatureJetPolynomial G)
    (m : CurvatureJetCoordinate G →₀ ℕ) :
    MvPolynomial.coeff m (engineeringPart degree p) =
      if monomialDimension m = degree then MvPolynomial.coeff m p else 0 := by
  classical
  rfl

lemma engineeringPart_support (degree : ℕ) (p : CurvatureJetPolynomial G) :
    (engineeringPart degree p).support = p.support.filter (fun m => monomialDimension m = degree) := rfl

lemma engineeringPart_homogeneous (degree : ℕ) (p : CurvatureJetPolynomial G) :
    (engineeringPart degree p).EngineeringHomogeneous degree := by
  intro m hm
  exact (Finset.mem_filter.mp hm).2

lemma engineeringPart_evaluate (degree : ℕ) (p : CurvatureJetPolynomial G)
    (j : CurvatureJetAssignment G) :
    (engineeringPart degree p).evaluate j =
      ∑ m ∈ p.support, if monomialDimension m = degree then
        MvPolynomial.coeff m p * ∏ c ∈ m.support, j c.1 c.2 ^ m c else 0 := by
  classical
  unfold evaluate
  rw [MvPolynomial.eval_eq, engineeringPart_support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : monomialDimension m = degree
  · simp only [hm, ite_true, engineeringPart_coeff]
  · simp [hm]

/-- The finite univariate polynomial records the actual engineering weight
of every monomial, so its coefficients are the homogeneous projections. -/
def scalePolynomial (p : CurvatureJetPolynomial G) (j : CurvatureJetAssignment G) : Polynomial ℝ :=
  ∑ m ∈ p.support, Polynomial.monomial (monomialDimension m)
    (MvPolynomial.coeff m p * ∏ c ∈ m.support, j c.1 c.2 ^ m c)

lemma scalePolynomial_coeff (degree : ℕ) (p : CurvatureJetPolynomial G)
    (j : CurvatureJetAssignment G) :
    (scalePolynomial p j).coeff degree = (engineeringPart degree p).evaluate j := by
  classical
  rw [engineeringPart_evaluate]
  simp only [scalePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

def scaleJets (scale : ℝ) (j : CurvatureJetAssignment G) : CurvatureJetAssignment G :=
  fun k => scale ^ k.dimension • j k

lemma scalePolynomial_eval (p : CurvatureJetPolynomial G) (j : CurvatureJetAssignment G) (scale : ℝ) :
    (scalePolynomial p j).eval scale = p.evaluate (scaleJets scale j) := by
  classical
  unfold scalePolynomial evaluate
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m _
  change _ = MvPolynomial.coeff m p *
    (∏ c ∈ m.support, (scale ^ c.1.dimension * j c.1 c.2) ^ m c)
  rw [weighted_monomial_product]
  ring

lemma transform_scaleJets (g : G.Carrier) (scale : ℝ) (j : CurvatureJetAssignment G) :
    transform g (scaleJets scale j) = scaleJets scale (transform g j) := by
  funext k
  exact (G.adjoint g).map_smul (scale ^ k.dimension) (j k)

/-- Every engineering component of a genuine invariant is again invariant
under the SAME actual gauge-group adjoint representation. -/
theorem engineeringPart_invariant (degree : ℕ) {p : CurvatureJetPolynomial G}
    (invariant : p.IsInvariant) : (engineeringPart degree p).IsInvariant := by
  intro g j
  have equal : scalePolynomial p (transform g j) = scalePolynomial p j := by
    apply Polynomial.funext
    intro scale
    rw [scalePolynomial_eval, scalePolynomial_eval, ← transform_scaleJets]
    exact invariant g (scaleJets scale j)
  have coefficient := congrArg (fun P : Polynomial ℝ => P.coeff degree) equal
  simpa only [scalePolynomial_coeff] using coefficient

/-- No freely supplied invariant-component witness is required. -/
def invariantEngineeringPart (degree : ℕ) (p : invariantAlgebra G) : invariantAlgebra G :=
  ⟨engineeringPart degree p.val, engineeringPart_invariant degree p.property⟩

/-- The decomposition is an actual finite sum of coefficient projections. -/
theorem engineeringParts_sum (p : CurvatureJetPolynomial G) :
    (∑ degree ∈ p.support.image monomialDimension, engineeringPart degree p) = p := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_sum, engineeringPart_coeff]
  by_cases hz : MvPolynomial.coeff m p = 0
  · simp [hz]
  · have member : monomialDimension m ∈ p.support.image monomialDimension :=
      Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hz, rfl⟩
    simp [member]

/-- Distinct engineering components are actual orthogonal projections. -/
theorem engineeringPart_part (degree other : ℕ) (p : CurvatureJetPolynomial G) :
    engineeringPart degree (engineeringPart other p) =
      if degree=other then engineeringPart degree p else 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases same : degree=other
  · subst other; simp only [ite_true, engineeringPart_coeff]; split_ifs <;> rfl
  · rw [if_neg same]
    simp only [engineeringPart_coeff, MvPolynomial.coeff_zero]
    by_cases hd : monomialDimension m=degree <;> by_cases ho : monomialDimension m=other <;>
      simp_all

theorem engineeringPart_add (degree : ℕ) (p q : CurvatureJetPolynomial G) :
    engineeringPart degree (p+q) = engineeringPart degree p + engineeringPart degree q := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [engineeringPart_coeff, MvPolynomial.coeff_add]
  split_ifs <;> simp

theorem engineeringPart_smul (degree : ℕ) (scalar : ℝ) (p : CurvatureJetPolynomial G) :
    engineeringPart degree (scalar • p) = scalar • engineeringPart degree p := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [engineeringPart_coeff, MvPolynomial.coeff_smul]
  split_ifs <;> simp

theorem engineeringPart_zero (degree : ℕ) :
    engineeringPart degree (0 : CurvatureJetPolynomial G) = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [engineeringPart_coeff, MvPolynomial.coeff_zero, ite_self]

/-- The projection is linear on the actual invariant polynomial algebra. -/
def invariantEngineeringProjection (degree : ℕ) : invariantAlgebra G →ₗ[ℝ] invariantAlgebra G where
  toFun := invariantEngineeringPart degree
  map_add' p q := Subtype.ext (engineeringPart_add degree p.val q.val)
  map_smul' scalar p := Subtype.ext (engineeringPart_smul degree scalar p.val)

theorem invariantEngineeringParts_sum (p : invariantAlgebra G) :
    (∑ degree ∈ p.val.support.image monomialDimension, invariantEngineeringPart degree p) = p := by
  apply Subtype.ext
  change (invariantAlgebra G).val (∑ degree ∈ p.val.support.image monomialDimension,
    invariantEngineeringPart degree p) = p.val
  rw [map_sum]
  exact engineeringParts_sum p.val

theorem engineeringPart_eq_zero_of_bound (degree bound : ℕ) (higher : bound < degree)
    {p : CurvatureJetPolynomial G} (bounded : HasDimensionAtMost bound p) :
    engineeringPart degree p = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [engineeringPart_coeff, MvPolynomial.coeff_zero]
  split_ifs with weight
  · by_contra nonzero
    have le := bounded m (MvPolynomial.mem_support_iff.mpr nonzero)
    omega
  · rfl

end YangMills.CurvatureJetPolynomial

