import Problems.YangMills.InvariantJetPolynomials
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Engineering dilation of the same actual classical connection

The canonical weights used in UV/OPE definitions are checked against actual
coordinate dilation of the same gauge potential and curvature. This is
support for the engineering filtration; it does not establish availability
of a homogeneous quantum subtraction scheme.
-/
noncomputable section
open scoped ContDiff
namespace YangMills
local instance dilationAlgebraNormedAddCommGroup (G : CompactSimpleGaugeGroup) : NormedAddCommGroup G.Algebra :=
  inferInstanceAs (NormedAddCommGroup (Fin G.dimension → ℝ))
local instance dilationAlgebraNormedSpace (G : CompactSimpleGaugeGroup) : NormedSpace ℝ G.Algebra :=
  inferInstanceAs (NormedSpace ℝ (Fin G.dimension → ℝ))

local instance dilationAlgebraFiniteDimensional (G : CompactSimpleGaugeGroup) : FiniteDimensional ℝ G.Algebra :=
  inferInstanceAs (FiniteDimensional ℝ (Fin G.dimension → ℝ))

/-- Continuity of the actual finite-dimensional Lie bracket, with no extra
normed-Lie-algebra structure supplied by a candidate. -/
def algebraBracketLinear (G : CompactSimpleGaugeGroup) :
    G.Algebra →ₗ[ℝ] G.Algebra →ₗ[ℝ] G.Algebra where
  toFun a := { toFun := fun b => ⁅a,b⁆
               map_add' := fun b c => lie_add a b c
               map_smul' := fun r b => lie_smul r a b }
  map_add' a b := by ext c; exact add_lie a b c
  map_smul' r a := by ext b; exact smul_lie r a b

def algebraBracketContinuous (G : CompactSimpleGaugeGroup) :
    G.Algebra →L[ℝ] G.Algebra →L[ℝ] G.Algebra :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap.toLinearMap).comp (algebraBracketLinear G))

@[simp] theorem algebraBracketContinuous_apply (G : CompactSimpleGaugeGroup) (a b : G.Algebra) :
    algebraBracketContinuous G a b = ⁅a,b⁆ := rfl

theorem contDiff_algebraBracket {G : CompactSimpleGaugeGroup}
    {f h : Spacetime → G.Algebra} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun x => ⁅f x,h x⁆) :=
  by simpa only [Function.comp_apply, algebraBracketContinuous_apply] using
    ((algebraBracketContinuous G).contDiff.comp hf).clm_apply hh

namespace Connection
variable {G : CompactSimpleGaugeGroup}

/-- A connection one-form has engineering weight one. Zero and negative
scales are included algebraically; physical UV comparisons use positive scales. -/
def dilate (A : Connection G) (scale : ℝ) : Connection G where
  potential x := scale • A.potential (scale • x)
  smooth := (A.smooth.comp ((contDiff_id : ContDiff ℝ ∞ (id : Spacetime → Spacetime)).const_smul scale)).const_smul scale

theorem partialDerivative_dilate_field (f : Spacetime → G.Algebra)
    (coefficient scale : ℝ) (mu : Fin 4) (x : Spacetime)
    (hf : DifferentiableAt ℝ f (scale • x)) :
    partialDerivative (fun y => coefficient • f (scale • y)) mu x =
      (coefficient * scale) • partialDerivative f mu (scale • x) := by
  have inner_deriv : HasFDerivAt (fun y : Spacetime => scale • y)
      (scale • ContinuousLinearMap.id ℝ Spacetime) x :=
    (hasFDerivAt_id x).const_smul scale
  have whole := (hf.hasFDerivAt.comp x inner_deriv).const_smul coefficient
  have derivative : fderiv ℝ (fun y : Spacetime => coefficient • f (scale • y)) x =
      coefficient • (fderiv ℝ f (scale • x)).comp
        (scale • ContinuousLinearMap.id ℝ Spacetime) := whole.fderiv
  unfold partialDerivative
  rw [derivative]
  simp [smul_smul]

/-- The canonical curvature weight is two, for the actual Lie bracket of G. -/
theorem curvature_dilate (A : Connection G) (scale : ℝ) (x : Spacetime) (mu nu : Fin 4) :
    (A.dilate scale).curvature x mu nu = scale ^ 2 • A.curvature (scale • x) mu nu := by
  have smooth_component (rho : Fin 4) : DifferentiableAt ℝ
      (fun y => A.potential y rho) (scale • x) :=
    ((contDiff_apply ℝ G.Algebra rho).comp A.smooth).differentiable (by norm_num) _
  change partialDerivative (fun y => scale • A.potential (scale • y) nu) mu x -
      partialDerivative (fun y => scale • A.potential (scale • y) mu) nu x +
      ⁅scale • A.potential (scale • x) mu, scale • A.potential (scale • x) nu⁆ = _
  rw [partialDerivative_dilate_field _ _ _ _ _ (smooth_component nu),
    partialDerivative_dilate_field _ _ _ _ _ (smooth_component mu)]
  simp only [curvature, lie_smul, smul_lie, smul_smul, pow_two]
  module

theorem smooth_partialDerivative (f : Spacetime → G.Algebra) (hf : ContDiff ℝ ∞ f)
    (mu : Fin 4) : ContDiff ℝ ∞ (partialDerivative f mu) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem smooth_covariantDerivative (A : Connection G) (f : Spacetime → G.Algebra)
    (hf : ContDiff ℝ ∞ f) (mu : Fin 4) : ContDiff ℝ ∞ (A.covariantDerivative f mu) :=
  (smooth_partialDerivative f hf mu).add
    (contDiff_algebraBracket ((contDiff_apply ℝ G.Algebra mu).comp A.smooth) hf)

theorem smooth_curvature (A : Connection G) (mu nu : Fin 4) :
    ContDiff ℝ ∞ (fun x => A.curvature x mu nu) :=
  ((smooth_partialDerivative _ ((contDiff_apply ℝ G.Algebra nu).comp A.smooth) mu).sub
    (smooth_partialDerivative _ ((contDiff_apply ℝ G.Algebra mu).comp A.smooth) nu)).add
      (contDiff_algebraBracket ((contDiff_apply ℝ G.Algebra mu).comp A.smooth)
        ((contDiff_apply ℝ G.Algebra nu).comp A.smooth))

theorem covariantDerivative_dilate_field (A : Connection G) (f : Spacetime → G.Algebra)
    (weight : ℕ) (scale : ℝ) (mu : Fin 4) (x : Spacetime)
    (hf : DifferentiableAt ℝ f (scale • x)) :
    (A.dilate scale).covariantDerivative (fun y => scale ^ weight • f (scale • y)) mu x =
      scale ^ (weight+1) • A.covariantDerivative f mu (scale • x) := by
  unfold covariantDerivative
  rw [partialDerivative_dilate_field f _ _ _ _ hf]
  simp only [dilate, Pi.smul_apply, lie_smul, smul_lie, smul_smul, pow_succ]
  module

end Connection

/-- All curvature descendants occurring in the actual local observable
algebra are smooth functions of the same connection. -/
theorem CurvatureJet.smooth_evaluate {G : CompactSimpleGaugeGroup}
    (j : CurvatureJet) (A : Connection G) : ContDiff ℝ ∞ (j.evaluate A) := by
  rcases j with ⟨mu,nu,ds⟩
  induction ds with
  | nil => exact A.smooth_curvature mu nu
  | cons rho ds ih => exact A.smooth_covariantDerivative _ ih rho

/-- Every actual covariant curvature descendant has exactly its prescribed
engineering weight, not merely an assigned dimension number. -/
theorem CurvatureJet.evaluate_dilate {G : CompactSimpleGaugeGroup}
    (j : CurvatureJet) (A : Connection G) (scale : ℝ) (x : Spacetime) :
    j.evaluate (A.dilate scale) x = scale ^ j.dimension • j.evaluate A (scale • x) := by
  rcases j with ⟨mu,nu,ds⟩
  induction ds generalizing x with
  | nil => exact A.curvature_dilate scale x mu nu
  | cons rho ds ih =>
      let tail : CurvatureJet := ⟨mu,nu,ds⟩
      have transformed : tail.evaluate (A.dilate scale) =
          fun y => scale ^ tail.dimension • tail.evaluate A (scale • y) := by
        funext y
        exact ih y
      change (A.dilate scale).covariantDerivative (tail.evaluate (A.dilate scale)) rho x = _
      rw [transformed]
      have identity := A.covariantDerivative_dilate_field (tail.evaluate A) tail.dimension
        scale rho x ((tail.smooth_evaluate A).differentiable (by norm_num) _)
      simpa only [CurvatureJet.dimension, List.length_cons, Nat.add_assoc, tail,
        CurvatureJet.evaluate, List.foldr_cons] using identity

/-- Polynomial evaluation under dilation uses those same actual jet weights.
This is the elementary bridge between classical labels and engineering
powers appearing in the generated short-distance formulas. -/
theorem CurvatureJetPolynomial.onConnection_dilate {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial G) (A : Connection G) (scale : ℝ) (x : Spacetime) :
    p.onConnection (A.dilate scale) x =
      MvPolynomial.eval (fun c : CurvatureJetCoordinate G =>
        scale ^ c.1.dimension * c.1.evaluate A (scale • x) c.2) p := by
  unfold CurvatureJetPolynomial.onConnection CurvatureJetPolynomial.evaluate
  apply congrArg (fun assignment : CurvatureJetCoordinate G → ℝ => MvPolynomial.eval assignment p)
  funext c
  have identity := congrArg (fun value : G.Algebra => value c.2)
    (c.1.evaluate_dilate A scale x)
  exact identity

/-- Exact weighted homogeneity, before identities on smooth connections. -/
def CurvatureJetPolynomial.EngineeringHomogeneous {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial G) (degree : ℕ) : Prop :=
  ∀ m ∈ p.support, CurvatureJetPolynomial.monomialDimension m = degree

theorem CurvatureJetPolynomial.weighted_monomial_product {G : CompactSimpleGaugeGroup}
    (m : CurvatureJetCoordinate G →₀ ℕ) (values : CurvatureJetCoordinate G → ℝ)
    (scale : ℝ) :
    (∏ c ∈ m.support, (scale ^ c.1.dimension * values c) ^ m c) =
      scale ^ CurvatureJetPolynomial.monomialDimension m *
        ∏ c ∈ m.support, values c ^ m c := by
  classical
  simp_rw [mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [CurvatureJetPolynomial.monomialDimension, Finsupp.sum]
  congr 2
  apply Finset.sum_congr rfl
  intro c _
  exact Nat.mul_comm _ _

/-- Homogeneous actual curvature labels scale with the engineering power
used by the UV/OPE presentation. Lower-degree mixtures remain permitted by
its separate filtered normalization, rather than declared homogeneous. -/
theorem CurvatureJetPolynomial.EngineeringHomogeneous.onConnection_dilate
    {G : CompactSimpleGaugeGroup} {p : CurvatureJetPolynomial G} {degree : ℕ}
    (homogeneous : p.EngineeringHomogeneous degree) (A : Connection G)
    (scale : ℝ) (x : Spacetime) :
    p.onConnection (A.dilate scale) x = scale ^ degree * p.onConnection A (scale • x) := by
  classical
  rw [CurvatureJetPolynomial.onConnection_dilate]
  unfold CurvatureJetPolynomial.onConnection CurvatureJetPolynomial.evaluate
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [CurvatureJetPolynomial.weighted_monomial_product, homogeneous m hm]
  ring

end YangMills
