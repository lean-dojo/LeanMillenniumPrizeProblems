import Problems.YangMills.ClassicalDilation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
open scoped ContDiff
namespace YangMills
local instance recenterAlgebraNormedAddCommGroup (G : CompactSimpleGaugeGroup) : NormedAddCommGroup G.Algebra :=
  inferInstanceAs (NormedAddCommGroup (Fin G.dimension → ℝ))
local instance recenterAlgebraNormedSpace (G : CompactSimpleGaugeGroup) : NormedSpace ℝ G.Algebra :=
  inferInstanceAs (NormedSpace ℝ (Fin G.dimension → ℝ))
namespace Connection
variable {G : CompactSimpleGaugeGroup}

def recenter (A : Connection G) (center : Spacetime) : Connection G where
  potential y := A.potential (y+center)
  smooth := A.smooth.comp (contDiff_id.add contDiff_const)

lemma partialDerivative_recenter (f : Spacetime → G.Algebra) (center : Spacetime)
    (mu : Fin 4) (y : Spacetime) (hf : DifferentiableAt ℝ f (y+center)) :
    partialDerivative (fun z => f (z+center)) mu y = partialDerivative f mu (y+center) := by
  have inner_derivative : HasFDerivAt (fun z : Spacetime => z+center)
      (ContinuousLinearMap.id ℝ Spacetime) y := (hasFDerivAt_id y).add_const center
  have derivative := (hf.hasFDerivAt.comp y inner_derivative).fderiv
  simp only [Function.comp_def] at derivative
  unfold partialDerivative
  rw [derivative]
  rfl

lemma curvature_recenter (A : Connection G) (center y : Spacetime) (mu nu : Fin 4) :
    (A.recenter center).curvature y mu nu = A.curvature (y+center) mu nu := by
  have smooth_component (rho : Fin 4) : DifferentiableAt ℝ
      (fun z => A.potential z rho) (y+center) :=
    ((contDiff_apply ℝ G.Algebra rho).comp A.smooth).differentiable (by norm_num) _
  change partialDerivative (fun z => A.potential (z+center) nu) mu y -
      partialDerivative (fun z => A.potential (z+center) mu) nu y +
      ⁅A.potential (y+center) mu, A.potential (y+center) nu⁆ = _
  rw [partialDerivative_recenter _ _ _ _ (smooth_component nu),
    partialDerivative_recenter _ _ _ _ (smooth_component mu)]
  rfl

lemma covariantDerivative_recenter (A : Connection G) (f : Spacetime → G.Algebra)
    (center y : Spacetime) (mu : Fin 4) (hf : DifferentiableAt ℝ f (y+center)) :
    (A.recenter center).covariantDerivative (fun z => f (z+center)) mu y =
      A.covariantDerivative f mu (y+center) := by
  unfold covariantDerivative
  rw [partialDerivative_recenter _ _ _ _ hf]
  rfl
end Connection

lemma CurvatureJet.evaluate_recenter {G : CompactSimpleGaugeGroup} (j : CurvatureJet)
    (A : Connection G) (center y : Spacetime) :
    j.evaluate (A.recenter center) y = j.evaluate A (y+center) := by
  rcases j with ⟨mu,nu,ds⟩
  induction ds generalizing y with
  | nil => exact A.curvature_recenter center y mu nu
  | cons rho ds ih =>
      let tail : CurvatureJet := ⟨mu,nu,ds⟩
      have translated : tail.evaluate (A.recenter center) = fun z => tail.evaluate A (z+center) := by
        funext z
        exact ih z
      change (A.recenter center).covariantDerivative (tail.evaluate (A.recenter center)) rho y = _
      rw [translated]
      exact A.covariantDerivative_recenter (tail.evaluate A) center y rho
        ((tail.smooth_evaluate A).differentiable (by norm_num) _)

lemma CurvatureJetPolynomial.onConnection_recenter {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial G) (A : Connection G) (center y : Spacetime) :
    p.onConnection (A.recenter center) y = p.onConnection A (y+center) := by
  unfold CurvatureJetPolynomial.onConnection CurvatureJetPolynomial.evaluate
  apply congrArg (fun assignment : CurvatureJetCoordinate G → ℝ => MvPolynomial.eval assignment p)
  funext c
  exact congrArg (fun value : G.Algebra => value c.2) (c.1.evaluate_recenter A center y)

end YangMills
