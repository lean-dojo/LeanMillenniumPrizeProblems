import Problems.YangMills.PerturbativeFlow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Multilinear.Pi

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Finite Taylor determinacy for the actual flow boundary problem

A globally vanishing next derivative and the prescribed lower jets at one
point determine the smooth function. This is the analytic uniqueness step;
no analyticity or convergence of an infinite Taylor expansion is assumed.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Descend one derivative using the actual zero derivative theorem on the
whole convex vector space. -/
theorem iteratedJet_zero_step {f : E → ℂ} (smooth : ContDiff ℝ ∞ f) (k : ℕ)
    (higher : ∀ x, iteratedFDeriv ℝ (k+1) f x = 0)
    (atOrigin : iteratedFDeriv ℝ k f 0 = 0) :
    ∀ x, iteratedFDeriv ℝ k f x = 0 := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    (smooth.iteratedFDeriv_right (m := 1) (i := k) (by exact_mod_cast (show (1 : ℕ∞) + k ≤ ⊤ from le_top))).differentiable (by norm_num)
  have hzero : ∀ x, fderiv ℝ (iteratedFDeriv ℝ k f) x = 0 := by
    intro x
    apply (norm_eq_zero (a := fderiv ℝ (iteratedFDeriv ℝ k f) x)).mp
    rw [norm_fderiv_iteratedFDeriv, higher x, norm_zero]
  intro x
  exact (is_const_of_fderiv_eq_zero hd hzero x 0).trans atOrigin

/-- Finite jet determinacy, with no restriction to analytic amplitudes. -/
theorem finiteJet_determinacy {f : E → ℂ} (smooth : ContDiff ℝ ∞ f) (degree : ℕ)
    (highest : ∀ x, iteratedFDeriv ℝ (degree+1) f x = 0)
    (lower : ∀ k ≤ degree, iteratedFDeriv ℝ k f 0 = 0) : f = 0 := by
  induction degree with
  | zero =>
      have h := iteratedJet_zero_step smooth 0 highest (lower 0 (by omega))
      funext x
      have hx := congrArg (fun A => A (0 : Fin 0 → E)) (h x)
      simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply,
        Pi.zero_apply] using hx
  | succ degree ih =>
      apply ih
      · exact iteratedJet_zero_step smooth (degree+1) highest (lower _ (by omega))
      · intro k hk
        exact lower k (by omega)

/-- Coordinate evaluation determines the actual multilinear derivative tensor. -/
theorem doublePi_multilinear_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → κ → ℝ) ℂ)
    (basis : ∀ p : Fin k → ι × κ,
      A (fun i => Pi.single (p i).1 (Pi.single (p i).2 1)) = 0) : A = 0 := by
  classical
  have expand (y : ι → κ → ℝ) : y = ∑ p : ι × κ,
      y p.1 p.2 • (Pi.single p.1 (Pi.single p.2 (1 : ℝ)) : ι → κ → ℝ) := by
    ext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Fintype.sum_prod_type]
    simp only [Pi.single_apply, ite_apply, Pi.zero_apply]
    simp
  ext x
  change A x = 0
  conv_lhs => rw [show x = (fun i => ∑ p : ι × κ,
      x i p.1 p.2 • (Pi.single p.1 (Pi.single p.2 (1 : ℝ)) : ι → κ → ℝ)) from funext (fun i => expand (x i))]
  rw [A.map_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [A.map_smul_univ, basis p, smul_zero]

end YangMills.PerturbativeFlow
