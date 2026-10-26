import Problems.YangMills.FourierTaylorRadial
import Mathlib.LinearAlgebra.Multilinear.Pi

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization

/-- Complete actual coordinate expansion of a real multilinear momentum
tensor. This is a finite equality, not a formal Taylor convergence premise. -/
theorem doublePi_multilinear_expansion {J K : Type*} [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K] (n : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => J → K → ℝ) ℂ)
    (x : Fin n → J → K → ℝ) :
    A x = ∑ p : Fin n → J × K,
      (∏ i : Fin n, x i (p i).1 (p i).2) •
        A (fun i => Pi.single (p i).1 (Pi.single (p i).2 1)) := by
  classical
  have expand (y : J → K → ℝ) : y = ∑ p : J × K,
      y p.1 p.2 • (Pi.single p.1 (Pi.single p.2 (1 : ℝ)) : J → K → ℝ) := by
    ext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      Pi.single_apply, ite_apply, Pi.zero_apply]
    simp
  conv_lhs => rw [show x = (fun i => ∑ p : J × K,
      x i p.1 p.2 • (Pi.single p.1 (Pi.single p.2 (1 : ℝ)) : J → K → ℝ)) from
        funext (fun i => expand (x i))]
  rw [A.map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact A.map_smul_univ _ _

end YangMills.IntegratedNormalization
