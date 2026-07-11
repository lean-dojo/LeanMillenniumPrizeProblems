import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators RealInnerProductSpace

universe u

/-!
# Common Euclidean Coordinate Infrastructure

This module contains small Euclidean-space aliases and calculus helpers shared by multiple
Millennium problem formalizations.
-/

/--
`EuclideanCoordinateSpace 𝕜 n` is `𝕜^n` with the canonical `ℓ²` norm and inner product from
Mathlib, implemented as `EuclideanSpace 𝕜 (Fin n)`.
-/
abbrev EuclideanCoordinateSpace (𝕜 : Type u) (n : ℕ) : Type u :=
  EuclideanSpace 𝕜 (Fin n)

namespace EuclideanCoordinateSpace

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}

/-- Build a vector in `EuclideanCoordinateSpace 𝕜 n` from its coordinate function. -/
noncomputable abbrev of_fun (f : Fin n → 𝕜) : EuclideanCoordinateSpace 𝕜 n :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := 𝕜)).symm f

@[simp] theorem of_fun_apply (f : Fin n → 𝕜) (i : Fin n) :
    (of_fun (𝕜 := 𝕜) (n := n) f) i = f i := by
  simp [of_fun, EuclideanSpace.equiv]

end EuclideanCoordinateSpace

section Real

variable {n : ℕ}

/-- Standard basis vector `eᵢ` in `ℝⁿ`. -/
noncomputable def standard_basis (i : Fin n) : EuclideanCoordinateSpace ℝ n :=
  EuclideanSpace.single i (1 : ℝ)

@[simp] theorem standard_basis_apply (i j : Fin n) :
    (standard_basis (n := n) i) j = if j = i then 1 else 0 := by
  simp [standard_basis, eq_comm]

@[simp] theorem standard_basis_self (i : Fin n) : (standard_basis (n := n) i) i = 1 := by
  simp [standard_basis]

@[simp] theorem standard_basis_neq (i j : Fin n) (h : i ≠ j) :
    (standard_basis (n := n) i) j = 0 := by
  simp [standard_basis, Ne.symm h]

/-- Partial derivative `∂ᵢ f(x)` for `f : ℝⁿ → ℝ`, defined via `fderiv`. -/
noncomputable def partial_deriv
    (i : Fin n) (f : EuclideanCoordinateSpace ℝ n → ℝ) (x : EuclideanCoordinateSpace ℝ n) : ℝ :=
  (fderiv ℝ f x) (standard_basis (n := n) i)

/-- Unfolding lemma for `partial_deriv` as `fderiv` applied to the standard basis vector. -/
theorem partial_deriv_eq_fderiv_apply
    (i : Fin n) (f : EuclideanCoordinateSpace ℝ n → ℝ) (x : EuclideanCoordinateSpace ℝ n) :
    partial_deriv (n := n) i f x = (fderiv ℝ f x) (standard_basis (n := n) i) :=
  rfl

/-- Iterated partial derivative in directions specified by a list of indices. -/
noncomputable def iterated_partial_deriv
    (indices : List (Fin n)) (f : EuclideanCoordinateSpace ℝ n → ℝ)
    (x : EuclideanCoordinateSpace ℝ n) : ℝ :=
  match indices with
  | [] => f x
  | i :: rest => partial_deriv (n := n) i (fun y => iterated_partial_deriv rest f y) x

/-- Iterated derivatives of the zero function are zero. -/
@[simp]
theorem iterated_partial_deriv_zero
    (indices : List (Fin n)) (x : EuclideanCoordinateSpace ℝ n) :
    iterated_partial_deriv (n := n) indices (0 : EuclideanCoordinateSpace ℝ n → ℝ) x = 0 := by
  induction indices generalizing x with
  | nil => simp [iterated_partial_deriv]
  | cons i rest ih =>
      simp [iterated_partial_deriv, ih, partial_deriv]

end Real
