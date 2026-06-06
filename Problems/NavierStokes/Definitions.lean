import Problems.NavierStokes.Imports

open scoped BigOperators RealInnerProductSpace

universe u

/--
`Euc 𝕜 n` is `𝕜^n` with the canonical `ℓ^2` norm and inner product from Mathlib
(implemented as `EuclideanSpace 𝕜 (Fin n)`).
-/
abbrev Euc (𝕜 : Type u) (n : ℕ) : Type u :=
  EuclideanSpace 𝕜 (Fin n)

namespace Euc

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}

/-- Build a vector in `Euc 𝕜 n` from its coordinate function. -/
noncomputable abbrev ofFun (f : Fin n → 𝕜) : Euc 𝕜 n :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := 𝕜)).symm f

@[simp] theorem ofFun_apply (f : Fin n → 𝕜) (i : Fin n) :
    (ofFun (𝕜 := 𝕜) (n := n) f) i = f i := by
  simp [ofFun, EuclideanSpace.equiv]

end Euc

section Real

variable {n m : ℕ}

/-- Standard basis vector `eᵢ` in `ℝⁿ`. -/
noncomputable def standardBasis (i : Fin n) : Euc ℝ n :=
  EuclideanSpace.single i (1 : ℝ)

@[simp] theorem standardBasis_apply (i j : Fin n) :
    (standardBasis (n := n) i) j = if j = i then 1 else 0 := by
  simp [standardBasis, eq_comm]

@[simp] theorem standardBasis_self (i : Fin n) : (standardBasis (n := n) i) i = 1 := by
  simp [standardBasis]

@[simp] theorem standardBasis_neq (i j : Fin n) (h : i ≠ j) :
    (standardBasis (n := n) i) j = 0 := by
  simp [standardBasis, Ne.symm h]

/-- Partial derivative `∂ᵢ f(x)` for `f : ℝⁿ → ℝ`, defined via `fderiv`. -/
noncomputable def partialDeriv (i : Fin n) (f : Euc ℝ n → ℝ) (x : Euc ℝ n) : ℝ :=
  (fderiv ℝ f x) (standardBasis (n := n) i)

/-- Unfolding lemma: `partialDeriv` is definitionally `fderiv` applied to the standard basis vector. -/
theorem partialDeriv_eq_fderiv (i : Fin n) (f : Euc ℝ n → ℝ) (x : Euc ℝ n) :
    partialDeriv (n := n) i f x = (fderiv ℝ f x) (standardBasis (n := n) i) :=
  rfl

/-- Iterated partial derivative in directions specified by a list of indices. -/
noncomputable def iteratedPartialDeriv (indices : List (Fin n)) (f : Euc ℝ n → ℝ) (x : Euc ℝ n) : ℝ :=
  match indices with
  | [] => f x
  | i :: rest => partialDeriv (n := n) i (fun y => iteratedPartialDeriv rest f y) x

/-- Iterated derivatives of the zero function are zero. -/
@[simp]
theorem iteratedPartialDeriv_zero (indices : List (Fin n)) (x : Euc ℝ n) :
    iteratedPartialDeriv (n := n) indices (0 : Euc ℝ n → ℝ) x = 0 := by
  induction indices generalizing x with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih =>
      simp [iteratedPartialDeriv, ih, partialDeriv]

end Real

/-!
# PDE scaffolding

These are lightweight structures used by the Navier–Stokes statement files to organize PDEs.
-/

/-- List of indices for denoting partial derivatives. -/
def DerivIndices (n : ℕ) := List (Fin n)

namespace DerivIndices

/-- Empty list indicates no derivatives. -/
def zero (n : ℕ) : DerivIndices n := []

/-- Order of a derivative is the length of the list. -/
def order {n : ℕ} (α : DerivIndices n) : ℕ := α.length

/-- `|α| ≤ k` predicate for derivative lists. -/
def leq {n : ℕ} (α : DerivIndices n) (k : ℕ) : Prop := α.length ≤ k

/-- `|α| = k` predicate for derivative lists. -/
def eq {n : ℕ} (α : DerivIndices n) (k : ℕ) : Prop := α.length = k

end DerivIndices

/--
General `k`-th order partial differential equation.
`F(D^k u(x), D^{k-1} u(x), ..., Du(x), u(x), x) = 0`.
-/
structure GeneralPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) where
  /-- The equation operator. -/
  eqn : (E → F) → E → F
  /-- The domain where the equation holds. -/
  domain : Set E := Set.univ
  /-- The order of highest derivatives that appear. -/
  order : ℕ := k

/-- Linear PDE: `∑ aₐ(x) D^α u = f(x)`. -/
structure LinearPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) extends GeneralPDE 𝕜 E F n k where
  /-- Coefficients `aₐ(x)` for each derivative index `α`. -/
  coeffs : Π (α : DerivIndices n), DerivIndices.leq α k → (E → F)
  /-- Right-hand side `f(x)`. -/
  rhs : E → F
  /-- Marker that the PDE is linear. -/
  is_linear : True

/-- Fully nonlinear PDE: `F` depends nonlinearly on highest order derivatives. -/
structure FullyNonlinearPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) extends GeneralPDE 𝕜 E F n k where
  is_fully_nonlinear : True

section Examples

open scoped BigOperators

variable (n : ℕ)

/-- Divergence of a vector field `F : ℝⁿ → ℝⁿ`. -/
noncomputable def divergence (F : Euc ℝ n → Euc ℝ n) (x : Euc ℝ n) : ℝ :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y => F y i) x

/-- Laplacian `Δf` in `n` dimensions. -/
noncomputable def laplacian (f : Euc ℝ n → ℝ) (x : Euc ℝ n) : ℝ :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y => partialDeriv (n := n) i f y) x

/-- Laplace equation: `Δu = 0`. -/
noncomputable def laplace_equation : LinearPDE ℝ (Euc ℝ n) ℝ n 2 where
  eqn := fun u x => laplacian (n := n) u x
  coeffs := fun α _h => if DerivIndices.order α = 2 then fun _ => (1 : ℝ) else fun _ => (0 : ℝ)
  rhs := fun _ => (0 : ℝ)
  is_linear := trivial
  domain := Set.univ

end Examples
