import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes

namespace MillenniumNSRDomain

open EuclideanSpace MeasureTheory Order NavierStokes
open scoped BigOperators

/-!
# Navier–Stokes Millennium problem (Fefferman) on `ℝ³`

This file states Fefferman's parts (A) and (C) from the Clay problem description
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

We follow the PDF's numbering:

* (4) decay of the initial velocity and its spatial derivatives
* (5) decay of the force and its space/time derivatives
* (6) smoothness of the solution `(p,u)` on `ℝ³ × [0,∞)`
* (7) bounded energy: `∫_{ℝ³} |u(x,t)|^2 dx < C` uniformly in `t ≥ 0`
-/

/-- Initial velocity field `u₀ : ℝ³ → ℝ³` in Fefferman's statements (A) and (C). -/
abbrev InitialVelocityR3 : Type := Euc ℝ 3 → Euc ℝ 3

/-- Force field `f : (t,x) ∈ ℝ × ℝ³ ↦ ℝ³`, i.e. a function on spacetime `ℝ⁴`. -/
abbrev ForceFieldR3 : Type := Euc ℝ 4 → Euc ℝ 3

/-- Divergence-free condition for an initial velocity field on `ℝ³`. -/
def DivergenceFreeInitial (u₀ : InitialVelocityR3) : Prop :=
  ∀ x, ∑ i : Fin 3, partialDeriv i (fun y => u₀ y i) x = 0

/-! ## Fefferman's conditions (4)–(7) -/

/-- Spatial derivatives of a vector field, packaged as an `ℝ³`-vector. -/
noncomputable def spatialDerivVec (u₀ : InitialVelocityR3) (α : List (Fin 3)) (x : Euc ℝ 3) : Euc ℝ 3 :=
  Euc.ofFun (𝕜 := ℝ) (n := 3) (fun i : Fin 3 => iteratedPartialDeriv (n := 3) α (fun y => u₀ y i) x)

/--
Fefferman's decay condition (4) for the initial velocity `u₀` on `ℝ³`.

We encode multi-indices as lists of coordinate directions; this is (slightly) stronger than the
commutative multi-index formulation, but matches the intent.
-/
def FeffermanCond4 (u₀ : InitialVelocityR3) : Prop :=
  ContDiff ℝ ⊤ u₀ ∧
    ∀ (α : List (Fin 3)) (K : ℕ),
      ∃ C : ℝ, 0 < C ∧ ∀ x : Euc ℝ 3,
        ‖spatialDerivVec u₀ α x‖ ≤ C / (1 + ‖x‖) ^ K

/-- Mixed (time + space) derivatives of a force field, packaged as an `ℝ³`-vector. -/
noncomputable def spaceTimeDerivVec (f : ForceFieldR3) (α : List (Fin 3)) (m : ℕ) (x : Euc ℝ 4) : Euc ℝ 3 :=
  let idx : List (Fin 4) := (List.replicate m (0 : Fin 4)) ++ (α.map Fin.succ)
  Euc.ofFun (𝕜 := ℝ) (n := 3) (fun i : Fin 3 => iteratedPartialDeriv (n := 4) idx (fun y => f y i) x)

/--
Fefferman's decay condition (5) for the forcing term `f` on `ℝ³ × [0,∞)`.

We express the weight as `(1 + |x| + t)^{-K}` using `‖getSpace x‖` for `|x|` and the time coordinate `x 0 = t`.
-/
def FeffermanCond5 (f : ForceFieldR3) : Prop :=
  ContDiff ℝ ⊤ f ∧
    ∀ (α : List (Fin 3)) (m K : ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ x : Euc ℝ 4, 0 ≤ x 0 →
          ‖spaceTimeDerivVec f α m x‖ ≤ C / (1 + ‖getSpace x‖ + x 0) ^ K

/-- Fefferman's smoothness condition (6) for a solution `(p,u)`. -/
def FeffermanCond6 (u : VelocityField 3) (p : PressureField 3) : Prop :=
  ContDiff ℝ ⊤ u ∧ ContDiff ℝ ⊤ p

/-- Fefferman's bounded-energy condition (7) for a velocity field `u`. -/
def FeffermanCond7 (u : VelocityField 3) : Prop :=
  ∃ C : ℝ,
    ∀ t : ℝ, 0 ≤ t →
      HasFiniteIntegral (fun x : Euc ℝ 3 => ∑ i : Fin 3, (u (pairToEuc t x) i) ^ 2) ∧
        energyIntegral u t < C

/-! ## Fefferman's statements (A) and (C) -/

/-- Navier–Stokes equations on `ℝ³` for given `ν`, initial data, and forcing. -/
def nseR3 (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocityR3) (u₀_div : DivergenceFreeInitial u₀)
    (f : ForceField 3) : NavierStokesEquations 3 :=
  { nu := ν
    f := f
    nu_pos := ν_pos
    initialVelocity := u₀
    initialDivergenceFree := u₀_div }

/--
Fefferman's statement (A): Existence and smoothness on `ℝ³`, with `f ≡ 0`.

This asks for a global smooth solution on `ℝ³ × [0,∞)` satisfying (6) and (7), for every smooth
divergence-free initial velocity satisfying (4).
-/
def FeffermanA : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocityR3),
    FeffermanCond4 u₀ →
    ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (nseR3 ν ν_pos u₀ hdiv (fun _ => 0)),
        FeffermanCond7 sol.u

/--
Fefferman's statement (C): Breakdown on `ℝ³` (forcing allowed).

There exist smooth data `u₀,f` satisfying (4) and (5) for which there is **no** global smooth
solution on `ℝ³ × [0,∞)` satisfying (6) and (7).
-/
def FeffermanC : Prop :=
  ∃ (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocityR3) (f : ForceFieldR3),
    FeffermanCond4 u₀ ∧
    DivergenceFreeInitial u₀ ∧
    FeffermanCond5 f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (nseR3 ν ν_pos u₀ hdiv (fun x => f x)),
              FeffermanCond7 sol.u)

end MillenniumNSRDomain
