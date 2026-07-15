import Problems.NavierStokes.Equations

namespace NavierStokesOnR3

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
def InitialVelocity : Type := Space3 → Space3

/-- Force field `f : (t,x) ∈ ℝ × ℝ³ ↦ ℝ³`, i.e. a function on spacetime `ℝ⁴`. -/
def SpacetimeForce : Type := Spacetime3 → Space3

/-- Divergence-free condition for an initial velocity field on `ℝ³`. -/
def DivergenceFreeInitial (u₀ : InitialVelocity) : Prop :=
  ∀ x, ∑ i : Fin 3, partial_deriv i (fun y => u₀ y i) x = 0

/-! ## Fefferman's conditions (4)–(7) -/

/-- Spatial derivatives of a vector field as an `ℝ³`-vector. -/
noncomputable def spatial_derivative_vector (u₀ : InitialVelocity) (α : List (Fin 3)) (x : Space3) : Space3 :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := 3) (fun i : Fin 3 => iterated_partial_deriv (n := 3) α (fun y => u₀ y i) x)

/--
Fefferman's decay condition (4) for the initial velocity `u₀` on `ℝ³`.

We encode multi-indices as lists of coordinate directions, giving a direct coordinate form of the
derivative decay condition.
-/
def SmoothRapidDecayInitial (u₀ : InitialVelocity) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
    ∀ (α : List (Fin 3)) (K : ℕ),
      ∃ C : ℝ, 0 < C ∧ ∀ x : Space3,
        ‖spatial_derivative_vector u₀ α x‖ ≤ C / (1 + ‖x‖) ^ K

/-- Mixed (time + space) derivatives of a force field as an `ℝ³`-vector. -/
noncomputable def spacetime_derivative_vector (f : SpacetimeForce) (α : List (Fin 3)) (m : ℕ) (x : Spacetime3) : Space3 :=
  let idx : List (Fin 4) := (List.replicate m (0 : Fin 4)) ++ (α.map Fin.succ)
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := 3) (fun i : Fin 3 => iterated_partial_deriv (n := 4) idx (fun y => f y i) x)

/-- Every mixed derivative of the zero force field is the zero vector. -/
@[simp] theorem spacetime_derivative_vector_zero (α : List (Fin 3)) (m : ℕ) (x : Spacetime3) :
    spacetime_derivative_vector (fun _ : Spacetime3 => (0 : Space3)) α m x = 0 := by
  ext i
  simp only [spacetime_derivative_vector, EuclideanCoordinateSpace.of_fun_apply]
  change iterated_partial_deriv (n := 4)
    (List.replicate m (0 : Fin 4) ++ α.map Fin.succ) (0 : Spacetime3 → ℝ) x = 0
  exact iterated_partial_deriv_zero
    (List.replicate m (0 : Fin 4) ++ α.map Fin.succ) x

/--
Fefferman's decay condition (5) for the forcing term `f` on `ℝ³ × [0,∞)`.

We express the weight as `(1 + |x| + t)^{-K}` using `‖space x‖` for `|x|` and the time coordinate `x 0 = t`.
-/
def SmoothRapidDecayForce (f : SpacetimeForce) : Prop :=
  force_smooth_on_global_spacetime_domain f ∧
    ∀ (α : List (Fin 3)) (m K : ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ x : Spacetime3, 0 ≤ x 0 →
          ‖spacetime_derivative_vector f α m x‖ ≤ C / (1 + ‖space x‖ + x 0) ^ K

/-- The zero force satisfies Fefferman's forcing decay condition (5). -/
theorem zero_force_smooth_rapid_decay :
    SmoothRapidDecayForce (fun _ : Spacetime3 => (0 : Space3)) := by
  refine ⟨?_, ?_⟩
  · change ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Spacetime3 => (0 : Space3)) (global_spacetime_domain 3)
    fun_prop
  intro α m K
  refine ⟨1, by norm_num, ?_⟩
  intro x hx_nonneg
  rw [spacetime_derivative_vector_zero, norm_zero]
  positivity

/-- Fefferman's smoothness condition (6) for a solution `(p,u)` on `ℝ³ × [0,∞)`. -/
def SmoothSolutionFields (u : VelocityField 3) (p : PressureField 3) : Prop :=
  velocity_smooth_on_global_spacetime_domain u ∧ pressure_smooth_on_global_spacetime_domain p

/-- A `GlobalSmoothSolution` automatically satisfies Fefferman's smoothness condition (6). -/
theorem GlobalSmoothSolution.smooth_fields {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) : SmoothSolutionFields sol.velocity sol.pressure :=
  ⟨sol.velocity_smooth, sol.pressure_smooth⟩

/-- Fefferman's bounded-energy condition (7) for a velocity field `u`. -/
def FiniteEnergy (u : VelocityField 3) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 ≤ t →
      HasFiniteIntegral (fun x : Space3 => ∑ i : Fin 3, (u (spacetime_point t x) i) ^ 2) ∧
        energy_integral u t < C

/-! ## Fefferman's statements (A) and (C) -/

/-- Navier–Stokes equations on `ℝ³` for given `ν`, initial data, and forcing. -/
def equations (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocity) (u₀_div : DivergenceFreeInitial u₀)
    (f : ForceField 3) : NavierStokesEquations 3 :=
  { viscosity := ν
    external_force := f
    viscosity_positive := ν_pos
    initial_velocity := u₀
    initial_divergence_free := u₀_div }

/--
Fefferman's statement (A): Existence and smoothness on `ℝ³`, with `f ≡ 0`.

This asks for a global smooth solution on `ℝ³ × [0,∞)` satisfying (6) and (7), for every smooth
divergence-free initial velocity satisfying (4).
-/
def SmoothExistence : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocity),
    SmoothRapidDecayInitial u₀ →
      ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
        SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity

/--
In statement (A), condition (6) is already part of `GlobalSmoothSolution`; the substantive extra
solution-side condition is the bounded energy condition (7).
-/
theorem SmoothExistence.iff_finite_energy :
    SmoothExistence ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : InitialVelocity),
        SmoothRapidDecayInitial u₀ →
        ∀ hdiv : DivergenceFreeInitial u₀,
          ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
            FiniteEnergy sol.velocity := by
  constructor
  · intro hA ν ν_pos u₀ h4 hdiv
    rcases hA ν ν_pos u₀ h4 hdiv with ⟨sol, _h6, h7⟩
    exact ⟨sol, h7⟩
  · intro hA ν ν_pos u₀ h4 hdiv
    rcases hA ν ν_pos u₀ h4 hdiv with ⟨sol, h7⟩
    exact ⟨sol, GlobalSmoothSolution.smooth_fields sol, h7⟩

/--
Fefferman's statement (C): Breakdown on `ℝ³` (forcing allowed).

For any fixed viscosity `ν > 0`, there exist smooth data `u₀,f` satisfying (4) and (5) for which
there is **no** global smooth solution on `ℝ³ × [0,∞)` satisfying (6) and (7).
-/
def Breakdown : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0),
  ∃ (u₀ : InitialVelocity) (f : SpacetimeForce),
    SmoothRapidDecayInitial u₀ ∧
    DivergenceFreeInitial u₀ ∧
    SmoothRapidDecayForce f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun x => f x)),
              SmoothSolutionFields sol.velocity sol.pressure ∧ FiniteEnergy sol.velocity)

/--
In statement (C), condition (6) is automatic for `GlobalSmoothSolution`, so the nonexistence clause
can equivalently rule out global smooth finite-energy solutions.
-/
theorem Breakdown.iff_no_finite_energy_solution :
    Breakdown ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0),
      ∃ (u₀ : InitialVelocity) (f : SpacetimeForce),
        SmoothRapidDecayInitial u₀ ∧
        DivergenceFreeInitial u₀ ∧
        SmoothRapidDecayForce f ∧
          ∀ hdiv : DivergenceFreeInitial u₀,
            ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun x => f x)),
                  FiniteEnergy sol.velocity) := by
  constructor
  · intro hC ν ν_pos
    rcases hC ν ν_pos with ⟨u₀, f, h4, hdiv₀, h5, hNo⟩
    refine ⟨u₀, f, h4, hdiv₀, h5, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, h7⟩
    exact ⟨sol, GlobalSmoothSolution.smooth_fields sol, h7⟩
  · intro hC ν ν_pos
    rcases hC ν ν_pos with ⟨u₀, f, h4, hdiv₀, h5, hNo⟩
    refine ⟨u₀, f, h4, hdiv₀, h5, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, _h6, h7⟩
    exact ⟨sol, h7⟩

end NavierStokesOnR3
