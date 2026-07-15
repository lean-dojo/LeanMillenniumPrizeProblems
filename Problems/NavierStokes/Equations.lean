import Problems.Common.Euclidean
import Problems.NavierStokes.Imports

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

/-- Spatial coordinate space `ℝⁿ`. -/
abbrev Space (n : ℕ) : Type :=
  EuclideanCoordinateSpace ℝ n

/-- Ambient spacetime coordinates for `ℝⁿ × [0,∞)`, represented as `ℝⁿ⁺¹`. -/
abbrev Spacetime (n : ℕ) : Type :=
  Space (n + 1)

/-- Clay's whole-space spatial domain `ℝ³`. -/
abbrev Space3 : Type :=
  Space 3

/-- Ambient coordinates for Clay's whole-space spacetime `ℝ³ × [0,∞)`. -/
abbrev Spacetime3 : Type :=
  Spacetime 3

/-- Initial velocity field `u₀ : ℝⁿ → ℝⁿ`. -/
abbrev InitialVelocityField (n : ℕ) : Type :=
  Space n → Space n

/-- A velocity field `u : ℝⁿ × [0,∞) → ℝⁿ`, represented on ambient spacetime. -/
abbrev VelocityField (n : ℕ) : Type :=
  Spacetime n → Space n

/-- A pressure field `p : ℝⁿ × [0,∞) → ℝ`, represented on ambient spacetime. -/
abbrev PressureField (n : ℕ) : Type :=
  Spacetime n → ℝ

/-- An external force field acting on the fluid. -/
abbrev ForceField (n : ℕ) : Type :=
  VelocityField n

/--
The material derivative operator `∂/∂t + (u · ∇)`, i.e. the total derivative following the fluid
motion.
-/
noncomputable def material_derivative (n : ℕ) (u : VelocityField n) :
    (Spacetime n → Space n) → (Spacetime n → Space n) :=
  λ v x =>
    EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n =>
      -- Time derivative term: ∂v/∂t
      partial_deriv (n := n + 1) 0 (fun y => v y i) x +
      -- Convective term: (u·∇)v
      ∑ j : Fin n, u x j * partial_deriv (n := n + 1) (j.succ) (fun y => v y i) x)

/-- Divergence of a velocity field at a spacetime point: `div u = ∑ᵢ ∂ᵢ uᵢ`. -/
noncomputable def divergence {n : ℕ} (u : VelocityField n) (x : Spacetime n) : ℝ :=
  ∑ i : Fin n, partial_deriv (n := n + 1) (i.succ) (fun y => u y i) x

/-- Divergence-free condition at a spacetime point. -/
def divergence_free_at {n : ℕ} (u : VelocityField n) (x : Spacetime n) : Prop :=
  divergence u x = 0

/-- The viscous term `ν Δu`. -/
noncomputable def viscous_term (n : ℕ) (viscosity : ℝ) (u : VelocityField n) (x : Spacetime n) : Space n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n =>
    viscosity *
      (∑ j : Fin n,
        partial_deriv (n := n + 1) (j.succ)
          (fun y => partial_deriv (n := n + 1) (j.succ) (fun z => u z i) y) x))

/-- The spatial gradient of the pressure, `∇p`. -/
noncomputable def pressure_gradient {n : ℕ} (p : PressureField n) (x : Spacetime n) : Space n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n => partial_deriv (n := n + 1) (i.succ) p x)

/-- Convert a pair `(time, space)` to a point in spacetime. -/
noncomputable def spacetime_point {n : ℕ} (t : ℝ) (x : Space n) : Spacetime n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n + 1) (fun i : Fin (n + 1) =>
    if h : i = 0 then t else x (Fin.pred i h))

/-- Extract the time component from a spacetime point. -/
def time {n : ℕ} (x : Spacetime n) : ℝ := x 0

/-- Extract the spatial component from a spacetime point. -/
noncomputable def space {n : ℕ} (x : Spacetime n) : Space n :=
  EuclideanCoordinateSpace.of_fun (𝕜 := ℝ) (n := n) (fun i : Fin n => x (i.succ))

-- ===========================================================================
/--
  The Navier-Stokes equations in differential form for actually any general n.

  This structure encapsulates the core components of the Navier-Stokes equations,
  which describe the motion of viscous fluid substances. These equations are
  a set of nonlinear partial differential equations that govern fluid dynamics
  under the assumption of constant density.
-/
structure NavierStokesEquations (n : ℕ) where
  /--
    Viscosity coefficient (ν > 0).

    This parameter represents the fluid's resistance to flow or deformation.
    Higher values indicate more viscous fluids (like honey), while lower values
    indicate less viscous fluids (like water). In the Millennium Problem,
    we typically use ν = 1 to normalize the equations.

    It appears in the diffusion term ν·Δu, which models how momentum diffuses
    through the fluid due to molecular interactions.
  -/
  viscosity : ℝ

  /--
    External force field acting on the fluid.

    This represents any external forces applied to the fluid, such as:
    - Gravity
    - Magnetic fields
    - Mechanical forcing
    - Other body forces

    The force field is a function of both space and time, allowing for
    spatially and temporally varying external influences.
  -/
  external_force : ForceField n

  /--
    Viscosity is positive - a physical requirement.

    This constraint ensures the model is physically valid. A negative viscosity
    would violate the second law of thermodynamics, as it would cause energy to
    spontaneously concentrate rather than dissipate.
  -/
  viscosity_positive : viscosity > 0

  /--
    Initial velocity field at time t=0.

    This defines the starting configuration of the fluid flow. In the Millennium
    Problem, this initial condition is assumed to be smooth and have finite energy.

    The evolution of this initial state according to the Navier-Stokes equations
    is the central focus of the Millennium Problem - specifically whether this
    evolution remains smooth for all time or develops singularities.
  -/
  initial_velocity : InitialVelocityField n

  /--
    Initial velocity is divergence free - the incompressibility condition.

    This mathematical statement expresses that the fluid is incompressible
    (its density remains constant) at the initial time. Specifically:

    ∇·u = ∑(∂uⱼ/∂xⱼ) = 0

    Physically, this means the fluid's volume doesn't change as it flows.
    This constraint must be maintained throughout the flow evolution.
  -/
  initial_divergence_free : ∀ x, ∑ i : Fin n, partial_deriv i (λ y => initial_velocity y i) x = 0

-- ===========================================================================

/-- Spacetime domain `ℝⁿ × [0,∞)` viewed inside `ℝ^{n+1}`. -/
def global_spacetime_domain (n : ℕ) : Set (Spacetime n) :=
  {x | 0 ≤ x 0}

/--
Smoothness of a velocity field on Clay's global time domain.

The fields are still ambient functions on `ℝⁿ⁺¹`, which is convenient for partial derivatives, but
the regularity demanded by the Millennium statement is imposed on the half-space
`ℝⁿ × [0,∞)`.
-/
def velocity_smooth_on_global_spacetime_domain {n : ℕ} (u : VelocityField n) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun y => u y) (global_spacetime_domain n)

/--
Smoothness of a pressure field on Clay's global time domain.

This is the scalar analogue of `velocity_smooth_on_global_spacetime_domain`.
-/
def pressure_smooth_on_global_spacetime_domain {n : ℕ} (p : PressureField n) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun y => p y) (global_spacetime_domain n)

/--
Smoothness of a force field on Clay's global time domain.

This matches the force hypotheses in Fefferman's conditions (5) and (9), where `f` is smooth on
`ℝⁿ × [0,∞)` rather than on all of ambient spacetime.
-/
def force_smooth_on_global_spacetime_domain {n : ℕ} (f : ForceField n) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun y => f y) (global_spacetime_domain n)

/--
A global-in-time Navier–Stokes solution on `ℝⁿ × [0,∞)`.

This matches the Clay statement's use of solutions on `ℝ³ × [0,∞)`, avoiding the finite-horizon
parameter `T` used by `Solution`.
-/
structure GlobalSolution {n : ℕ} (nse : NavierStokesEquations n) where
  /-- Velocity field `u : ℝ^{n+1} → ℝⁿ`. -/
  velocity : VelocityField n
  /-- Pressure field `p : ℝ^{n+1} → ℝ`. -/
  pressure : PressureField n

  /-- Momentum equation (Navier–Stokes) on `t ≥ 0`. -/
  momentum_equation :
    ∀ x : Spacetime n,
      x ∈ global_spacetime_domain n →
        material_derivative n velocity velocity x + pressure_gradient pressure x =
          viscous_term n nse.viscosity velocity x + nse.external_force x

  /-- Incompressibility `div u = 0` on `t ≥ 0`. -/
  incompressible :
    ∀ x : Spacetime n, x ∈ global_spacetime_domain n → divergence_free_at velocity x

  /-- Initial condition at time `t = 0`. -/
  initial_condition :
    ∀ x : Space n, velocity (spacetime_point 0 x) = nse.initial_velocity x

/-- A global solution whose fields are smooth on `ℝⁿ × [0,∞)`. -/
structure GlobalSmoothSolution {n : ℕ} (nse : NavierStokesEquations n) extends GlobalSolution nse where
  velocity_smooth : velocity_smooth_on_global_spacetime_domain velocity
  pressure_smooth : pressure_smooth_on_global_spacetime_domain pressure

-- ===========================================================================
/--
  The energy of a fluid flow at time t.

  This function captures the total kinetic energy of the fluid at a given time t.
  It is defined as the integral of the squared velocity field over the spatial domain.
-/
noncomputable def energy_integral {n : ℕ} (u : VelocityField n) (t : ℝ) : ℝ :=
  ∫ x : Space n, ∑ i : Fin n, (u (spacetime_point t x) i)^2

end NavierStokes
