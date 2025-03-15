import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

/-- The velocity field: a vector-valued function on ℝⁿ⁺¹ (space + time) -/
def VelocityField (n : ℕ) := Euc ℝ (n+1) → Euc ℝ n

/-- The pressure field: a scalar function on ℝⁿ⁺¹ (space + time) -/
def PressureField (n : ℕ) := Euc ℝ (n+1) → ℝ

/-- External force field acting on the fluid -/
def ForceField (n : ℕ) := Euc ℝ (n+1) → Euc ℝ n

/-- Material derivative operator: ∂/∂t + (u·∇)
    This represents the total derivative following fluid motion -/
noncomputable def MaterialDerivative (n : ℕ) (u : VelocityField n) :
    (Euc ℝ (n+1) → Euc ℝ n) → (Euc ℝ (n+1) → Euc ℝ n) :=
  λ v x =>
    -- Time derivative term: ∂v/∂t
    (λ i => partialDeriv 0 (λ y => v y i) x) +
    -- Convective term: (u·∇)v
    (λ i => ∑ j : Fin n, u x j * partialDeriv (j.succ) (λ y => v y i) x)

/-- The divergence-free condition: ∇·u = 0 -/
noncomputable def DivergenceFree {n : ℕ} (u : VelocityField n) : Prop :=
  ∀ x, ∑ i : Fin n, partialDeriv (i.succ) (λ y => u y i) x = 0

/-- The viscous stress term: ν·Δu -/
noncomputable def ViscousTerm (n : ℕ) (nu : ℝ) (u : VelocityField n) (x : Euc ℝ (n+1)) : Euc ℝ n :=
  λ i => nu * (∑ j : Fin n, partialDeriv (j.succ) (λ y => partialDeriv (j.succ) (λ z => u z i) y) x)

/-- Spatial gradient of the pressure: ∇p -/
noncomputable def PressureGradient {n : ℕ} (p : PressureField n) (x : Euc ℝ (n+1)) : Euc ℝ n :=
  λ i => partialDeriv (i.succ) p x

/-- Helper function to convert a pair (time, space) to a point in spacetime -/
def pairToEuc {n : ℕ} (t : ℝ) (x : Euc ℝ n) : Euc ℝ (n+1) :=
  fun i =>
    if h : i = 0
    then t
    else x (Fin.pred i h)

/-- Helper function to extract the time component from a spacetime point -/
def getTime {n : ℕ} (x : Euc ℝ (n+1)) : ℝ := x 0

/-- Helper function to extract the space component from a
time point -/
def getSpace {n : ℕ} (x : Euc ℝ (n+1)) : Euc ℝ n :=
  fun i => x (i.succ)

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
  nu : ℝ

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
  f : ForceField n

  /--
    Viscosity is positive - a physical requirement.

    This constraint ensures the model is physically valid. A negative viscosity
    would violate the second law of thermodynamics, as it would cause energy to
    spontaneously concentrate rather than dissipate.
  -/
  nu_pos : nu > 0

  /--
    Initial velocity field at time t=0.

    This defines the starting configuration of the fluid flow. In the Millennium
    Problem, this initial condition is assumed to be smooth and have finite energy.

    The evolution of this initial state according to the Navier-Stokes equations
    is the central focus of the Millennium Problem - specifically whether this
    evolution remains smooth for all time or develops singularities.
  -/
  initialVelocity : Euc ℝ n → Euc ℝ n

  /--
    Initial velocity is divergence free - the incompressibility condition.

    This mathematical statement expresses that the fluid is incompressible
    (its density remains constant) at the initial time. Specifically:

    ∇·u = ∑(∂uⱼ/∂xⱼ) = 0

    Physically, this means the fluid's volume doesn't change as it flows.
    This constraint must be maintained throughout the flow evolution.
  -/
  initialDivergenceFree : ∀ x, ∑ i : Fin n, partialDeriv i (λ y => initialVelocity y i) x = 0

-- ===========================================================================

/--
  A solution to the Navier-Stokes equations.

  This structure defines what constitutes a mathematical solution to the Navier-Stokes
  equations on the time interval [0,T). It captures both the physical variables
  (velocity and pressure) and the mathematical conditions they must satisfy.
-/
structure Solution {n : ℕ} (nse : NavierStokesEquations n) where
  /--
    Velocity field solution - a vector field representing fluid flow.

    The velocity u(x,t) gives the fluid velocity vector at position x and time t,
    where x ∈ ℝⁿ and t ∈ [0,T). This is the primary unknown in the equations.
  -/
  u : VelocityField n

  /--
    Pressure field solution - a scalar field representing fluid pressure.

    The pressure p(x,t) gives the fluid pressure at position x and time t.
    It acts as a Lagrange multiplier enforcing the incompressibility constraint.
  -/
  p : PressureField n

  /--
    Time interval of existence [0, T).

    The maximal time T for which the solution is defined. One of the key
    questions of the Millennium Problem is whether T can be infinite.
  -/
  T : ℝ

  /--
    T is positive - ensures a non-degenerate time interval.

    This guarantees that the solution exists for at least some positive time.
  -/
  T_pos : T > 0

  /--
    Domain is [0,T) × ℝⁿ - the spacetime region where the solution is defined.

    This represents the product of the time interval [0,T) with the entire
    spatial domain ℝⁿ, giving a half-open cylinder in ℝⁿ⁺¹.
  -/
  domain : Set (Euc ℝ (n+1)) := {x | 0 ≤ x 0 ∧ x 0 < T}

  /--
    The solution satisfies the momentum equation - Newton's 2nd law for fluids.

    This is the core dynamical equation of fluid motion:
    ∂u/∂t + (u·∇)u + ∇p = ν·Δu + f

    From left to right, the terms represent:
    - Material acceleration (time derivative following fluid motion)
    - Pressure gradient force
    - Viscous dissipation
    - External forces

    This equation expresses conservation of momentum in the fluid.
  -/
  momentum_equation : ∀ x ∈ domain, MaterialDerivative n u u x + PressureGradient p x = ViscousTerm n nse.nu u x + nse.f x

  /--
    The solution satisfies the incompressibility condition - fluid volume is preserved.

    This constraint requires that ∇·u = 0 everywhere, expressing that the
    fluid density remains constant (fluid is incompressible). Mathematically,
    this means the velocity field is divergence-free at all points in the domain.

    This is a kinematic constraint rather than a dynamic equation.
  -/
  incompressible : ∀ x ∈ domain, DivergenceFree u

  /--
    The solution matches the initial condition at t=0.

    This ensures that the solution starts from the prescribed initial velocity field.
    The initial condition is critical in determining the subsequent evolution of the flow.
    In the Millennium Problem, this initial data is assumed to be smooth and have finite energy.
  -/
  initial_condition : ∀ x : Euc ℝ n, u (pairToEuc 0 x) = nse.initialVelocity x

-- ===========================================================================
/--
  The energy of a fluid flow at time t.

  This function captures the total kinetic energy of the fluid at a given time t.
  It is defined as the integral of the squared velocity field over the spatial domain.
-/
noncomputable def kineticEnergy {n : ℕ} (u : VelocityField n) (t : ℝ) : ℝ :=
  ∫ x : Euc ℝ n, (1/2) * ∑ i : Fin n, (u (pairToEuc t x) i)^2

/-- The enstrophy function needs to be updated as well -/
noncomputable def enstrophy {n : ℕ} (u : VelocityField n) (t : ℝ) : ℝ :=
  ∫ x : Euc ℝ n, (1/2) * ∑ i : Fin n, ∑ j : Fin n,
    (partialDeriv (j.succ) (λ y => u y i) (pairToEuc t x) -
     partialDeriv (i.succ) (λ y => u y j) (pairToEuc t x))^2

/-- A smooth solution to the Navier-Stokes equations -/
structure SmoothSolution {n : ℕ} (nse : NavierStokesEquations n) extends Solution nse where
  /-- The velocity field is infinitely differentiable -/
  velocity_smooth : ∀ x ∈ domain, ContDiffAt ℝ ⊤ (λ y => u y) x
  /-- The pressure field is infinitely differentiable -/
  pressure_smooth : ∀ x ∈ domain, ContDiffAt ℝ ⊤ (λ y => p y) x

-- ===========================================================================
/--
  # A weak solution to the Navier-Stokes equations in a suitable Sobolev space.

  This structure defines a generalized solution concept that requires less regularity
  than classical solutions. Weak solutions are formulated using integration by parts
  and test functions, allowing solutions that may not be differentiable in the classical sense.

  Jean Leray pioneered this approach in 1934, proving the existence of weak solutions
  to the Navier-Stokes equations, but their uniqueness and regularity remain open questions.
-/
structure WeakSolution {n : ℕ} (nse : NavierStokesEquations n) where
  /--
    Velocity field solution - the primary unknown function.

    Unlike in the classical solution, this velocity field is only required
    to have limited regularity (belonging to specific Sobolev spaces).
  -/
  u : VelocityField n

  /--
    Pressure field solution - acts as a Lagrange multiplier for incompressibility.

    In weak formulations, the pressure has reduced regularity requirements
    compared to classical solutions.
  -/
  p : PressureField n

  /--
    Time interval of existence [0, T).

    For weak solutions, existence can often be proven for all time (T = ∞),
    unlike smooth solutions which may develop singularities.
  -/
  T : ℝ

  /--
    T is positive - ensures a non-degenerate time interval.
  -/
  T_pos : T > 0

  /--
    Domain is [0,T) × ℝⁿ - the spacetime region where the solution is defined.
  -/
  domain : Set (Euc ℝ (n+1)) := {x | 0 ≤ x 0 ∧ x 0 < T}

  /--
    The velocity field belongs to the appropriate Sobolev space.

    Specifically, for each time t, the velocity field:
    - Belongs to L²(ℝⁿ) (finite energy)
    - Has first derivatives in L²(ℝⁿ) (finite enstrophy)

    This corresponds to the Sobolev space H¹(ℝⁿ), which is crucial for
    the energy methods used in analyzing the Navier-Stokes equations.

    These regularity conditions are much weaker than those required for
    classical solutions, allowing for velocity fields that aren't necessarily
    continuously differentiable.
  -/
  velocity_regularity : ∀ t ∈ Set.Icc 0 T,
    -- u(t,·) is in L² (finite energy)
    HasFiniteIntegral (fun x => ∑ i : Fin n, (u (pairToEuc t x) i)^2) ∧
    -- ∇u(t,·) is in L² (finite enstrophy)
    HasFiniteIntegral (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (partialDeriv (j.succ) (λ y => u y i) (pairToEuc t x))^2)

  /--
    The solution satisfies the momentum equation in the weak sense.

    Instead of requiring the PDE to hold pointwise, we multiply by smooth
    test functions with compact support and integrate by parts. This transfers
    derivatives from the solution to the test function, requiring less regularity.

    The equation represents:
    ∫∫[-∂φ/∂t·u - (u·∇φ)·u + ν∇u:∇φ - p div φ + f·φ] dx dt = 0

    Each term corresponds to a part of the Navier-Stokes momentum equation:
    1. Time derivative term
    2. Convective (nonlinear) term
    3. Viscous diffusion term
    4. Pressure gradient term
    5. External force term

    This formulation is derived by multiplying the momentum equation by a test
    function φ, integrating over the domain, and applying integration by parts.
  -/
  weak_momentum_equation : ∀ φ : Euc ℝ (n+1) → Euc ℝ n,
    -- Test function requirements (smooth, compact support, divergence-free)
    ContDiff ℝ ⊤ φ →
    (∃ K : Set (Euc ℝ (n+1)), IsCompact K ∧ ∀ x ∉ K, φ x = 0) →
    (∀ x ∈ domain, ∑ i : Fin n, partialDeriv (i.succ) (λ y => φ y i) x = 0) →
    -- Weak formulation of momentum equation
    ∫ t in Set.Icc 0 T, ∫ x : Euc ℝ n,
      (-(∑ i : Fin n, u (pairToEuc t x) i * partialDeriv 0 (λ y => φ y i) (pairToEuc t x))  -- Time derivative term
       -(∑ i : Fin n, ∑ j : Fin n, u (pairToEuc t x) i * u (pairToEuc t x) j *
           partialDeriv (j.succ) (λ y => φ y i) (pairToEuc t x))  -- Convective (nonlinear) term
       +nse.nu * (∑ i : Fin n, ∑ j : Fin n,
           partialDeriv (j.succ) (λ y => u y i) (pairToEuc t x) *
           partialDeriv (j.succ) (λ y => φ y i) (pairToEuc t x))  -- Viscous diffusion term
       -(∑ i : Fin n, p (pairToEuc t x) * partialDeriv (i.succ) (λ y => φ y i) (pairToEuc t x))  -- Pressure term
       +(∑ i : Fin n, nse.f (pairToEuc t x) i * φ (pairToEuc t x) i)) = 0  -- External force term

  /--
    The solution satisfies the incompressibility condition in the weak sense.

    This represents the divergence-free constraint ∇·u = 0 in its weak form.
    It states that for any smooth test function ψ with compact support,
    the integral of u·∇ψ vanishes.

    This is derived by multiplying the incompressibility equation by test functions
    and applying integration by parts:
    ∫ div(u)·ψ dx = 0  →  ∫ u·∇ψ dx = 0

    The condition ensures mass conservation in the weak formulation.
  -/
  weak_incompressible :
    ∀ t ∈ Set.Icc 0 T, ∀ ψ : Euc ℝ n → ℝ,
    ContDiff ℝ ⊤ ψ →
    (∃ K : Set (Euc ℝ n), IsCompact K ∧ ∀ x ∉ K, ψ x = 0) →
    ∫ x : Euc ℝ n, (∑ i : Fin n, partialDeriv i (λ y => u (pairToEuc t y) i) x * ψ x) = 0

  /--
    The solution matches the initial condition at t=0 in the weak sense.

    Rather than requiring pointwise equality, this states that the velocity field
    at t=0 equals the initial data when tested against smooth functions.

    For any smooth test function φ with compact support:
    ∫ u(0,x)·φ(x) dx = ∫ u₀(x)·φ(x) dx

    This is a weaker way of requiring that the solution starts from the given
    initial condition, suitable for functions with limited regularity.
  -/
  weak_initial_condition :
    ∀ φ : Euc ℝ n → Euc ℝ n,
    ContDiff ℝ ⊤ φ →
    (∃ K : Set (Euc ℝ n), IsCompact K ∧ ∀ x ∉ K, φ x = 0) →
    ∫ x : Euc ℝ n, (∑ i : Fin n, u (pairToEuc 0 x) i * φ x i) =
    ∫ x : Euc ℝ n, (∑ i : Fin n, nse.initialVelocity x i * φ x i)

/--
  Leray-Hopf weak solutions to the Navier-Stokes equations.

  These are a special class of weak solutions with additional properties that make them
  physically meaningful. Named after Jean Leray and Eberhard Hopf, these solutions
  satisfy an energy inequality that represents the physical principle that energy
  should not increase in a viscous fluid without external forcing.

  Leray-Hopf solutions are the most important class of weak solutions because:
  1. They can be proven to exist globally in time (for any initial data with finite energy)
  2. They satisfy physical energy principles
  3. They are the basis for many modern analytical approaches to the Navier-Stokes equations

  The existence of these solutions was one of the first major breakthroughs in the
  mathematical theory of fluid dynamics, demonstrated by Jean Leray in 1934.
-/

structure LerayHopfSolution {n : ℕ} (nse : NavierStokesEquations n) extends WeakSolution nse where
  /--
    The energy inequality for Leray-Hopf solutions.

    So I like that this inequality expresses a fundamental physical principle: in a viscous fluid,
    the total energy can only decrease over time (in the absence of external forces).

    The inequality states that:

    KE(t) + 2ν∫₀ᵗ Ens(s)ds ≤ KE(0)

    where:
    - KE(t) is the kinetic energy at time t
    - Ens(s) is the enstrophy (squared vorticity) at time s
    - ν is the viscosity coefficient

    Components of the inequality:
    1. Kinetic energy: (1/2)∫|u(t,x)|² dx - represents the total kinetic energy at time t
    2. Viscous dissipation: 2ν∫₀ᵗ∫|∇u(s,x)|² dx ds - represents the cumulative energy
       dissipated by viscous effects up to time t
    3. Initial energy: (1/2)∫|u(0,x)|² dx - the total energy at the initial time

    This inequality is weaker than the energy equality that holds for smooth solutions,
    reflecting the reduced regularity of weak solutions.

    The presence of this inequality distinguishes Leray-Hopf solutions from general weak solutions and provides a selection criterion among the possibly non-unique weak solutions to identify those that are physically meaningful. Again question is do we care about only the physically meaningful solutions?: ) Thats up for debate and what is a good way to find them?
  -/
  energy_inequality : ∀ t ∈ Set.Icc 0 T, kineticEnergy u t +
    2 * nse.nu * ∫ s in Set.Icc 0 t, enstrophy u s ≤ kineticEnergy u 0

end NavierStokes
