import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes

namespace MillenniumNSRDomain

open EuclideanSpace MeasureTheory Order NavierStokes


/--
  # The Millennium Problem statement for Navier-Stokes equations in 3D on the full domain!

  Again this is my understanding of the problem and the statement plus has been verified by some
  Analysis graduate students.

  The Clay Mathematics Institute Millennium Prize Problem on
  Navier-Stokes equations, which asks for either a proof of existence of
  smooth solutions for all time or a proof of blow-up (breakdown) of solutions.

  The Navier-Stokes equations model the motion of incompressible fluid flows,
  and despite their widespread use in physics and engineering, the question of
  whether their solutions remain smooth for all time remains open.
-/
structure MillenniumProblem where
  /--
    Given smooth initial data with finite energy.
    The initial velocity field is a function from 3D space to 3D vectors.
  -/
  initialVelocity : Euc ℝ 3 → Euc ℝ 3

  /--
    The initial velocity is infinitely differentiable (smooth).
    This is represented by ContDiff ℝ ⊤, where ⊤ indicates infinite differentiability.
  -/
  initialVelocity_smooth : ContDiff ℝ ⊤ initialVelocity

  /--
    The initial velocity has finite energy.
    This is a physical requirement ensuring the total kinetic energy of the fluid
    is finite, which is measured by the L² norm of the velocity field.
  -/
  initialVelocity_finite_energy : HasFiniteIntegral (fun x => ∑ i : Fin 3, (initialVelocity x i)^2)

  /--
    The initial velocity is divergence free.
    This condition represents the incompressibility of the fluid,
    mathematically expressed as ∇⋅v = 0. It means the fluid density
    remains constant as it flows.
  -/
  initialVelocity_div_free : ∀ x, ∑ i : Fin 3, partialDeriv i (λ y => initialVelocity y i) x = 0


  /-- Viscosity coefficient (must be positive) -/
  nu : ℝ

  /-- Viscosity is positive - a physical requirement -/
  nu_pos : nu > 0

  /-- External force field acting on the fluid -/
  f : ForceField 3

  /--
    The Navier-Stokes equations with this initial data.

    We set up a specific instance of the Navier-Stokes system with:
    - Viscosity (nu) = 1 (normalized)
    - No external forces (f = 0)
    - Our specified initial velocity field

    These equations represent the fundamental laws of fluid motion,
    combining Newton's second law with the assumption of constant density.
  -/
  nse : NavierStokesEquations 3 := {
    nu := nu,                            -- Kinematic viscosity (from parameter)
    f := f,                              -- External force field
    nu_pos := nu_pos,                    -- Proof that viscosity is positive
    initialVelocity := initialVelocity,  -- Initial velocity field
    initialDivergenceFree := initialVelocity_div_free  -- Proof of incompressibility
  }

/--
  # The existence part of the Millennium Problem.

  Now the first possible resolution to the Millennium Problem:
  that there exists a globally defined smooth solution to the Navier-Stokes equations
  that extends for all time (t ∈ [0,∞)).

  In mathematical terms, this means there is a velocity field that:
  - Satisfies the Navier-Stokes equations at every point in space and time
  - Remains smooth (infinitely differentiable) for all time
  - Never develops singularities or discontinuities

  Where ⊤ is the top element (infinity) in the WithTop ℝ type, representing unbounded time.
-/
def ExistenceOfSmoothSolution (problem : MillenniumProblem) : Prop :=
  ∃ sol : SmoothSolution problem.nse, sol.T = (⊤ : WithTop ℝ)

/--
  # The breakdown of smooth solutions part of the Millennium Problem.

  Now the second possible resolution to the Millennium Problem:
  that there exists a maximal time T < ∞ beyond which smooth solutions cannot be extended.

  This corresponds to the formation of a singularity or "blowup" where:
  - Some quantity (like velocity or its derivatives) becomes unbounded
  - The solution loses regularity (smoothness)
  - Physical quantities like energy may concentrate in infinitesimal regions

  The second part (∀ sol'...) ensures T is truly the maximal possible time,
  meaning no smooth solution can exist beyond this critical time.
-/
def BreakdownOfSmoothSolution (problem : MillenniumProblem) : Prop :=
  ∃ sol : SmoothSolution problem.nse, sol.T < (⊤ : WithTop ℝ) ∧
    ∀ sol' : SmoothSolution problem.nse, sol'.T ≤ sol.T

/--
  # The Millennium Problem Statement: The mathematical dichotomy.

  Okay so basically the statement says that exactly one of the two possibilities must occur:

  1. Either for ALL valid initial conditions (smooth, divergence-free, finite energy),
     smooth solutions exist for all time (global existence)
  2. OR there EXISTS at least one valid initial condition for which
     no smooth solution can exist beyond some finite time (finite-time blowup)
-/
def MillenniumProblemStatement : Prop :=
  (∀ problem : MillenniumProblem, ExistenceOfSmoothSolution problem) ∨
  (∃ problem : MillenniumProblem, BreakdownOfSmoothSolution problem)

end MillenniumNSRDomain
