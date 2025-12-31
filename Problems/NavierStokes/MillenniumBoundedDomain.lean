import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes
import Problems.NavierStokes.MillenniumRDomain
import Problems.NavierStokes.Torus

namespace MillenniumNS_BoundedDomain

set_option diagnostics true
set_option diagnostics.threshold 5000

open EuclideanSpace MeasureTheory Order NavierStokes

/--
  The 3-dimensional torus T³ = R³/Z³.

  This represents a bounded periodic domain where:
  - Points are identified modulo 1 in each coordinate direction
  - Functions defined on this domain are periodic with period 1

  Using the torus allows us to work in a bounded domain while avoiding
  boundary conditions, providing a simpler setting for studying the
  core mathematical difficulties of the Navier-Stokes equations.

  We will be using the instance defined in `Problems.NavierStokes.Torus` file. Please check the file for more details.

  A function is periodic on the torus if it has period 1 in each coordinate.
-/
def IsPeriodic {α : Type} (f : Euc ℝ 3 → α) : Prop :=
  ∀ (x : Euc ℝ 3) (i : Fin 3) (n : ℤ),
    let e_i : Euc ℝ 3 := standardBasis (n := 3) i
    f (x + n • e_i) = f x

/--
  The Millennium Problem statement for Navier-Stokes equations on the torus T³.

  Now one of my friends who works on PDE's told me to also give the equivalent formulation that restricts the problem to a bounded domain (the 3D torus), which eliminates issues related to behavior at infinity while having the same challenges.

  To me intuitively the periodic boundary conditions on the torus simplifies the analysis by removing
  physical boundaries while still allowing for complex fluid behavior such as turbulence.
-/
structure MillenniumProblemBoundedDomain where
  /--
    Given smooth periodic initial data with finite energy.
    The initial velocity field is defined on the 3D torus.
  -/
  initialVelocity : Torus3 → Euc ℝ 3

  /--
    The initial velocity is infinitely differentiable (smooth).
  -/
  initialVelocity_smooth : ContDiff ℝ ⊤ initialVelocity

  /--
    The initial velocity is periodic with period 1 in each coordinate direction.

    This means for each unit vector e_i and any integer n:
    v(x + n·e_i) = v(x)
  -/
  initialVelocity_periodic : IsPeriodic initialVelocity

  /--
    The initial velocity has finite energy on the torus.

    Due to the bounded domain, this integral is automatically finite for
    continuous functions, but we include it for consistency with the
    original formulation.
  -/
  initialVelocity_finite_energy : HasFiniteIntegral (fun x => ∑ i : Fin 3, (initialVelocity x i)^2)

  /--
    The initial velocity is divergence free (incompressible).
  -/
  initialVelocity_div_free : ∀ x, ∑ i : Fin 3, partialDeriv i (λ y => initialVelocity y i) x = 0

  /--
    Mean-zero condition: the average velocity over the torus is zero.

    This additional condition is often imposed in the periodic case to
    ensure uniqueness of solutions.
  -/
  initialVelocity_mean_zero : ∫ x : Torus3, initialVelocity x = 0

  /-- Viscosity coefficient (must be positive) -/
  nu : ℝ

  /-- Viscosity is positive - a physical requirement -/
  nu_pos : nu > 0

  /-- External force field acting on the fluid -/
  f : ForceField 3

  /--
    The Navier-Stokes equations with this initial data on the torus.
  -/
  nse : NavierStokesEquations 3 := {
    nu := nu,                            -- Kinematic viscosity (from parameter)
    f := f,                              -- External force field
    nu_pos := nu_pos,                    -- Proof that viscosity is positive
    initialVelocity := initialVelocity,  -- Initial velocity field
    initialDivergenceFree := initialVelocity_div_free  -- Proof of incompressibility
  }

/--
  A periodic solution to the Navier-Stokes equations on the torus.

  This extends the standard solution concept with periodicity requirements
  for both the velocity and pressure fields.
-/
structure PeriodicSolution (nse : NavierStokesEquations 3) extends Solution nse where
  /-- The velocity field is periodic in space -/
  velocity_periodic : ∀ t ∈ Set.Icc 0 T, IsPeriodic (fun x => u (pairToEuc t x))

  /-- The pressure field is periodic in space -/
  pressure_periodic : ∀ t ∈ Set.Icc 0 T, IsPeriodic (fun x => p (pairToEuc t x))

  /-- The velocity field has zero mean on the torus at all times -/
  velocity_mean_zero : ∀ t ∈ Set.Icc 0 T, ∫ x : Torus3, u (pairToEuc t x) = 0

/--
  A smooth periodic solution to the Navier-Stokes equations on the torus.

  This combines the requirements for smoothness with the periodicity
  conditions needed for the torus domain.
-/
structure SmoothPeriodicSolution (nse : NavierStokesEquations 3)
    extends PeriodicSolution nse, SmoothSolution nse where

/--
  # The energy bound for solutions on the torus.

  One of the key aspects of the bounded domain formulation is that the
  total kinetic energy must remain bounded for all time:

  ∫(T³) |v(x,t)|² dx < E for all t ≥ 0

  This condition is included in the problem statement and is essential
  for physically relevant solutions.
-/
def HasBoundedEnergy (nse : NavierStokesEquations 3) (sol : PeriodicSolution nse) : Prop :=
  ∃ E : ℝ, E > 0 ∧ ∀ t ∈ Set.Icc 0 sol.T,
    ∫ x : Torus3, (∑ i : Fin 3, (sol.u (pairToEuc t x) i)^2) < E

/--
  # The existence part of the Millennium Problem on the bounded domain.

  Again like before this asks does there exists a smooth periodic solution to the
  Navier-Stokes equations on the torus that extends for all time.
-/
def ExistenceOfSmoothPeriodicSolution (problem : MillenniumProblemBoundedDomain) : Prop :=
  ∃ sol : SmoothPeriodicSolution problem.nse, sol.T = (⊤ : WithTop ℝ)

/--
  # The breakdown of smooth periodic solutions part of the Millennium Problem.

  Again like before this asks whether solutions on the torus must develop singularities
  in finite time, despite the bounded domain.
-/
def BreakdownOfSmoothPeriodicSolution (problem : MillenniumProblemBoundedDomain) : Prop :=
  ∃ sol : SmoothPeriodicSolution problem.nse, sol.T < (⊤ : WithTop ℝ) ∧
    ∀ sol' : SmoothPeriodicSolution problem.nse, sol'.T ≤ sol.T

/--
  # The Millennium Problem Statement for the bounded domain case.

  Again the problem is to determine whether exactly one of the following statements is true:

 1. Either for ALL valid initial conditions (smooth, divergence-free, finite energy),
     smooth periodic solutions exist for all time (global existence)
  2. OR there EXISTS at least one valid initial condition for which
     no smooth periodic solution can exist beyond some finite time (finite-time blowup)

  This periodic formulation is mathematically equivalent to the original problem.
-/
def MillenniumProblemBoundedDomainStatement : Prop :=
  (∀ problem : MillenniumProblemBoundedDomain, ExistenceOfSmoothPeriodicSolution problem) ∨
  (∃ problem : MillenniumProblemBoundedDomain, BreakdownOfSmoothPeriodicSolution problem)

end MillenniumNS_BoundedDomain
