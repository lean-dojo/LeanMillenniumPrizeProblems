import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes
import Problems.NavierStokes.MillenniumRDomain
import Problems.NavierStokes.Torus

namespace MillenniumNS_BoundedDomain

open EuclideanSpace MeasureTheory Order NavierStokes
open MillenniumNSRDomain
open scoped BigOperators

/-!
# Navier–Stokes Millennium problem: periodic setting (`ℝ³/ℤ³`)

This file states Fefferman's parts (B) and (D) from the Clay problem description
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

The periodic hypotheses are numbered (8)–(11) in the PDF.
-/

/-- Periodicity in each coordinate direction with period `1`. -/
def IsPeriodic {α : Type} (f : Euc ℝ 3 → α) : Prop :=
  ∀ (x : Euc ℝ 3) (i : Fin 3) (n : ℤ),
    let e_i : Euc ℝ 3 := standardBasis (n := 3) i
    f (x + n • e_i) = f x

/-- Spatial periodicity (in the `ℝ³` directions) for a spacetime function `ℝ⁴ → _`. -/
def IsSpatiallyPeriodicForce (f : ForceField 3) : Prop :=
  ∀ (x : Euc ℝ 4) (i : Fin 3) (n : ℤ),
    let e_i : Euc ℝ 4 := standardBasis (n := 4) i.succ
    f (x + n • e_i) = f x

/-! ## Fefferman's conditions (8)–(11) -/

/--
Fefferman's periodicity condition (8) for an initial velocity field on `ℝ³`.
-/
def FeffermanCond8_initial (u₀ : Euc ℝ 3 → Euc ℝ 3) : Prop :=
  IsPeriodic u₀

/-- Fefferman's periodicity condition (8) for a force field on `ℝ³ × [0,∞)`. -/
def FeffermanCond8_force (f : ForceField 3) : Prop :=
  IsSpatiallyPeriodicForce f

/--
Fefferman's time-decay condition (9) for the force in the periodic setting.

This is the same mixed-derivative expression as in (5), but the weight depends only on time.
-/
def FeffermanCond9 (f : ForceField 3) : Prop :=
  ContDiff ℝ ⊤ f ∧
    ∀ (α : List (Fin 3)) (m K : ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ x : Euc ℝ 4, 0 ≤ x 0 →
          ‖spaceTimeDerivVec f α m x‖ ≤ C / (1 + |x 0|) ^ K

/--
Fefferman's periodicity condition (10) in the periodic setting.

The Clay PDF states periodicity for `u` in (10). The errata page adds that `p` should also be
periodic in the spatial variables.
-/
def FeffermanCond10 (u : VelocityField 3) (p : PressureField 3) : Prop :=
  (∀ t : ℝ, 0 ≤ t → IsPeriodic (fun x : Euc ℝ 3 => u (pairToEuc t x))) ∧
    (∀ t : ℝ, 0 ≤ t → IsPeriodic (fun x : Euc ℝ 3 => p (pairToEuc t x)))

/-- Fefferman's smoothness condition (11) for a solution `(p,u)` (same as (6)). -/
def FeffermanCond11 (u : VelocityField 3) (p : PressureField 3) : Prop :=
  ContDiff ℝ ⊤ u ∧ ContDiff ℝ ⊤ p

/-! ## Fefferman's statements (B) and (D) -/

/--
Fefferman's statement (B): Existence and smoothness in the periodic setting, with `f ≡ 0`.
-/
def FeffermanB : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : Euc ℝ 3 → Euc ℝ 3),
    ContDiff ℝ ⊤ u₀ →
    FeffermanCond8_initial u₀ →
    ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (nseR3 ν ν_pos u₀ hdiv (fun _ => 0)),
        FeffermanCond10 sol.u sol.p

/--
Fefferman's statement (D): Breakdown in the periodic setting (forcing allowed).
-/
def FeffermanD : Prop :=
  ∃ (ν : ℝ) (ν_pos : ν > 0) (u₀ : Euc ℝ 3 → Euc ℝ 3) (f : ForceField 3),
    ContDiff ℝ ⊤ u₀ ∧
    FeffermanCond8_initial u₀ ∧
    DivergenceFreeInitial u₀ ∧
    FeffermanCond8_force f ∧
    FeffermanCond9 f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (nseR3 ν ν_pos u₀ hdiv f),
              FeffermanCond10 sol.u sol.p)

/--
The four Fefferman alternatives appearing in Clay's Navier--Stokes problem statement.

We keep these as separate targets. Assembling the `ℝ³` alternatives into a single proposition
`FeffermanA ∨ FeffermanC` is classically too weak in this formalization: if (A) fails, the
zero-force counterexample already satisfies the forcing hypotheses in (C).
-/
structure FeffermanMillenniumProblems where
  /-- Fefferman's statement (A), existence and smoothness on `ℝ³` with zero force. -/
  A : Prop := MillenniumNSRDomain.FeffermanA
  /-- Fefferman's statement (B), existence and smoothness in the periodic setting with zero force. -/
  B : Prop := FeffermanB
  /-- Fefferman's statement (C), breakdown on `ℝ³` with forcing allowed. -/
  C : Prop := MillenniumNSRDomain.FeffermanC
  /-- Fefferman's statement (D), breakdown in the periodic setting with forcing allowed. -/
  D : Prop := FeffermanD

/-- The separated Navier--Stokes Millennium problem targets. -/
def FeffermanMillenniumProblem : FeffermanMillenniumProblems := {}

end MillenniumNS_BoundedDomain
