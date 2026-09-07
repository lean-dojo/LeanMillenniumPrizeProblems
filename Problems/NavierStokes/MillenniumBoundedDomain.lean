import Problems.NavierStokes.Equations
import Problems.NavierStokes.MillenniumRDomain
import Problems.NavierStokes.Torus

namespace NavierStokesPeriodic

open EuclideanSpace MeasureTheory Order NavierStokes
open NavierStokesOnR3
open scoped BigOperators

/-!
# Navier–Stokes Millennium problem: periodic setting (`ℝ³/ℤ³`)

This file states Fefferman's parts (B) and (D) from the Clay problem description
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

The periodic hypotheses are numbered (8)–(11) in the PDF.
-/

/-- Periodicity in each coordinate direction with period `1`. -/
def IsPeriodic {α : Type} (f : Space3 → α) : Prop :=
  ∀ (x : Space3) (i : Fin 3) (n : ℤ),
    let e_i : Space3 := standard_basis (n := 3) i
    f (x + n • e_i) = f x

/-- A function on the quotient torus pulls back to a `ℤ³`-periodic coordinate function. -/
theorem IsPeriodic.torus_lift {α : Type} (F : ThreeTorus → α) :
    IsPeriodic (torus_lift F) := by
  intro x i n
  change F (torus_quotient_map (x + n • standard_basis (n := 3) i)) = F (torus_quotient_map x)
  rw [torus_quotient_map_add_int_standard_basis]

/-- Spatial periodicity (in the `ℝ³` directions) for a spacetime function `ℝ⁴ → _`. -/
def IsSpatiallyPeriodicForce (f : ForceField 3) : Prop :=
  ∀ (x : Spacetime3), 0 ≤ x 0 → ∀ (i : Fin 3) (n : ℤ),
    let e_i : Spacetime3 := standard_basis (n := 4) i.succ
    f (x + n • e_i) = f x

/-- Spatial periodicity (in the `ℝ³` directions) for a pressure field `ℝ⁴ → ℝ`. -/
def IsSpatiallyPeriodicPressure (p : PressureField 3) : Prop :=
  ∀ (x : Spacetime3), 0 ≤ x 0 → ∀ (i : Fin 3) (n : ℤ),
    let e_i : Spacetime3 := standard_basis (n := 4) i.succ
    p (x + n • e_i) = p x

/-! ## Fefferman's conditions (8)–(11) -/

/--
Fefferman's periodicity condition (8) for an initial velocity field on `ℝ³`.
-/
def PeriodicInitial (u₀ : Space3 → Space3) : Prop :=
  IsPeriodic u₀

/-- Fefferman's periodicity condition (8) for a force field on `ℝ³ × [0,∞)`. -/
def PeriodicForce (f : ForceField 3) : Prop :=
  IsSpatiallyPeriodicForce f

/-- The zero force is spatially periodic. -/
theorem zero_force_periodic :
    PeriodicForce (fun _ : Spacetime3 => (0 : Space3)) := by
  intro x _hx i n
  rfl

/--
Fefferman's time-decay condition (9) for the force in the periodic setting.

This is the same mixed-derivative expression as in (5), but the weight depends only on time.
-/
def PeriodicForceDecay (f : ForceField 3) : Prop :=
  force_smooth_on_global_spacetime_domain f ∧
    ∀ (α : List (Fin 3)) (m K : ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ x : Spacetime3, 0 ≤ x 0 →
          ‖spacetime_derivative_vector f α m x‖ ≤ C / (1 + |x 0|) ^ K

/-- The zero force satisfies Fefferman's periodic-setting force decay condition (9). -/
theorem zero_force_periodic_decay :
    PeriodicForceDecay (fun _ : Spacetime3 => (0 : Space3)) := by
  refine ⟨?_, ?_⟩
  · change ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Spacetime3 => (0 : Space3)) (global_spacetime_domain 3)
    fun_prop
  intro α m K
  refine ⟨1, by norm_num, ?_⟩
  intro x hx_nonneg
  rw [spacetime_derivative_vector_zero, norm_zero]
  positivity

/--
Fefferman's periodicity condition (10) in the periodic setting.

The main text states periodicity for the velocity field `u` in (10); the local PDF errata says
pressure periodicity should also be made explicit in the periodic setting.
-/
def PeriodicSolutionFields (u : VelocityField 3) (p : PressureField 3) : Prop :=
  (∀ t : ℝ, 0 ≤ t → IsPeriodic (fun x : Space3 => u (spacetime_point t x))) ∧
    IsSpatiallyPeriodicPressure p

/-- Fefferman's smoothness condition (11) for a solution `(p,u)` on `ℝ³ × [0,∞)`. -/
def SmoothPeriodicSolutionFields (u : VelocityField 3) (p : PressureField 3) : Prop :=
  velocity_smooth_on_global_spacetime_domain u ∧ pressure_smooth_on_global_spacetime_domain p

/-- A `GlobalSmoothSolution` automatically satisfies Fefferman's smoothness condition (11). -/
theorem GlobalSmoothSolution.smooth_periodic_fields {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) : SmoothPeriodicSolutionFields sol.velocity sol.pressure :=
  ⟨sol.velocity_smooth, sol.pressure_smooth⟩

/-! ## Fefferman's statements (B) and (D) -/

/--
Fefferman's statement (B): Existence and smoothness in the periodic setting, with `f ≡ 0`.
-/
def SmoothExistence : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : Space3 → Space3),
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    PeriodicInitial u₀ →
      ∀ hdiv : DivergenceFreeInitial u₀,
      ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
        PeriodicSolutionFields sol.velocity sol.pressure ∧
          SmoothPeriodicSolutionFields sol.velocity sol.pressure

/--
In statement (B), condition (11) is already part of `GlobalSmoothSolution`; the substantive extra
solution-side condition is periodicity (10).
-/
theorem SmoothExistence.iff_periodic_fields :
    SmoothExistence ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0) (u₀ : Space3 → Space3),
        ContDiff ℝ (⊤ : ℕ∞) u₀ →
        PeriodicInitial u₀ →
        ∀ hdiv : DivergenceFreeInitial u₀,
          ∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv (fun _ => 0)),
            PeriodicSolutionFields sol.velocity sol.pressure := by
  constructor
  · intro hB ν ν_pos u₀ hSmooth hPeriodic hdiv
    rcases hB ν ν_pos u₀ hSmooth hPeriodic hdiv with ⟨sol, h10, _h11⟩
    exact ⟨sol, h10⟩
  · intro hB ν ν_pos u₀ hSmooth hPeriodic hdiv
    rcases hB ν ν_pos u₀ hSmooth hPeriodic hdiv with ⟨sol, h10⟩
    exact ⟨sol, h10, GlobalSmoothSolution.smooth_periodic_fields sol⟩

/--
Fefferman's statement (D): Breakdown in the periodic setting (forcing allowed).
-/
def Breakdown : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0),
  ∃ (u₀ : Space3 → Space3) (f : ForceField 3),
    ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
    PeriodicInitial u₀ ∧
    DivergenceFreeInitial u₀ ∧
    PeriodicForce f ∧
    PeriodicForceDecay f ∧
      ∀ hdiv : DivergenceFreeInitial u₀,
        ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv f),
              PeriodicSolutionFields sol.velocity sol.pressure ∧
                SmoothPeriodicSolutionFields sol.velocity sol.pressure)

/--
In statement (D), condition (11) is automatic for `GlobalSmoothSolution`, so the nonexistence
clause can equivalently rule out global smooth periodic solutions.
-/
theorem Breakdown.iff_no_periodic_solution :
    Breakdown ↔
      ∀ (ν : ℝ) (ν_pos : ν > 0),
      ∃ (u₀ : Space3 → Space3) (f : ForceField 3),
        ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
        PeriodicInitial u₀ ∧
        DivergenceFreeInitial u₀ ∧
        PeriodicForce f ∧
        PeriodicForceDecay f ∧
          ∀ hdiv : DivergenceFreeInitial u₀,
            ¬ (∃ sol : GlobalSmoothSolution (equations ν ν_pos u₀ hdiv f),
                  PeriodicSolutionFields sol.velocity sol.pressure) := by
  constructor
  · intro hD ν ν_pos
    rcases hD ν ν_pos with ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, hNo⟩
    refine ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, h10⟩
    exact ⟨sol, h10, GlobalSmoothSolution.smooth_periodic_fields sol⟩
  · intro hD ν ν_pos
    rcases hD ν ν_pos with ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, hNo⟩
    refine ⟨u₀, f, hSmooth, hPeriodic₀, hdiv₀, hPeriodicf, h9, ?_⟩
    intro hdiv hExists
    apply hNo hdiv
    rcases hExists with ⟨sol, h10, _h11⟩
    exact ⟨sol, h10⟩

end NavierStokesPeriodic
