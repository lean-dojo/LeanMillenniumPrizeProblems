import Problems.NavierStokes.MillenniumBoundedDomain

/-!
# Navier–Stokes Millennium problem (Fefferman)

Top-level statement for Clay Navier--Stokes, following:
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

Fefferman's accepted Clay cases are formalized directly as:
- `NavierStokesOnR3.SmoothExistence`
- `NavierStokesPeriodic.SmoothExistence`
- `NavierStokesOnR3.Breakdown`
- `NavierStokesPeriodic.Breakdown`

This file just packages those four cases into the single public Clay proposition.
-/

namespace MillenniumNavierStokes

/-- Clay's Navier--Stokes statement: prove one of Fefferman's cases (A)--(D). -/
def ClayNavierStokes : Prop :=
  NavierStokesOnR3.SmoothExistence ∨ NavierStokesPeriodic.SmoothExistence ∨
    NavierStokesOnR3.Breakdown ∨ NavierStokesPeriodic.Breakdown

/-- `ClayNavierStokes` is exactly the disjunction of Fefferman's four accepted cases. -/
theorem ClayNavierStokes.iff_cases :
    ClayNavierStokes ↔
      NavierStokesOnR3.SmoothExistence ∨ NavierStokesPeriodic.SmoothExistence ∨
        NavierStokesOnR3.Breakdown ∨ NavierStokesPeriodic.Breakdown :=
  Iff.rfl

/-- Whole-space smooth existence proves the Clay statement. -/
theorem ClayNavierStokes.of_whole_space_smooth_existence
    (h : NavierStokesOnR3.SmoothExistence) :
    ClayNavierStokes :=
  Or.inl h

/-- Periodic smooth existence proves the Clay statement. -/
theorem ClayNavierStokes.of_periodic_smooth_existence
    (h : NavierStokesPeriodic.SmoothExistence) :
    ClayNavierStokes :=
  Or.inr (Or.inl h)

/-- Whole-space breakdown proves the Clay statement. -/
theorem ClayNavierStokes.of_whole_space_breakdown
    (h : NavierStokesOnR3.Breakdown) :
    ClayNavierStokes :=
  Or.inr (Or.inr (Or.inl h))

/-- Periodic breakdown proves the Clay statement. -/
theorem ClayNavierStokes.of_periodic_breakdown
    (h : NavierStokesPeriodic.Breakdown) :
    ClayNavierStokes :=
  Or.inr (Or.inr (Or.inr h))

/-- Case analysis on `ClayNavierStokes` using the four accepted Fefferman cases directly. -/
theorem ClayNavierStokes.elim
    {P : Prop} (h : ClayNavierStokes)
    (hA : NavierStokesOnR3.SmoothExistence → P)
    (hB : NavierStokesPeriodic.SmoothExistence → P)
    (hC : NavierStokesOnR3.Breakdown → P)
    (hD : NavierStokesPeriodic.Breakdown → P) :
    P := by
  rcases h with hA' | hBCD
  · exact hA hA'
  rcases hBCD with hB' | hCD
  · exact hB hB'
  rcases hCD with hC' | hD'
  · exact hC hC'
  · exact hD hD'

/-!
## Main theorem

This final theorem records the Navier--Stokes alternatives directly. Replace the placeholder proof
with a proof of any one accepted Clay case.
-/

/--
Clay Millennium Prize target for Navier--Stokes.

Prove one accepted Clay case, then finish via
`ClayNavierStokes.of_whole_space_smooth_existence`,
`ClayNavierStokes.of_periodic_smooth_existence`,
`ClayNavierStokes.of_whole_space_breakdown`, or
`ClayNavierStokes.of_periodic_breakdown`.
-/
theorem clay_prize_navier_stokes :
    ClayNavierStokes := by
  sorry

end MillenniumNavierStokes
