import Problems.NavierStokes.MillenniumBoundedDomain

/-!
# Navier–Stokes Millennium problem (Fefferman)

Top-level entry point for the Clay Navier–Stokes problem, following
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

Fefferman's write-up gives four statements.  A solution of the Millennium problem is a sorry-free
proof of **any one** of them:

* (A) `NavierStokesOnR3.SmoothExistence`: existence and smoothness on `ℝ³`, zero force;
* (B) `NavierStokesPeriodic.SmoothExistence`: existence and smoothness on `ℝ³/ℤ³`, zero force;
* (C) `NavierStokesOnR3.Breakdown`: breakdown on `ℝ³`, forcing allowed;
* (D) `NavierStokesPeriodic.Breakdown`: breakdown on `ℝ³/ℤ³`, forcing allowed.

The abbreviations `FeffermanA`–`FeffermanD` below name them.

## Why there is no single target declaration

This file deliberately does **not** define the disjunction `(A) ∨ (B) ∨ (C) ∨ (D)`, nor any other
aggregate of the four cases, and there is no `sorry` placeholder for Navier–Stokes.

The disjunction is a theorem of classical logic with no fluid dynamics in it.  If (A) fails for
some viscosity `ν₀`, the offending initial datum together with the zero force (which satisfies
Fefferman's force hypotheses) witnesses (C) at `ν₀`, and the Navier–Stokes scaling symmetry
`u(x,t) ↦ b·u(x,bt)`, `p(x,t) ↦ b²·p(x,bt)` moves that witness to every viscosity.  A compiled
proof of the disjunction is kept in `Tests/NavierStokes/AggregateIsTrivial.lean`.  Packaging the
four cases as constructors of an inductive `Type` does not help: classical case analysis
(`Classical.propDecidable` together with `dite`) inhabits any such type, see
`Tests/AggregateTargets.lean`.

The same argument shows that Fefferman's four alternatives are exhaustive in ordinary mathematics
as well.  The prize question is *which* of them holds, not *whether* one of them holds, so the
only meaningful formal targets are the four propositions themselves.

History: the aggregate was reported as classically provable in issue #5 (June 2026) and removed;
it was reintroduced in July 2026 and is now removed again.
-/

namespace MillenniumNavierStokes

/-- Fefferman's statement (A): existence and smoothness on `ℝ³` with zero force. -/
abbrev FeffermanA : Prop :=
  NavierStokesOnR3.SmoothExistence

/-- Fefferman's statement (B): existence and smoothness on `ℝ³/ℤ³` with zero force. -/
abbrev FeffermanB : Prop :=
  NavierStokesPeriodic.SmoothExistence

/-- Fefferman's statement (C): breakdown on `ℝ³`, forcing allowed. -/
abbrev FeffermanC : Prop :=
  NavierStokesOnR3.Breakdown

/-- Fefferman's statement (D): breakdown on `ℝ³/ℤ³`, forcing allowed. -/
abbrev FeffermanD : Prop :=
  NavierStokesPeriodic.Breakdown

end MillenniumNavierStokes
