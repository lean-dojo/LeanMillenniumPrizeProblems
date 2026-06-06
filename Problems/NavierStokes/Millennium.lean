import Problems.NavierStokes.MillenniumBoundedDomain

/-!
# Navier–Stokes Millennium problem (Fefferman)

Single entry point for the Clay Navier–Stokes problem statement, following:
`Problems/NavierStokes/references/clay/navierstokes.pdf`.

The Clay write-up (Fefferman) gives four related statements (A)–(D), with (A,C) in the `ℝ³`
setting and (B,D) in the periodic setting. In this repository they are formalized as:
- `MillenniumNSRDomain.FeffermanA` and `MillenniumNSRDomain.FeffermanC`
  (`Problems/NavierStokes/MillenniumRDomain.lean`)
- `MillenniumNS_BoundedDomain.FeffermanB` and `MillenniumNS_BoundedDomain.FeffermanD`
  (`Problems/NavierStokes/MillenniumBoundedDomain.lean`)

The Clay Millennium problem asks for a proof of one of these four statements. We expose the four
formal targets separately below, rather than as a single disjunction.
-/

namespace MillenniumNavierStokes

/-- Fefferman's Clay Millennium problem statements (A)–(D), kept as separate targets. -/
abbrev NavierStokesMillenniumProblem : MillenniumNS_BoundedDomain.FeffermanMillenniumProblems :=
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem

/-- Fefferman's statement (A), existence and smoothness on `ℝ³` with zero force. -/
abbrev FeffermanA : Prop :=
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem.A

/-- Fefferman's statement (B), existence and smoothness in the periodic setting with zero force. -/
abbrev FeffermanB : Prop :=
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem.B

/-- Fefferman's statement (C), breakdown on `ℝ³` with forcing allowed. -/
abbrev FeffermanC : Prop :=
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem.C

/-- Fefferman's statement (D), breakdown in the periodic setting with forcing allowed. -/
abbrev FeffermanD : Prop :=
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem.D

end MillenniumNavierStokes
