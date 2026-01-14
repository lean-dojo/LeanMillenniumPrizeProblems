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

The Clay Millennium problem asks for a proof of one of these four statements; the combined
statement is `MillenniumNS_BoundedDomain.FeffermanMillenniumProblem`, which we also re-export as
`MillenniumNavierStokes.NavierStokesMillenniumProblem` below.
-/

namespace MillenniumNavierStokes

/-- Fefferman's Clay Millennium problem statement (A)–(D), as a single disjunction. -/
abbrev NavierStokesMillenniumProblem : Prop :=
  MillenniumNS_BoundedDomain.FeffermanMillenniumProblem

end MillenniumNavierStokes

