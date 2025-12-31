import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes
import Problems.NavierStokes.MillenniumRDomain
import Mathlib.Analysis.InnerProductSpace.PiL2

open EuclideanSpace MeasureTheory Order NavierStokes

/-!
`Torus3` is currently modeled as `ℝ³` (`Euc ℝ 3`) together with the *intended interpretation*
that points are identified modulo `ℤ³`.

This is enough for a clean statement of “periodic” Navier–Stokes on a bounded domain without
introducing additional quotient / Haar-measure infrastructure.
-/

abbrev Torus3 : Type := Euc ℝ 3

noncomputable instance : MeasurableSpace Torus3 := borel Torus3

noncomputable instance : BorelSpace Torus3 := ⟨rfl⟩

noncomputable instance : MeasureSpace Torus3 := ⟨volume⟩
