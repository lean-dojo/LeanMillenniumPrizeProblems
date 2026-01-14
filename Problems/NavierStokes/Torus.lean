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

/-- A lightweight model of the 3-torus, implemented as `ℝ³` with “periodic” interpretation. -/
abbrev Torus3 : Type := Euc ℝ 3

/-- Use the Borel σ-algebra on the `Torus3` model. -/
noncomputable instance : MeasurableSpace Torus3 := borel Torus3

/-- `Torus3` is a Borel space (by definition of the model). -/
noncomputable instance : BorelSpace Torus3 := ⟨rfl⟩

/-- Use Lebesgue measure (`volume`) on the `Torus3` model. -/
noncomputable instance : MeasureSpace Torus3 := ⟨volume⟩
