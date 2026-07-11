import Problems.NavierStokes.Equations
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.PiL2

open EuclideanSpace MeasureTheory Order NavierStokes

/-!
`ThreeTorus` is implemented as the Mathlib product torus `(ℝ/ℤ)³`.

The PDE operators in the Navier--Stokes files are still written on coordinate lifts `ℝ³` or
`ℝ³ × [0,∞)`. The maps below connect those lifted statements to the actual quotient torus used
for Clay's periodic domain `ℝ³/ℤ³`.
-/

/-- Clay's periodic spatial domain `ℝ³/ℤ³`, as a product of three unit additive circles. -/
def ThreeTorus : Type :=
  UnitAddTorus (Fin 3)

/-- The quotient map from coordinates on `ℝ³` to the torus `(ℝ/ℤ)³`. -/
noncomputable def torus_quotient_map (x : Space3) : ThreeTorus :=
  fun i => (x i : UnitAddCircle)

@[simp] theorem torus_quotient_map_apply (x : Space3) (i : Fin 3) :
    torus_quotient_map x i = (x i : UnitAddCircle) :=
  rfl

/-- Integer coordinates vanish in `ℝ/ℤ`. -/
@[simp] theorem unit_add_circle_int_cast_eq_zero (n : ℤ) :
    ((n : ℝ) : UnitAddCircle) = 0 := by
  simp

/-- The coordinate quotient map is unchanged by integer shifts in any standard basis direction. -/
@[simp] theorem torus_quotient_map_add_int_standard_basis
    (x : Space3) (i : Fin 3) (n : ℤ) :
    torus_quotient_map (x + n • standard_basis (n := 3) i) = torus_quotient_map x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [torus_quotient_map]
  · simp [torus_quotient_map, hji]

/-- The coordinate lift of a function on the quotient torus. -/
noncomputable def torus_lift {α : Type*} (F : ThreeTorus → α) : Space3 → α :=
  fun x => F (torus_quotient_map x)

/-- A coordinate function factors through the quotient torus if it is a torus lift. -/
def factors_through_torus {α : Type*} (f : Space3 → α) : Prop :=
  ∃ F : ThreeTorus → α, f = torus_lift F

/-- Every torus lift factors through the quotient torus. -/
theorem torus_lift_factors_through_torus {α : Type*} (F : ThreeTorus → α) :
    factors_through_torus (torus_lift F) :=
  ⟨F, rfl⟩
