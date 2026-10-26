import Problems.YangMills.LatticeGaugeAction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Four-dimensional periodic lattice gauge testbed

The vertex set is (ℤ/(n+1)ℤ)^4. All four directions and their oriented
elementary plaquettes are fixed here: the proof author cannot substitute an
arbitrary graph or silently switch to two dimensions.

Each link takes values in the *actual* group G, and plaquette holonomies use
its noncommutative multiplication. Gauge invariance is inherited from the
algebraic holonomy theorems.

The lattice regulator is a necessary construction tool, not a continuum
Yang--Mills identification or a mass-gap proof. The class-function weight
must eventually be fixed from a justified representation, with a measure,
renormalization and a proved four-dimensional continuum correspondence.
-/

noncomputable section

namespace YangMills

universe v

/-- Periodic four-dimensional lattice with side length n+1. -/
abbrev PeriodicFourVertex (n : ℕ) := Fin 4 → ZMod (n + 1)

/-- Unit shift in the μ direction. -/
def periodicShift {n : ℕ} (x : PeriodicFourVertex n)
    (μ : Fin 4) : PeriodicFourVertex n :=
  x + Pi.single μ 1

/-- Orthogonal lattice shifts commute, a consequence of the abelian
coordinate lattice, not of the generally noncommutative gauge group. -/
theorem periodicShift_comm {n : ℕ} (x : PeriodicFourVertex n)
    (μ ν : Fin 4) :
    periodicShift (periodicShift x μ) ν =
      periodicShift (periodicShift x ν) μ := by
  unfold periodicShift
  abel

/-- The positively oriented μν plaquette, based at lattice site x. -/
def periodicFourPlaquette {n : ℕ} (x : PeriodicFourVertex n)
    (μ ν : Fin 4) : GaugeWalk (PeriodicFourVertex n) x x :=
  squareGaugeLoop x (periodicShift x μ)
    (periodicShift (periodicShift x μ) ν) (periodicShift x ν)

/-- Exactly the oriented elementary plaquettes with μ < ν in four
dimensions, at every lattice vertex. -/
def periodicFourPlaquettes (n : ℕ) :
    List (ClosedGaugeWalk (PeriodicFourVertex n)) :=
  (Finset.univ : Finset (PeriodicFourVertex n)).toList.flatMap fun x =>
    (Finset.univ : Finset (Fin 4)).toList.flatMap fun μ =>
      ((Finset.univ : Finset (Fin 4)).filter fun ν => μ < ν).toList.map
        fun ν => ⟨x, periodicFourPlaquette x μ ν⟩

/-- The finite four-dimensional group-specific plaquette action. -/
def periodicFourClassAction (n : ℕ)
    (G : CompactSimpleGaugeGroup.{v})
    (classWeight : ConjClasses G.Carrier → ℝ)
    (links : GaugeLinks (PeriodicFourVertex n) G) : ℝ :=
  finiteCentralPlaquetteAction G (periodicFourPlaquettes n) classWeight links

theorem periodicFourClassAction_gauge_invariant (n : ℕ)
    (G : CompactSimpleGaugeGroup.{v})
    (classWeight : ConjClasses G.Carrier → ℝ)
    (h : PeriodicFourVertex n → G.Carrier)
    (links : GaugeLinks (PeriodicFourVertex n) G) :
    periodicFourClassAction n G classWeight (gaugeTransform G h links) =
      periodicFourClassAction n G classWeight links :=
  finiteCentralPlaquetteAction_gauge_invariant G _ classWeight h links

/-- Finite Boltzmann weights, with explicit real coupling.
This is NOT a normalized Haar expectation or a continuum Schwinger function. -/
def periodicFourClassBoltzmann (n : ℕ)
    (G : CompactSimpleGaugeGroup.{v})
    (classWeight : ConjClasses G.Carrier → ℝ)
    (coupling : ℝ)
    (links : GaugeLinks (PeriodicFourVertex n) G) : ℝ :=
  finiteCentralBoltzmannWeight G (periodicFourPlaquettes n)
    classWeight coupling links

theorem periodicFourClassBoltzmann_gauge_invariant (n : ℕ)
    (G : CompactSimpleGaugeGroup.{v})
    (classWeight : ConjClasses G.Carrier → ℝ)
    (coupling : ℝ)
    (h : PeriodicFourVertex n → G.Carrier)
    (links : GaugeLinks (PeriodicFourVertex n) G) :
    periodicFourClassBoltzmann n G classWeight coupling
        (gaugeTransform G h links) =
      periodicFourClassBoltzmann n G classWeight coupling links :=
  finiteCentralBoltzmannWeight_gauge_invariant G _ classWeight coupling h links

end YangMills
