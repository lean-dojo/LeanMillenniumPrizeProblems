import Problems.YangMills.GaugeHolonomy
import Mathlib.Analysis.SpecialFunctions.Exp

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Gauge-invariant finite link actions (not a continuum Yang--Mills measure)

A plaquette is an actual closed oriented path in vertices. A conjugacy-class
function on the *specific gauge group G* turns its holonomy into a scalar
lattice term. Summing over finitely many plaquettes and taking a Boltzmann
weight are mathematically defined and gauge invariant.

This layer deliberately does not choose a preferred representation/character,
define a Yang--Mills continuum limit or claim the resulting lattice measure
equals a quantum field theory. Those are essential missing proof obligations.

These definitions may be replaced by the official Physlib lattice-QFT APIs
when its roadmap implements gauge-invariant lattice actions and measures.
A replacement must preserve the class-function generality used here.
-/

noncomputable section

namespace YangMills

universe u v

/-- A closed oriented walk with a dependent base vertex. -/
abbrev ClosedGaugeWalk (V : Type u) :=
  Σ a : V, GaugeWalk V a a

/-- Any chosen real class function induces a concrete finite link action.
A future Wilson regulator must fix the class function from a justified
representation/normalization, not let the proof author redefine the theory. -/
def finiteCentralPlaquetteAction {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (plaquettes : List (ClosedGaugeWalk V))
    (classWeight : ConjClasses G.Carrier → ℝ)
    (links : GaugeLinks V G) : ℝ :=
  (plaquettes.map fun p => classWeight (wilsonConjugacyClass G links p.2)).sum

/-- Every central plaquette action is gauge-invariant, for the actual
(possibly noncommutative) multiplication law of the given gauge group. -/
theorem finiteCentralPlaquetteAction_gauge_invariant {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (plaquettes : List (ClosedGaugeWalk V))
    (classWeight : ConjClasses G.Carrier → ℝ)
    (h : V → G.Carrier) (links : GaugeLinks V G) :
    finiteCentralPlaquetteAction G plaquettes classWeight
        (gaugeTransform G h links) =
      finiteCentralPlaquetteAction G plaquettes classWeight links := by
  simp [finiteCentralPlaquetteAction,
    wilsonConjugacyClass_gauge_invariant]

/-- A finite formal Boltzmann weight for a chosen class function.
A full continuum construction still needs a canonical representation,
Haar integration, renormalization and a justified limit. -/
def finiteCentralBoltzmannWeight {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (plaquettes : List (ClosedGaugeWalk V))
    (classWeight : ConjClasses G.Carrier → ℝ)
    (coupling : ℝ) (links : GaugeLinks V G) : ℝ :=
  Real.exp (-(coupling * finiteCentralPlaquetteAction
      G plaquettes classWeight links))

theorem finiteCentralBoltzmannWeight_gauge_invariant {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (plaquettes : List (ClosedGaugeWalk V))
    (classWeight : ConjClasses G.Carrier → ℝ)
    (coupling : ℝ) (h : V → G.Carrier)
    (links : GaugeLinks V G) :
    finiteCentralBoltzmannWeight G plaquettes classWeight coupling
        (gaugeTransform G h links) =
      finiteCentralBoltzmannWeight G plaquettes classWeight coupling links := by
  simp [finiteCentralBoltzmannWeight,
    finiteCentralPlaquetteAction_gauge_invariant]

end YangMills
