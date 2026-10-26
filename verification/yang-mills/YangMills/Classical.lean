import YangMills.GaugeGroup
import YangMills.QFT.Spacetime

/-!
# Classical data from Jaffe–Witten §1

These are concrete classical definitions, not a claim that a QFT quantizes them.
The missing quantum/classical identification is recorded in README.md.
The connection is written in a global trivialization on ℝ⁴.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace YangMills

-- Use the model norm only for differentiation on this finite-dimensional
-- tangent space. The underlying topology is the existing tangent topology.
local instance (G : CompactSimpleGaugeGroup) : NormedAddCommGroup G.Algebra :=
  inferInstanceAs (NormedAddCommGroup (Fin G.dimension → ℝ))

local instance (G : CompactSimpleGaugeGroup) : NormedSpace ℝ G.Algebra :=
  inferInstanceAs (NormedSpace ℝ (Fin G.dimension → ℝ))

/-- An invariant positive quadratic form on the actual tangent Lie algebra.
This supplies the invariant trace convention in the classical action. -/
structure InvariantForm (G : CompactSimpleGaugeGroup) where
  bilinear : G.Algebra →ₗ[ℝ] G.Algebra →ₗ[ℝ] ℝ
  symmetric : ∀ X Y, bilinear X Y = bilinear Y X
  positive : ∀ X, X ≠ 0 → 0 < bilinear X X
  invariant : ∀ X Y Z : G.Algebra,
    bilinear ⁅X, Y⁆ Z + bilinear Y ⁅X, Z⁆ = 0

/-- A smooth gauge potential, with four Lie-algebra-valued components. -/
structure Connection (G : CompactSimpleGaugeGroup) where
  potential : Spacetime → Fin 4 → G.Algebra
  smooth : ContDiff ℝ ∞ potential

namespace Connection
variable {G : CompactSimpleGaugeGroup}

/-- ∂μ applied to a Lie-algebra-valued field. -/
def partialDerivative (f : Spacetime → G.Algebra) (μ : Fin 4) (x : Spacetime) : G.Algebra :=
  fderiv ℝ f x (Pi.single μ 1)

/-- Fμν = ∂μ Aν - ∂ν Aμ + [Aμ,Aν]. -/
def curvature (A : Connection G) (x : Spacetime) (μ ν : Fin 4) : G.Algebra :=
  partialDerivative (fun y => A.potential y ν) μ x -
    partialDerivative (fun y => A.potential y μ) ν x + ⁅A.potential x μ, A.potential x ν⁆

/-- Dμ f = ∂μ f + [Aμ,f]. Iteration gives the covariant derivatives
appearing in the local observables of §4. -/
def covariantDerivative (A : Connection G) (f : Spacetime → G.Algebra)
    (μ : Fin 4) (x : Spacetime) : G.Algebra :=
  partialDerivative f μ x + ⁅A.potential x μ, f x⁆

/-- The Euclidean density Tr(F ∧ ⋆F), using μ < ν to count each independent
2-form component once. The invariant form fixes the trace normalization. -/
def actionDensity (A : Connection G) (B : InvariantForm G) (x : Spacetime) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    if μ < ν then B.bilinear (A.curvature x μ ν) (A.curvature x μ ν) else 0

/-- Finiteness must be checked before interpreting the totalized integral. -/
def HasFiniteAction (A : Connection G) (B : InvariantForm G) : Prop :=
  Integrable (A.actionDensity B)

/-- Euclidean action with the normalization used in §1. -/
def euclideanAction (A : Connection G) (B : InvariantForm G)
    (g : ℝ) (_positive : 0 < g) (_finite : A.HasFiniteAction B) : ℝ :=
  (1 / (4 * g ^ 2)) * ∫ x : Spacetime, A.actionDensity B x

end Connection
end YangMills
