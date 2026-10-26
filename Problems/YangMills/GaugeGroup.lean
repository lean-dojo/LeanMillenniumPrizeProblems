import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Algebra.Lie.Semisimple.Defs

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# The gauge-group quantifier in §4

The group has an actual finite-dimensional real smooth manifold structure.
Simplicity means simplicity of its tangent Lie algebra, not simplicity as
an abstract group. Finite central subgroups are therefore allowed.
We use the connected compact Lie group convention.

This gauge-group interface may be replaced by an official Physlib interface
when one covers all compact connected simple Lie groups with the same hypotheses.
-/

noncomputable section
open scoped Manifold ContDiff
namespace YangMills

universe u

structure CompactSimpleGaugeGroup where
  Carrier : Type u
  dimension : ℕ
  [group : Group Carrier]
  [topology : TopologicalSpace Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [charted : ChartedSpace (Fin dimension → ℝ) Carrier]
  [smooth : IsManifold (𝓘(ℝ, Fin dimension → ℝ)) ∞ Carrier]
  [lie : LieGroup (𝓘(ℝ, Fin dimension → ℝ)) ∞ Carrier]
  /-- The finite smoothness instance used by mathlib's tangent Lie bracket;
  this is a redundant consequence of smoothness, retained explicitly because
  `minSmoothness` is irreducible in the pinned mathlib version. -/
  [lieThree : LieGroup (𝓘(ℝ, Fin dimension → ℝ)) (minSmoothness ℝ 3) Carrier]
  [compact : CompactSpace Carrier]
  [connected : ConnectedSpace Carrier]
  [simple : LieAlgebra.IsSimple ℝ
    (GroupLieAlgebra (𝓘(ℝ, Fin dimension → ℝ)) Carrier)]

attribute [instance] CompactSimpleGaugeGroup.group CompactSimpleGaugeGroup.topology
  CompactSimpleGaugeGroup.hausdorff CompactSimpleGaugeGroup.secondCountable
  CompactSimpleGaugeGroup.charted CompactSimpleGaugeGroup.smooth
  CompactSimpleGaugeGroup.lie CompactSimpleGaugeGroup.lieThree CompactSimpleGaugeGroup.compact
  CompactSimpleGaugeGroup.connected CompactSimpleGaugeGroup.simple

abbrev CompactSimpleGaugeGroup.Algebra (G : CompactSimpleGaugeGroup) :=
  GroupLieAlgebra (𝓘(ℝ, Fin G.dimension → ℝ)) G.Carrier

end YangMills
