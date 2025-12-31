import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.PoincareConjecture
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option diagnostics true
set_option diagnostics.threshold 3000

namespace MillenniumPoincare
/-!
# The Poincaré Conjecture

This file formalizes the statement of the original Poincaré conjecture in Lean 4 although a general version is already stated in PoincareConjecture.lean file.

I just wanted to write it in a simpler way for me to understand and its only for the n = 3 case as that was the one which got proven.

The Poincaré conjecture states that every simply connected, closed 3-manifold
is homeomorphic to the 3-sphere. It was proven by Grigori Perelman in 2003.

## Mathematical statement

In mathematical notation, the conjecture states:

If M is a compact 3-dimensional manifold without boundary such that every simple
closed curve in M can be continuously deformed to a point, then M is homeomorphic
to the 3-sphere.
-/
-- Using the same syntax as in the original Lean 4 file in PoincareConjecture.lean
open scoped Manifold
open Metric (sphere)

/-- The (topological) Poincaré conjecture in dimension `3`, stated as a proposition. -/
def PoincareConjecture3 : Prop :=
  ∀ (M : Type*)
    [TopologicalSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    [CompactSpace M],
      Nonempty (Homeomorph M (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))

/-!
`SimplyConnectedSpace` already captures trivial fundamental group, so `PoincareConjecture3` already
matches the usual “π₁(M) is trivial” formulation.
-/

/--
Again its there in the original file but still want to reiterate the poiints.
Generalized conjecture for higher dimensions (proven for n ≥ 5 by Smale,
for n = 4 by Freedman, and for n = 3 by Perelman):
Every compact n-dimensional manifold that is homotopy equivalent to the n-sphere
is homeomorphic to the n-sphere.

The hypothesis is stated for more general cases differently: instead of requiring the manifold to be simply connected, we require it to be homotopy equivalent to the n-sphere.

Two spaces are homotopy equivalent if they can be continuously deformed into each other,
allowing for dimensional collapsing. An n-sphere is homotopy equivalent to a point with
an n-dimensional "shell" around it.

Copied from the Poincareconjecture.lean but here are some historical results:
- For n ≥ 5: Proven by Stephen Smale in 1961 using the h-cobordism theorem
- For n = 4: Proven by Michael Freedman in 1982 using different techniques
- For n = 3: Proven by Grigori Perelman in 2003 using Ricci flow with surgery
- For n = 1,2: These were known much earlier (the 1-sphere and 2-sphere have simple classifications)
--/
def GeneralizedPoincareConjecture : Prop :=
  ∀ (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M],
      ContinuousMap.HomotopyEquiv M (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
        Nonempty (Homeomorph M (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

end MillenniumPoincare
