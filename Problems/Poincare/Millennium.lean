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

/--
The Poincaré conjecture (proven by Perelman):
A compact, connected, simply connected 3-manifold is homeomorphic to the 3-sphere.

This is the original conjecture formulated by Henri Poincaré in 1904 and proven
by Grigori Perelman in 2003 using Ricci flow with surgery.

## Mathematical details:

- A 3-manifold is a topological space where every point has a neighborhood homeomorphic to ℝ³
- "Compact" means the manifold is closed and bounded
- "Simply connected" means any loop in the manifold can be continuously contracted to a point
- The 3-sphere (𝕊³) is the set of points at unit distance from the origin in ℝ⁴

Atleast from my understanding Perelman's proof involved:
1. Starting with the manifold M
2. Evolving its geometry using Ricci flow with surgery
3. Showing that the resulting manifold must be a collection of geometric pieces
4. Proving that a simply connected union of these pieces must be 𝕊³

-/
theorem poincare_conjecture (M : Type*)
    [TopologicalSpace M]            -- M has a topology
    [T2Space M]                     -- M is a Hausdorff space (distinct points have disjoint neighborhoods)
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]  -- M has charts mapping to ℝ³
    [SimplyConnectedSpace M]        -- M is simply connected (π₁(M) is trivial)
    [CompactSpace M] :              -- M is compact (every open cover has a finite subcover)
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    -- The conclusion means there exists a homeomorphism between M and the 3-sphere
    -- (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) represents 𝕊³ as the unit sphere in ℝ⁴
  sorry -- Perelman's theorem (2003), proven using Ricci flow with surgery
        -- Perelman was awarded but declined the Fields Medal for this work

/--
Alternative formulation of the Poincaré conjecture using homotopy:
If a compact 3-manifold M has trivial fundamental group (π₁(M) = 0),
then M is homeomorphic to the 3-sphere.

I saw a video which told me that the fundamental group π₁(M) measures the "holes" in a space that can be detected
by loops. A trivial fundamental group means every loop can be continuously contracted
to a point.

To me this is essentially identical to the original conjecture, but explicitly
highlights that the key topological property is the triviality of the fundamental group.
This was Poincaré's main interest, as he was developing algebraic topology
and studying the relationship between algebraic invariants and the topology of spaces.

When we say "simply connected," we mean precisely that the fundamental group is trivial.
-/
theorem poincare_conjecture_homotopy (M : Type*)
    [TopologicalSpace M]            -- M has a topology
    [T2Space M]                     -- M is a Hausdorff space
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]  -- M is a 3-manifold
    [CompactSpace M]                -- M is compact
    [SimplyConnectedSpace M] :      -- M is simply connected (π₁(M) is trivial)
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  sorry -- Perelman's proof applies equally to this formulation


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
-/
theorem generalized_poincare_conjecture (n : ℕ) (M : Type*)
    [TopologicalSpace M]            -- M has a topology
    [T2Space M]                     -- M is a Hausdorff space
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]  -- M is an n-manifold
    [CompactSpace M]                -- M is compact
    [ConnectedSpace M]              -- M is connected
    (h : Nonempty (M ≃ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) :
    -- M is homotopy equivalent to the n-sphere (≃ₕ represents homotopy equivalence)
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    -- M is homeomorphic to the n-sphere (≃ₜ represents homeomorphism)
  sorry -- This has been proven for all n ≥ 1

end MillenniumPoincare
