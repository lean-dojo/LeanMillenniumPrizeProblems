import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.PoincareConjecture
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.TotallyDisconnected

set_option diagnostics true
set_option diagnostics.threshold 3000

namespace MillenniumPoincare
/-!
# The Poincaré Conjecture

This file states the Clay Millennium problem “Poincaré conjecture” in Lean, following the official
Clay problem description:
`Problems/Poincare/references/clay/poincare.pdf`.

Mathlib already contains the (proved) Poincaré conjecture as
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`. Here we restate the dimension-`3` case in a
simple standalone form (`PoincareConjecture3`) and include the usual generalized formulation.

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
    [SecondCountableTopology M]
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

/-!
## The `n = 0` case (provable in Mathlib today)

The Clay problem is the 3-dimensional Poincaré conjecture, but it is still useful to record that
the generalized statement is easy in dimension `0`: a `0`-manifold is discrete, and any homotopy
equivalence between discrete spaces is automatically a homeomorphism.
-/

open unitInterval

namespace ContinuousMap

/-- If the codomain is discrete, then homotopic continuous maps are equal. -/
theorem Homotopic.eq_of_discrete {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f g : C(X, Y)} (h : f.Homotopic g) : f = g := by
  classical
  ext x
  rcases h with ⟨F⟩
  have hcont : Continuous (fun t : I ↦ F (t, x)) := by
    simpa using F.continuous.comp (continuous_id.prodMk continuous_const)
  have hconst : (fun t : I ↦ F (t, x)) 0 = (fun t : I ↦ F (t, x)) 1 := by
    simpa using
      (PreconnectedSpace.constant (Y := Y) (hp := (by infer_instance : PreconnectedSpace I))
        (f := fun t : I ↦ F (t, x)) hcont (x := (0 : I)) (y := (1 : I)))
  simpa [F.map_zero_left, F.map_one_left] using hconst

end ContinuousMap

/--
Any homotopy equivalence between discrete spaces induces a homeomorphism.

This is the key ingredient in proving the generalized Poincaré conjecture in dimension `0`.
-/
theorem homotopyEquiv_nonempty_homeomorph_of_discrete
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology X] [DiscreteTopology Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (Homeomorph X Y) := by
  classical
  have hleft : e.invFun.comp e.toFun = ContinuousMap.id X :=
    ContinuousMap.Homotopic.eq_of_discrete (X := X) (Y := X) e.left_inv
  have hright : e.toFun.comp e.invFun = ContinuousMap.id Y :=
    ContinuousMap.Homotopic.eq_of_discrete (X := Y) (Y := Y) e.right_inv
  refine ⟨{ toEquiv := { toFun := e.toFun, invFun := e.invFun
                         left_inv := fun x ↦ congrArg (fun f ↦ f x) hleft
                         right_inv := fun y ↦ congrArg (fun f ↦ f y) hright }
            continuous_toFun := e.toFun.continuous
            continuous_invFun := e.invFun.continuous }⟩

/-- The generalized topological Poincaré conjecture for `n = 0`. -/
theorem generalizedPoincareConjecture_zero
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [CompactSpace M]
    (h : ContinuousMap.HomotopyEquiv M (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) :
    Nonempty (Homeomorph M (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) := by
  -- A `0`-manifold is discrete, and `S⁰` is also a `0`-manifold.
  haveI : DiscreteTopology (EuclideanSpace ℝ (Fin 0)) := inferInstance
  haveI : DiscreteTopology M :=
    ChartedSpace.discreteTopology (H := EuclideanSpace ℝ (Fin 0)) (M := M)
  haveI : DiscreteTopology (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    ChartedSpace.discreteTopology (H := EuclideanSpace ℝ (Fin 0))
      (M := sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
  exact homotopyEquiv_nonempty_homeomorph_of_discrete (X := M)
    (Y := sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) h

end MillenniumPoincare
