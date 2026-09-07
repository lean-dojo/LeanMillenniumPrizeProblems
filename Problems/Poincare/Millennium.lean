import Problems.Common.Euclidean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace MillenniumPoincare

universe u
/-!
# The Poincaré Conjecture

This file states the Clay Millennium problem “Poincaré conjecture” in Lean, following the
Clay problem description:
`Problems/Poincare/references/clay/poincare.pdf`.

Mathlib contains the standard Poincaré conjecture statements in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`. This file isolates the dimension-`3` case
as `ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold`, and
`ClayPoincareConjecture.iff_mathlib_shape` proves it equivalent to the statement shape of Mathlib's
`proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three`.

The Poincaré conjecture states that every simply connected, closed 3-manifold
is homeomorphic to the 3-sphere. It was proven by Grigori Perelman in 2003.

## Mathematical statement

In mathematical notation, the conjecture states:

If M is a compact 3-dimensional manifold without boundary such that every simple
closed curve in M can be continuously deformed to a point, then M is homeomorphic
to the 3-sphere.
-/
open scoped Manifold
open Metric (sphere)

/-- The model three-dimensional Euclidean space for topological `3`-manifolds. -/
@[reducible]
def EuclideanThreeSpace : Type :=
  EuclideanCoordinateSpace ℝ 3

/-- The ambient four-dimensional Euclidean space used in Milnor's Clay description of `S³`. -/
@[reducible]
def EuclideanFourSpace : Type :=
  EuclideanCoordinateSpace ℝ 4

/--
Milnor's Clay equation for points on `S³`: points in four-dimensional Euclidean space whose
distance from the origin is exactly `1`.
-/
def three_sphere_equation (x : EuclideanFourSpace) : Prop :=
  ‖x‖ = 1

/-- The Clay `S³` as a subset of `ℝ⁴`, given by the unit-sphere equation. -/
def three_sphere_set : Set EuclideanFourSpace :=
  {x | three_sphere_equation x}

/-- The 3-sphere `S³` as the unit sphere in `ℝ⁴`, matching the Clay description. -/
@[reducible]
def ThreeSphere : Type :=
  sphere (0 : EuclideanFourSpace) 1

/-- The metric-sphere definition of `S³` is the Clay unit-sphere equation in `ℝ⁴`. -/
theorem ThreeSphere.mem_iff_equation (x : EuclideanFourSpace) :
    x ∈ sphere (0 : EuclideanFourSpace) 1 ↔ three_sphere_equation x := by
  simp [three_sphere_equation]

/-- The subset form of `S³` agrees with the metric sphere used for `ThreeSphere`. -/
theorem three_sphere_set.eq_sphere :
    three_sphere_set = sphere (0 : EuclideanFourSpace) 1 := by
  ext x
  exact (ThreeSphere.mem_iff_equation x).symm

/--
The topological Poincaré conjecture in dimension `3`, stated as a proposition.

The `SecondCountableTopology` hypothesis is the standard Lean/topological-manifold regularity
condition used here to model Clay's phrase “3-manifold”; it is not a separate geometric conclusion.
-/
def ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold : Prop :=
  ∀ (M : Type u)
    [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace EuclideanThreeSpace M]
    [SimplyConnectedSpace M]
    [CompactSpace M],
      Nonempty (Homeomorph M ThreeSphere)

/--
The Clay Poincare Conjecture statement: every simply connected closed
3-manifold is homeomorphic to the 3-sphere.

In this repository, “3-manifold” is represented by the usual Hausdorff, second-countable
topological manifold typeclass package modeled on `ℝ³`.
-/
def ClayPoincareConjecture : Prop :=
  ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold.{u}

/--
Clay's wording “every simple closed curve can be deformed continuously to a point”: the space is
path connected and every loop, at every base point, is homotopic to the constant loop.

This is equivalent to Mathlib's `SimplyConnectedSpace` (`ClosedCurvesContract.iff_simplyConnected`).
Clay's word “simple” is informal: the fundamental group sees all loops, and in a simply connected
space all of them contract.
-/
def ClosedCurvesContract (M : Type u) [TopologicalSpace M] : Prop :=
  PathConnectedSpace M ∧ ∀ (x : M) (γ : Path x x), Path.Homotopic γ (Path.refl x)

/-- Contractibility of all closed curves is simple connectivity. -/
theorem ClosedCurvesContract.iff_simplyConnected (M : Type u) [TopologicalSpace M] :
    ClosedCurvesContract M ↔ SimplyConnectedSpace M :=
  simply_connected_iff_loops_nullhomotopic.symm

/-- The fundamental group `pi_1(M, x)` appearing in Milnor's Clay discussion. -/
@[reducible]
def FundamentalGroupAt (M : Type u) [TopologicalSpace M] (x : M) : Type _ :=
  FundamentalGroup M x

/--
Clay's equivalent modern wording that the fundamental group is trivial: the space is path
connected and `π₁(M, x)` is trivial at every base point `x`.

This is equivalent to Mathlib's `SimplyConnectedSpace`
(`TrivialFundamentalGroup.iff_simplyConnected`).
-/
def TrivialFundamentalGroup (M : Type u) [TopologicalSpace M] : Prop :=
  PathConnectedSpace M ∧ ∀ x : M, Subsingleton (FundamentalGroupAt M x)

/-- A `TrivialFundamentalGroup` hypothesis gives a subsingleton fundamental group. -/
theorem TrivialFundamentalGroup.fundamental_group_subsingleton
    {M : Type u} [TopologicalSpace M] (h : TrivialFundamentalGroup M) (x : M) :
    Subsingleton (FundamentalGroupAt (M := M) x) :=
  h.2 x

/--
Path connectedness together with a trivial fundamental group at every base point is simple
connectivity: a trivial `π₁(M, x)` means every loop at `x` is homotopic to the constant loop.
-/
theorem TrivialFundamentalGroup.iff_simplyConnected (M : Type u) [TopologicalSpace M] :
    TrivialFundamentalGroup M ↔ SimplyConnectedSpace M := by
  constructor
  · rintro ⟨hpc, hsub⟩
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨hpc, fun x γ => ?_⟩
    haveI : Subsingleton (Path.Homotopic.Quotient x x) := hsub x
    exact Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x x) _ ⟦γ⟧ ⟦Path.refl x⟧)
  · intro h
    exact ⟨inferInstance, fun x => inferInstance⟩

/--
Clay's question wording: if a compact 3-manifold has every closed curve deformable to a point, then
it is homeomorphic to `S³`.
-/
def ClayPoincareConjecture.Formulations.ClosedCurves : Prop :=
  ∀ (M : Type u)
    [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace EuclideanThreeSpace M]
    [CompactSpace M],
      ClosedCurvesContract M →
        Nonempty (Homeomorph M ThreeSphere)

/--
Clay's modern `π₁` wording: if a compact 3-manifold has trivial `π₁`,
then it is homeomorphic to `S³`.
-/
def ClayPoincareConjecture.Formulations.TrivialPi1 : Prop :=
  ∀ (M : Type u)
    [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace EuclideanThreeSpace M]
    [CompactSpace M],
      TrivialFundamentalGroup M →
        Nonempty (Homeomorph M ThreeSphere)

/-- The closed-curve formulation is equivalent to the simply-connected statement. -/
theorem ClayPoincareConjecture.iff_closed_curves :
    ClayPoincareConjecture.{u} ↔ ClayPoincareConjecture.Formulations.ClosedCurves.{u} := by
  constructor
  · intro h M _top _t2 _second _charted _compact hcurves
    haveI : SimplyConnectedSpace M := (ClosedCurvesContract.iff_simplyConnected M).1 hcurves
    exact h M
  · intro h M _top _t2 _second _charted _simple _compact
    exact h M ((ClosedCurvesContract.iff_simplyConnected M).2 inferInstance)

/-- The `π₁` formulation is equivalent to the simply-connected statement. -/
theorem ClayPoincareConjecture.iff_fundamental_group :
    ClayPoincareConjecture.{u} ↔ ClayPoincareConjecture.Formulations.TrivialPi1.{u} := by
  constructor
  · intro h M _top _t2 _second _charted _compact hpi
    haveI : SimplyConnectedSpace M := (TrivialFundamentalGroup.iff_simplyConnected M).1 hpi
    exact h M
  · intro h M _top _t2 _second _charted _simple _compact
    exact h M ((TrivialFundamentalGroup.iff_simplyConnected M).2 inferInstance)

/-- The closed-curve and `π₁` global formulations are equivalent. -/
theorem ClayPoincareConjecture.Formulations.ClosedCurves.iff_fundamental_group :
    ClayPoincareConjecture.Formulations.ClosedCurves.{u} ↔
      ClayPoincareConjecture.Formulations.TrivialPi1.{u} :=
  ClayPoincareConjecture.iff_closed_curves.symm.trans
    ClayPoincareConjecture.iff_fundamental_group

/-!
The three formulations above differ only in how the hypothesis on `M` is phrased: Mathlib's
`SimplyConnectedSpace`, contractibility of every closed curve (`ClosedCurvesContract`), and
triviality of every fundamental group `π₁(M, x)` (`TrivialFundamentalGroup`).  The equivalences
`ClosedCurvesContract.iff_simplyConnected` and `TrivialFundamentalGroup.iff_simplyConnected` are
genuine theorems, not definitional unfoldings.
-/

/--
The statement shape of Mathlib's
`proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three`
(`Mathlib/Geometry/Manifold/PoincareConjecture.lean`), which omits the second-countability
hypothesis and writes `S³` as the unit sphere of `EuclideanSpace ℝ (Fin (3 + 1))`.
-/
def ClayPoincareConjecture.Formulations.MathlibShape : Prop :=
  ∀ (M : Type u)
    [TopologicalSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    [CompactSpace M],
      Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)

/--
The repository statement is equivalent to Mathlib's statement shape: for a compact space charted
on `ℝ³`, second countability is automatic (`ChartedSpace.secondCountable_of_sigmaCompact`).
-/
theorem ClayPoincareConjecture.iff_mathlib_shape :
    ClayPoincareConjecture.{u} ↔ ClayPoincareConjecture.Formulations.MathlibShape.{u} := by
  constructor
  · intro h M _top _t2 _charted _simple _compact
    haveI : SecondCountableTopology M :=
      ChartedSpace.secondCountable_of_sigmaCompact EuclideanThreeSpace M
    exact h M
  · intro h M _top _t2 _second _charted _simple _compact
    exact h M

/-!
## Main theorem

This final theorem records the Poincare Conjecture target directly. The theorem is mathematically
known, but this file still treats the formal Lean proof as future work.
-/

/-- Clay Millennium Prize target for the Poincare Conjecture. -/
theorem clay_prize_poincare_conjecture :
    ClayPoincareConjecture.{u} := by
  sorry

end MillenniumPoincare
