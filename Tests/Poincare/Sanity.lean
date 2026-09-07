import Problems.Poincare.Millennium
import Mathlib.Geometry.Manifold.PoincareConjecture

/-!
# Poincaré conjecture: sanity checks

The repository statement is equivalent to the shape of Mathlib's
`proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three`; the three formulations are
genuinely equivalent; the empty space is not a counterexample; `S³` is the unit sphere of `ℝ⁴`.
Only the prize placeholder may use `sorryAx`.
-/

open MillenniumPoincare Metric

universe u

namespace Tests.Poincare

/-! ## Axiom audit -/

/-- info: 'MillenniumPoincare.ClayPoincareConjecture.iff_mathlib_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayPoincareConjecture.iff_mathlib_shape

/-- info: 'MillenniumPoincare.ClayPoincareConjecture.iff_closed_curves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayPoincareConjecture.iff_closed_curves

/-- info: 'MillenniumPoincare.ClayPoincareConjecture.iff_fundamental_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayPoincareConjecture.iff_fundamental_group

/-- info: 'MillenniumPoincare.ClosedCurvesContract.iff_simplyConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedCurvesContract.iff_simplyConnected

/-- info: 'MillenniumPoincare.TrivialFundamentalGroup.iff_simplyConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TrivialFundamentalGroup.iff_simplyConnected

/-- info: 'MillenniumPoincare.clay_prize_poincare_conjecture' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clay_prize_poincare_conjecture

/-! ## The sphere is the unit sphere of `EuclideanSpace ℝ (Fin 4)`, as in Milnor's Clay text -/

example : ThreeSphere = ↥(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := rfl

example : ThreeSphere = ↥(sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) := rfl

/-! ## The empty space is excluded: `SimplyConnectedSpace` forces `Nonempty` -/

example (M : Type) [TopologicalSpace M] [SimplyConnectedSpace M] : Nonempty M :=
  ((simply_connected_iff_unique_homotopic M).1 inferInstance).1

/-! ## Second countability is redundant given compactness and charts on `ℝ³` -/

example (M : Type u) [TopologicalSpace M] [ChartedSpace EuclideanThreeSpace M] [CompactSpace M] :
    SecondCountableTopology M :=
  ChartedSpace.secondCountable_of_sigmaCompact EuclideanThreeSpace M

/-! ## The Mathlib shape literally matches the `proof_wanted` hypotheses -/

example : ClayPoincareConjecture.Formulations.MathlibShape.{0} ↔
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) :=
  Iff.rfl

/-! ## The formulations are honest: a space with trivial `π₁` everywhere is simply connected -/

example (M : Type) [TopologicalSpace M] [PathConnectedSpace M]
    (h : ∀ x : M, Subsingleton (FundamentalGroup M x)) : SimplyConnectedSpace M :=
  (TrivialFundamentalGroup.iff_simplyConnected M).1 ⟨inferInstance, h⟩

example (M : Type) [TopologicalSpace M] [PathConnectedSpace M]
    (h : ∀ (x : M) (γ : Path x x), Path.Homotopic γ (Path.refl x)) : SimplyConnectedSpace M :=
  (ClosedCurvesContract.iff_simplyConnected M).1 ⟨inferInstance, h⟩

end Tests.Poincare
