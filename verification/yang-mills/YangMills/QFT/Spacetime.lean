import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.LinearAlgebra.Determinant

/-!
# Spacetime and the proper, orthochronous Poincaré transformations

The norm used for Schwartz functions is the ordinary finite-dimensional norm.
Causality uses the Minkowski form (+---), not that norm.
-/

noncomputable section
namespace YangMills

abbrev Spacetime := Fin 4 → ℝ
abbrev TestFunction := SchwartzMap Spacetime ℂ

/-- Minkowski pairing with signature (+---). -/
def minkowski (x y : Spacetime) : ℝ :=
  x 0 * y 0 - ∑ i : Fin 3, x i.succ * y i.succ

def FutureCone : Set Spacetime :=
  {p | 0 ≤ p 0 ∧ 0 ≤ minkowski p p}

def SpacelikeSeparated (x y : Spacetime) : Prop :=
  minkowski (x - y) (x - y) < 0

/-- A concrete Lorentz transformation, including both components of the
proper-orthochronous restriction. Cone preservation is required in both
 directions, so inverse transformations have the same property. -/
structure LorentzTransform where
  linear : Spacetime ≃L[ℝ] Spacetime
  metric : ∀ x y, minkowski (linear x) (linear y) = minkowski x y
  proper : LinearMap.det linear.toLinearMap = 1
  future : ∀ x ∈ FutureCone, linear x ∈ FutureCone
  inverse_future : ∀ x ∈ FutureCone, linear.symm x ∈ FutureCone

namespace LorentzTransform

def identity : LorentzTransform where
  linear := ContinuousLinearEquiv.refl ℝ Spacetime
  metric := fun _ _ => rfl
  proper := LinearMap.det_id
  future := fun _ h => h
  inverse_future := fun _ h => h

/-- `compose L M` acts first by M, then by L. -/
def compose (L M : LorentzTransform) : LorentzTransform where
  linear := M.linear.trans L.linear
  metric := by intro x y; exact (L.metric _ _).trans (M.metric x y)
  proper := by
    change LinearMap.det (L.linear.toLinearMap.comp M.linear.toLinearMap) = 1
    rw [LinearMap.det_comp, L.proper, M.proper, mul_one]
  future := fun x hx => L.future _ (M.future x hx)
  inverse_future := fun x hx => M.inverse_future _ (L.inverse_future x hx)

end LorentzTransform

structure PoincareTransform where
  lorentz : LorentzTransform
  translation : Spacetime

namespace PoincareTransform

def act (g : PoincareTransform) (x : Spacetime) : Spacetime :=
  g.translation + g.lorentz.linear x

def inverseAct (g : PoincareTransform) (x : Spacetime) : Spacetime :=
  g.lorentz.linear.symm (x - g.translation)

def identity : PoincareTransform := ⟨LorentzTransform.identity, 0⟩

def translate (a : Spacetime) : PoincareTransform := ⟨LorentzTransform.identity, a⟩

def compose (g h : PoincareTransform) : PoincareTransform :=
  ⟨g.lorentz.compose h.lorentz, g.translation + g.lorentz.linear h.translation⟩

/-- The usual finite-dimensional topology, specified by translation and
matrix entries, not an arbitrary topology chosen by a candidate theory. -/
instance : TopologicalSpace PoincareTransform :=
  TopologicalSpace.induced
    (fun g => (g.translation,
      fun i j : Fin 4 => g.lorentz.linear (Pi.single j 1) i)) inferInstance

@[simp] theorem act_identity (x : Spacetime) : identity.act x = x := by
  simp [act, identity, LorentzTransform.identity]

@[simp] theorem act_compose (g h : PoincareTransform) (x : Spacetime) :
    (g.compose h).act x = g.act (h.act x) := by
  simp [act, compose, LorentzTransform.compose, map_add, add_assoc]

@[simp] theorem inverseAct_act (g : PoincareTransform) (x : Spacetime) :
    g.inverseAct (g.act x) = x := by
  simp [act, inverseAct]

end PoincareTransform

/-- Separation of the closed supports of two test functions. -/
def TestFunctionsSpacelike (f g : TestFunction) : Prop :=
  ∀ x ∈ tsupport f, ∀ y ∈ tsupport g, SpacelikeSeparated x y

/-- Pointwise specification of the pullback of a Schwartz function.
The QFT data below must supply such a function for every transformation;
this equation uniquely determines it. -/
def IsPullback (g : PoincareTransform) (f transformed : TestFunction) : Prop :=
  ∀ x, transformed x = f (g.inverseAct x)

end YangMills
