import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option diagnostics true
set_option diagnostics.threshold 5000
set_option linter.unusedVariables false

/-!
# Mordell–Weil group infrastructure (BSD)

This file provides *honest* (i.e. non-`sorry`, non-fake) scaffolding for the BSD statement:

- We use Mathlib's group law on projective points of a Weierstrass curve.
- Analytic invariants (L-function, order at `s = 1`, Sha, regulator, etc.) are represented as
  *fields of a structure*, because Mathlib does not currently provide these objects for general
  number fields.

The BSD conjecture itself is stated as a `Prop` in `Problems/BirchSwinnertonDyer/Millennium.lean`.
-/

namespace EllipticCurveDef

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- An elliptic curve is a Weierstrass curve together with the `IsElliptic` property. -/
def EllipticCurve (K : Type u) [CommRing K] :=
  { W : WeierstrassCurve K // W.IsElliptic }

namespace EllipticCurve

variable (E : EllipticCurve K)

/-- The (additive) group of `K`-rational points, using Mathlib's projective model. -/
noncomputable abbrev MordellWeilGroup : Type u :=
  (E.1.toProjective).Point

noncomputable instance : AddCommGroup (MordellWeilGroup (K := K) E) := by
  dsimp [MordellWeilGroup]
  infer_instance

/-- The torsion subgroup of the Mordell–Weil group (Mathlib definition). -/
noncomputable def torsionSubgroup : AddSubgroup (MordellWeilGroup (K := K) E) :=
  AddCommGroup.torsion _

/-- The size of the torsion subgroup, as a natural number (`0` if infinite). -/
noncomputable def torsion_order : ℕ :=
  Nat.card ↥(torsionSubgroup (K := K) E)

/--
The rationalized Mordell–Weil space `ℚ ⊗[ℤ] (E(K) / torsion)`.
-/
noncomputable abbrev rankSpace : Type u :=
  TensorProduct ℤ ℚ ((MordellWeilGroup (K := K) E) ⧸ torsionSubgroup (K := K) E)

/--
The Mordell–Weil rank as a `Cardinal`, defined as `Module.rank ℚ` of `rankSpace`.

This is the standard way to define the rank of an abelian group without assuming finite generation.
If the group is finitely generated, this agrees with the usual `ℤ^r ⊕ (finite torsion)` decomposition.
-/
noncomputable def rankCardinal : Cardinal :=
  Module.rank ℚ (rankSpace (K := K) E)

/--
The Mordell–Weil rank as a natural number, defined as `Module.finrank ℚ` of `rankSpace`.

If the `ℚ`-vector space is infinite-dimensional, this definition returns `0`.
-/
noncomputable def rank : ℕ :=
  Module.finrank ℚ (rankSpace (K := K) E)

end EllipticCurve

/--
Analytic/arithmetic invariants used in the BSD statement.

We store these as data instead of postulating their existence via `axiom`s.
-/
structure BSDInvariants (E : EllipticCurve K) where
  /-- The Hasse–Weil L-function. -/
  L_function : ℂ → ℂ
  /-- The order of vanishing of `L(E, s)` at `s = 1`. -/
  L_function_order_at_one : ℕ
  /-- The Tate–Shafarevich group. -/
  Sha : Type*
  /-- The (finite) order of `Sha(E)`. -/
  Sha_order : ℕ
  /-- The real period `Ω_E`. -/
  period : ℝ
  /-- The regulator `Reg_E`. -/
  regulator : ℝ
  /-- The product of Tamagawa numbers. -/
  tamagawa_product : ℝ
  /-- The leading coefficient of the Taylor expansion of `L(E, s)` at `s = 1`. -/
  L_function_leading_coefficient : ℝ

end EllipticCurveDef
