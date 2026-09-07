import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Birch and Swinnerton-Dyer rank-part support

This file provides supporting definitions for the rank part of Birch and Swinnerton-Dyer using
Mathlib's Weierstrass-curve constructions.

The main Millennium statement in `Problems.BirchSwinnertonDyer.Millennium` uses the Clay-specific
Euler product and refined leading-coefficient formula.  The auxiliary definitions here keep the
Mordell-Weil group, rank, and the local Euler factor polynomial available as reusable ingredients.

A former "rank part" statement built from a naive Euler product over *all* primes was removed from
this file: its bad-prime factor used the good-reduction trace `q + 1 - #W(𝔽_q)`, which is off by
one at singular reductions, so the resulting product had poles that no entire continuation can
match and the statement was false for every curve with split multiplicative reduction.
-/

universe u

open Cardinal Polynomial

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The number of rational points of a Weierstrass curve `W` over a ring `R`.
It is zero if there are infinitely many such points. -/
noncomputable def num_points := Cardinal.toNat #W.toAffine.Point

/--
The trace-of-Frobenius expression for a Weierstrass curve over a finite field, written for a
general ring because the Clay local Euler polynomial below is polymorphic in the base ring.
-/
noncomputable def frobenius_trace : ℤ := Cardinal.toNat #R + 1 - W.num_points

open scoped Classical in
/--
The Clay local Euler factor polynomial for a Weierstrass curve over a finite field, written
polymorphically over the base ring for use after reduction modulo a prime.

The corresponding term in the L-function is `f(q⁻ˢ)⁻¹`, where `q` is the cardinality of the base
field.

For a singular reduction the standard factor is `1 - aₚ X` with `aₚ = q - #W_ns(𝔽_q)`, where
`W_ns(𝔽_q)` is the set of nonsingular points *including* the point at infinity.  Mathlib's
`W.toAffine.Point` consists of exactly these points, so `aₚ = q - W.num_points`, which is `1`,
`-1`, `0` for split multiplicative, nonsplit multiplicative and additive reduction respectively.
The good-reduction trace `W.frobenius_trace = q + 1 - W.num_points` would be off by one here.
The Clay Euler product `WeierstrassCurve.incomplete_lseries` omits the bad primes entirely and
never evaluates this branch.
-/
noncomputable def local_euler_factor_polynomial : ℤ[X] :=
  if W.IsElliptic then
    1 - W.frobenius_trace • X + Cardinal.toNat #R • X ^ 2
  else
    1 - (Cardinal.toNat #R - W.num_points : ℤ) • X

end CommRing

section Field

variable {F : Type u} [Field F]

/-- The (additive) group of `F`-rational points, using Mathlib's projective model. -/
abbrev MordellWeilGroup (W : WeierstrassCurve F) : Type u :=
  (W.toProjective).Point

/--
A `Prop` asserting that the group of rational points of `W` is finitely generated.

Mathematically, this is true for elliptic curves over global fields (Mordell-Weil theorem).
-/
def MordellWeil (W : WeierstrassCurve F) : Prop :=
  AddGroup.FG W.toProjective.Point

/-- The **Mordell-Weil rank** of a Weierstrass curve `W` over a field `F`, defined to be the
`ℚ`-dimension of `ℚ ⊗[ℤ] (E(F)/torsion)`, expressed as an `ENat` via `Cardinal.toENat`.

If the group is finitely generated, this agrees with the usual integer rank.
-/
noncomputable def rank (W : WeierstrassCurve F) : ENat :=
  Cardinal.toENat <|
    Module.rank ℚ
      (TensorProduct ℤ ℚ ((MordellWeilGroup (F := F) W) ⧸ AddCommGroup.torsion _))

/-- The torsion subgroup `W(F)_tors` of the Mordell-Weil group. -/
noncomputable def mordell_weil_torsion_subgroup (W : WeierstrassCurve F) :
    AddSubgroup (MordellWeilGroup (F := F) W) :=
  AddCommGroup.torsion _

/-- The torsion-free quotient `W(F) / W(F)_tors`. -/
abbrev MordellWeilFreePart (W : WeierstrassCurve F) : Type u :=
  (MordellWeilGroup (F := F) W) ⧸ mordell_weil_torsion_subgroup (F := F) W

/--
Data for the Clay/Mordell-Weil decomposition
`W(F) ≃ ℤ^r × W(F)_tors`.

This records the structure theorem package explicitly: the natural rank, the finite torsion
subgroup, the free quotient, and the full product decomposition of rational points.
-/
structure MordellWeilDecompositionData (W : WeierstrassCurve F) where
  /-- The integer rank `r` in `ℤ^r`. -/
  rank_nat : ℕ
  /-- The recorded integer rank agrees with the `ENat` Mordell-Weil rank. -/
  rank_eq : WeierstrassCurve.rank W = (rank_nat : ENat)
  /-- The torsion subgroup `W(F)_tors` is finite. -/
  finite_torsion : Finite ↥(mordell_weil_torsion_subgroup (F := F) W)
  /-- The torsion-free quotient is the free abelian group `ℤ^r`. -/
  quotient_equiv : MordellWeilFreePart (F := F) W ≃+ (Fin rank_nat → ℤ)
  /-- The full Mordell-Weil group decomposes as `ℤ^r × W(F)_tors`. -/
  points_equiv :
    MordellWeilGroup (F := F) W ≃+
      ((Fin rank_nat → ℤ) × ↥(mordell_weil_torsion_subgroup (F := F) W))

/-- The Clay-style Mordell-Weil decomposition statement for one Weierstrass curve. -/
def MordellWeilDecomposition (W : WeierstrassCurve F) : Prop :=
  Nonempty (MordellWeilDecompositionData W)

/-- A decomposition witness gives finite Mordell-Weil rank. -/
theorem MordellWeilDecompositionData.rank_finite {W : WeierstrassCurve F}
    (data : MordellWeilDecompositionData W) :
    WeierstrassCurve.rank W ≠ ⊤ := by
  rw [data.rank_eq]
  simp

/-- A decomposition witness gives a finite torsion subgroup. -/
theorem MordellWeilDecompositionData.torsion_finite {W : WeierstrassCurve F}
    (data : MordellWeilDecompositionData W) :
    Finite ↥(mordell_weil_torsion_subgroup (F := F) W) :=
  data.finite_torsion

end Field


end WeierstrassCurve
