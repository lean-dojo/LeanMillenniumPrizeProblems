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
# Birch and Swinnerton-Dyer Conjecture Formulation by Jz Pan [https://leanprover.zulipchat.com/#user/366779]

This file presents a technically precise formulation of the Birch and Swinnerton-Dyer conjecture
that differs from my original formulation in several key ways:

1. **Focus on "Fake" L-function**: It explicitly works with a "fake" Hasse-Weil L-function,
   acknowledging that this might differ from the mathematically correct one by finitely many
   Euler factors, but has the same analytic properties relevant to the conjecture.

2. **Scope Limitation**: This version focuses only on elliptic curves over ℚ (through base change
   from curves over ℤ), whereas my formulation considered curves over general number fields.

3. **Component Emphasis**: This formulation emphasizes the rank part of the BSD conjecture without
   including the more complex leading coefficient formula that my version included.

4. **Direct Use of Structures**: Instead of defining a separate EllipticCurve type, this works
   directly with WeierstrassCurve and its associated structures from mathlib.
-/

universe u

open Cardinal Polynomial

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The number of rational points of a Weierstrass curve `W` over a ring `R`.
It is zero if there are infinitely many such points. -/
noncomputable def numPoints := Cardinal.toNat #W.toAffine.Point

/-- The trace of Frobenius isogeny of a Weierstrass curve `W` over a ring `R`.
This definition is mathematically correct if `R` is a finite field. -/
noncomputable def frobeniusTrace : ℤ := Cardinal.toNat #R + 1 - W.numPoints

open scoped Classical in
/-- The **local Euler factor** `f` of a Weierstrass curve `W` over a ring `R`,
as a polynomial over `ℤ`. This definition is mathematically correct if `R` is a finite field.
The corresponding term in the L-function is `f(q⁻ˢ)⁻¹` where `q` is the cardinality of `R`. -/
noncomputable def localEulerFactor : ℤ[X] :=
  if W.IsElliptic then
    1 - W.frobeniusTrace • X + Cardinal.toNat #R • X ^ 2
  else
    1 - W.frobeniusTrace • X

end CommRing

section Field

variable {F : Type u} [Field F]

/-- The (additive) group of `F`-rational points, using Mathlib's projective model. -/
abbrev MordellWeilGroup (W : WeierstrassCurve F) : Type u :=
  (W.toProjective).Point

/--
A `Prop` asserting that the group of rational points of `W` is finitely generated.

Mathematically, this is true for elliptic curves over global fields (Mordell–Weil theorem),
but that theorem is not currently available in Mathlib.
-/
def MordellWeil (W : WeierstrassCurve F) : Prop :=
  AddGroup.FG (MordellWeilGroup (F := F) W)

/-- The **Mordell-Weil rank** of a Weierstrass curve `W` over a field `F`, defined to be the
`ℚ`-dimension of `ℚ ⊗[ℤ] (E(F)/torsion)`, expressed as an `ENat` via `Cardinal.toENat`.

If the group is finitely generated, this recovers the usual integer rank.
-/
noncomputable def rank (W : WeierstrassCurve F) : ENat :=
  Cardinal.toENat <|
    Module.rank ℚ
      (TensorProduct ℤ ℚ ((MordellWeilGroup (F := F) W) ⧸ AddCommGroup.torsion _))

end Field

section Int

variable (W : WeierstrassCurve ℤ)

/-- The *fake* **Hasse-Weil L-function** of a Weierstrass curve over `ℤ`.
Since the Weierstrass curve is not necessarily a global minimal model, it misses finitely many
Euler factors compared to the mathematically correct one, namely, it is `L(E,s) * ∏ p, fₚ(p⁻ˢ)`
for some finitely many `p`. Since `fₚ(p⁻ˢ)` is entire, this function is also entire.
Since `fₚ(p⁻ˢ)` has no zeros on reals, the order of zeroes of this function on reals is the same
as the actual L-function. -/
noncomputable def fakeHasseWeil (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (aeval (p ^ (-s) : ℂ) (W.baseChange (ZMod p.1)).localEulerFactor)⁻¹

/-- The **rank part of the Birch and Swinnerton-Dyer conjecture** for elliptic curves over `ℚ`.
It is stated as that for any Weierstrass curve over `ℤ` with non-zero discriminant, the
Mordell-Weil group of the corresponding elliptic curve over `ℚ` is finitely generated,
and its *fake* L-function has an analytic continuation to the whole complex plane,
whose order of zeroes at `1` is equal to the Mordell-Weil rank. -/
def BSD : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → WeierstrassCurve.MordellWeil (W.baseChange ℚ) ∧
    ∃ (L : ℂ → ℂ) (σ : ℝ) (_han : ∀ s : ℂ, AnalyticAt ℂ L s),
      (∀ s : ℂ, s.re > σ → L s = W.fakeHasseWeil s) ∧
        analyticOrderAt L 1 = WeierstrassCurve.rank (W.baseChange ℚ)

end Int

end WeierstrassCurve
