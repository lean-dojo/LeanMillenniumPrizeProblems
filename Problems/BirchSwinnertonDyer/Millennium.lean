import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Problems.BirchSwinnertonDyer.RankSupport

open Polynomial
open scoped BigOperators
open scoped Classical
open scoped Topology

namespace WeierstrassCurve

/--
The integral short Weierstrass model used in the Clay statement:
`y^2 = x^3 + ax + b`, with `a b : ℤ`.
-/
def short_integral_weierstrass_model (a b : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0
    a₂ := 0
    a₃ := 0
    a₄ := a
    a₆ := b }

instance short_integral_weierstrass_model.instIsShortNF (a b : ℤ) : (short_integral_weierstrass_model a b).IsShortNF := by
  constructor <;> rfl

/-- The discriminant of the Clay short integral model. -/
theorem short_integral_weierstrass_model.discriminant_eq (a b : ℤ) :
    (short_integral_weierstrass_model a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simpa [short_integral_weierstrass_model] using
    (WeierstrassCurve.Δ_of_isShortNF (W := short_integral_weierstrass_model a b))

/-- A nonsingular integral Weierstrass model base-changes to an elliptic curve over `ℚ`. -/
theorem is_elliptic_base_change_q
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    (W.baseChange ℚ).IsElliptic := by
  constructor
  have hΔQ : ((W.Δ : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hΔ
  have hUnit : IsUnit (((W.Δ : ℤ) : ℚ)) :=
    isUnit_iff_ne_zero.mpr hΔQ
  simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] using hUnit

/--
The incomplete Euler product `L(C,s)` from the Clay PDF (equation on page 2):

`L(C,s) = ∏_{p ∤ 2Δ} (1 - aₚ p^{-s} + p^{1-2s})^{-1}`.

We implement “omit primes `p | 2Δ`” by inserting a factor `1` at those primes.  The separate
`LSeriesData` package records convergence in the Clay half-plane `Re(s) > 3/2`.
-/
noncomputable def incomplete_lseries (W : WeierstrassCurve ℤ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes,
    if ((p : ℕ) : ℤ) ∣ (2 * W.Δ) then
      (1 : ℂ)
    else
      (aeval (p ^ (-s) : ℂ) (W.baseChange (ZMod (p : ℕ))).local_euler_factor_polynomial)⁻¹

/--
Mathlib's formal Hasse-Weil L-series for the rational elliptic curve obtained from the integral
Weierstrass model.

This is a formal Dirichlet-series construction in Mathlib; analytic continuation near `s = 1`
is still supplied by `LSeriesData`.
-/
protected noncomputable def hasse_weil_lseries (W : WeierstrassCurve ℤ) (s : ℂ) : ℂ :=
  (W.baseChange ℚ).LSeries s

/--
Auxiliary map used to show `WeierstrassCurve.Affine.Point` is finite over a finite ring: extract a
point's affine coordinates, using `none` for the point at infinity.
-/
noncomputable def point_to_option {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    W.toAffine.Point → Option (R × R)
  | 0 => none
  | Affine.Point.some (x := x) (y := y) _ => some (x, y)

/--
`point_to_option` is injective: an affine point is determined by whether it is the point at infinity
and, otherwise, by its `(x,y)`-coordinates.
-/
theorem point_to_option.injective {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    Function.Injective (point_to_option W) := by
  intro P Q h
  cases P <;> cases Q <;> cases h <;> rfl

/--
Over a finite ring, the type of affine points of a Weierstrass curve is finite.

This is an elementary finiteness lemma used to define `Nₚ`/`aₚ` in the Clay Euler product.
-/
theorem to_affine_point.finite {R : Type} [CommRing R] [Finite R] (W : WeierstrassCurve R) :
    Finite W.toAffine.Point := by
  classical
  exact Finite.of_injective (point_to_option W) (point_to_option.injective W)

/--
The Clay quantity `Nₚ` (Clay PDF, p.2): the number of affine solutions modulo `p`
(i.e. the number of points excluding the point at infinity).
-/
noncomputable def affine_point_count_mod_prime (W : WeierstrassCurve ℤ) (p : Nat.Primes) : ℕ :=
  (W.baseChange (ZMod (p : ℕ))).num_points - 1

/-- The Clay coefficient `aₚ := p - Nₚ` (Clay PDF, p.2). -/
noncomputable def frobenius_trace_coefficient (W : WeierstrassCurve ℤ) (p : Nat.Primes) : ℤ :=
  (p : ℤ) - (affine_point_count_mod_prime W p : ℤ)

private lemma one_le_num_points_zmod (W : WeierstrassCurve ℤ) (p : Nat.Primes) :
    1 ≤ (W.baseChange (ZMod (p : ℕ))).num_points := by
  classical
  have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
  letI : NeZero (p : ℕ) := ⟨hp0⟩
  haveI : Finite ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) :=
    to_affine_point.finite (W := W.baseChange (ZMod (p : ℕ)))
  letI : Fintype ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) := Fintype.ofFinite _
  have hcard :
      (W.baseChange (ZMod (p : ℕ))).num_points =
        Fintype.card ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) := by
    simp [WeierstrassCurve.num_points]
  have hpos :
      0 < Fintype.card ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) :=
    Fintype.card_pos_iff.mpr ⟨(0 : (W.baseChange (ZMod (p : ℕ))).toAffine.Point)⟩
  have hge :
      1 ≤ Fintype.card ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) :=
    Nat.succ_le_iff.mp hpos
  simpa [hcard] using hge
 
/--
Relate the Clay coefficient `aₚ` to Mathlib’s `frobenius_trace` for the reduction modulo `p`.

This identifies the `aₚ` appearing in the Clay Euler factor with the standard trace-of-Frobenius
quantity used in the definition of the local Euler polynomial.
-/
theorem frobenius_trace_coefficient_eq_frobenius_trace (W : WeierstrassCurve ℤ) (p : Nat.Primes) :
    frobenius_trace_coefficient W p = (W.baseChange (ZMod (p : ℕ))).frobenius_trace := by
  classical
  have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
  letI : NeZero (p : ℕ) := ⟨hp0⟩
  have hpoints : 1 ≤ (W.baseChange (ZMod (p : ℕ))).num_points := one_le_num_points_zmod W p
  have hPointCount :
      (affine_point_count_mod_prime W p : ℤ) =
        (W.baseChange (ZMod (p : ℕ))).num_points - 1 := by
    simp [WeierstrassCurve.affine_point_count_mod_prime, Int.ofNat_sub hpoints]
  simp [WeierstrassCurve.frobenius_trace_coefficient, WeierstrassCurve.frobenius_trace,
    WeierstrassCurve.num_points, hPointCount, ZMod.card]
  ring

/--
For primes `p ∤ 2Δ`, the Euler factor appearing in `incomplete_lseries` agrees with the explicit
Clay expression `1 - aₚ p^{-s} + p^{1-2s}` (Clay PDF, p.2).
-/
theorem local_euler_factor_polynomial.aeval_eq_explicit_clay_factor
    (W : WeierstrassCurve ℤ) (p : Nat.Primes) (s : ℂ) (hp : ¬ ((p : ℕ) : ℤ) ∣ (2 * W.Δ)) :
    aeval (p ^ (-s) : ℂ) ((W.baseChange (ZMod (p : ℕ))).local_euler_factor_polynomial) =
      (1 : ℂ) - (frobenius_trace_coefficient W p : ℂ) * (p ^ (-s) : ℂ) + (p : ℂ) ^ (1 - 2 * s) := by
  classical
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  have hpΔ : ¬ ((p : ℕ) : ℤ) ∣ W.Δ := by
    intro hdiv
    apply hp
    rcases hdiv with ⟨k, hk⟩
    refine ⟨2 * k, ?_⟩
    simp [hk, mul_assoc, mul_left_comm, mul_comm]
  have hΔmod : ((W.Δ : ℤ) : ZMod (p : ℕ)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hpΔ
  have hΔ' : (W.baseChange (ZMod (p : ℕ))).Δ ≠ 0 := by
    simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] using hΔmod
  have hIsUnit : IsUnit (W.baseChange (ZMod (p : ℕ))).Δ := by
    simp [isUnit_iff_ne_zero, hΔ']
  letI : (W.baseChange (ZMod (p : ℕ))).IsElliptic := ⟨hIsUnit⟩
  have hEll : (W.baseChange (ZMod (p : ℕ))).IsElliptic := by infer_instance
  have hap :
      (W.baseChange (ZMod (p : ℕ))).frobenius_trace = frobenius_trace_coefficient W p :=
    (frobenius_trace_coefficient_eq_frobenius_trace W p).symm
  have hEval :
      aeval (p ^ (-s) : ℂ) ((W.baseChange (ZMod (p : ℕ))).local_euler_factor_polynomial) =
        (1 : ℂ) - (frobenius_trace_coefficient W p : ℂ) * (p ^ (-s) : ℂ) + (p : ℂ) * (p ^ (-s) : ℂ) ^ 2 := by
    simp [WeierstrassCurve.local_euler_factor_polynomial, hEll, hap, aeval_X, mul_comm, ZMod.card]
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast (p.2.ne_zero)
  have hpow2 : (p : ℂ) ^ (-(2 * s)) = (p ^ (-s) : ℂ) ^ 2 := by
    have h := (Complex.cpow_nat_mul (p : ℂ) 2 (-s))
    have hexp : ((2 : ℂ) * (-s)) = (-(2 * s) : ℂ) := by
      ring
    simpa [hexp] using h
  have hquad : (p : ℂ) * (p ^ (-s) : ℂ) ^ 2 = (p : ℂ) ^ (1 - 2 * s) := by
    have h' : (p : ℂ) ^ (1 - 2 * s) = (p : ℂ) * (p ^ (-s) : ℂ) ^ 2 := by
      calc
        (p : ℂ) ^ (1 - 2 * s)
            = (p : ℂ) ^ ((1 : ℂ) + (-(2 * s))) := by
                  simp [sub_eq_add_neg]
        _ = (p : ℂ) ^ (1 : ℂ) * (p : ℂ) ^ (-(2 * s)) := by
              simpa using (Complex.cpow_add (x := (p : ℂ)) (y := (1 : ℂ)) (z := (-(2 * s))) hp0)
        _ = (p : ℂ) * (p ^ (-s) : ℂ) ^ 2 := by
              simp [Complex.cpow_one, hpow2]
    exact h'.symm
  simpa [hquad] using hEval

/-- The explicit Euler factor appearing in the Clay PDF. -/
noncomputable def clay_euler_product_factor (W : WeierstrassCurve ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if ((p : ℕ) : ℤ) ∣ (2 * W.Δ) then
    (1 : ℂ)
  else
    ((1 : ℂ) - (frobenius_trace_coefficient W p : ℂ) * (p ^ (-s) : ℂ) + (p : ℂ) ^ (1 - 2 * s))⁻¹

/--
The `incomplete_lseries` defined through the Clay local Euler polynomial equals the explicit
Clay Euler product `∏_{p ∤ 2Δ} (1 - aₚp^{-s} + p^{1-2s})^{-1}`.
-/
theorem incomplete_lseries.eq_clay_euler_product (W : WeierstrassCurve ℤ) (s : ℂ) :
    W.incomplete_lseries s = ∏' p : Nat.Primes, clay_euler_product_factor W p s := by
  refine tprod_congr fun p => ?_
  by_cases hp : ((p : ℕ) : ℤ) ∣ (2 * W.Δ)
  · simp [clay_euler_product_factor, hp]
  · simp [clay_euler_product_factor, hp, local_euler_factor_polynomial.aeval_eq_explicit_clay_factor W p s hp]

end WeierstrassCurve

namespace MillenniumBirchSwinnertonDyer

open Complex

/-!
# Birch and Swinnerton–Dyer Conjecture

Lean statement of the Clay Millennium problem “Birch and Swinnerton-Dyer conjecture”.

For an elliptic curve `C/ℚ` given by an integral Weierstrass model, the incomplete Euler product is

`L(C, s) := ∏_{p ∤ 2Δ} (1 - aₚ p^{-s} + p^{1-2s})^{-1}`

and the rank conjecture asserts that the Taylor expansion at `s = 1` begins
`c(s - 1)^r` with `c ≠ 0` and `r = rank(C(ℚ))`.

The refined leading-coefficient formula is kept as a separate optional statement. The arithmetic
objects needed for that refined formula, including Hasse-Weil L-functions, Tate-Shafarevich
groups, regulators, real periods, and Tamagawa factors, are recorded explicitly as data.
-/

/--
The ordinary Clay statement concerns elliptic curves over `ℚ`.

Our Euler product is attached to an integral Weierstrass model `W`; this predicate records that the
base change of that model is the rational elliptic curve whose group of rational points appears in
the rank statement.
-/
def IsEllipticCurveOverQ (W : WeierstrassCurve ℤ) : Prop :=
  (W.baseChange ℚ).IsElliptic

/--
A rational Weierstrass curve together with a chosen nonsingular integral model.

This keeps the Clay formulation honest: the Euler product is attached to the integral model, while
the Mordell-Weil rank is taken after base change to `ℚ`.
-/
structure IntegralWeierstrassModelForQCurve (E : WeierstrassCurve ℚ) where
  /-- The chosen integral Weierstrass model. -/
  model : WeierstrassCurve ℤ
  /-- Nonsingularity of the integral model. -/
  discriminant_ne_zero : model.Δ ≠ 0
  /-- The rational curve is obtained from the integral model by base change. -/
  base_change_eq : model.baseChange ℚ = E

namespace IntegralWeierstrassModelForQCurve

/-- A rational curve with a nonsingular integral model is elliptic over `ℚ`. -/
theorem is_elliptic {E : WeierstrassCurve ℚ} (M : IntegralWeierstrassModelForQCurve E) :
    E.IsElliptic := by
  have h := WeierstrassCurve.is_elliptic_base_change_q
    M.model M.discriminant_ne_zero
  simpa [M.base_change_eq] using h

end IntegralWeierstrassModelForQCurve

/--
Clay's “elliptic curve over `ℚ`”, represented in this repository by a nonsingular integral
Weierstrass model.

The model supplies the Euler product, while its base change to `ℚ` supplies the rational point
group and Mordell--Weil rank.
-/
structure ClayEllipticCurveOverQ where
  /-- The chosen nonsingular integral Weierstrass model. -/
  model : WeierstrassCurve ℤ
  /-- Nonsingularity of the integral model. -/
  discriminant_ne_zero : model.Δ ≠ 0

namespace ClayEllipticCurveOverQ

/-- The rational elliptic curve obtained by base change from the integral model. -/
def rational_curve (C : ClayEllipticCurveOverQ) : WeierstrassCurve ℚ :=
  C.model.baseChange ℚ

/-- The rational curve attached to a Clay elliptic curve is nonsingular. -/
theorem is_elliptic (C : ClayEllipticCurveOverQ) : C.rational_curve.IsElliptic :=
  WeierstrassCurve.is_elliptic_base_change_q
    C.model C.discriminant_ne_zero

/-- The rational point group `C(ℚ)` in the Clay statement. -/
def rational_point_group (C : ClayEllipticCurveOverQ) : Type :=
  C.rational_curve.toProjective.Point

/-- The incomplete Clay L-series attached to the chosen integral model. -/
noncomputable def incomplete_lseries (C : ClayEllipticCurveOverQ) (s : ℂ) : ℂ :=
  C.model.incomplete_lseries s

/-- The Mordell--Weil rank of `C(ℚ)`. -/
noncomputable def rank (C : ClayEllipticCurveOverQ) : ℕ∞ :=
  WeierstrassCurve.rank C.rational_curve

end ClayEllipticCurveOverQ

/--
The exact short integral model from the Clay PDF: `y^2 = x^3 + ax + b`, `a b : ℤ`, with
nonzero discriminant.
-/
structure ClayShortIntegralModel where
  a : ℤ
  b : ℤ
  discriminant_ne_zero : (WeierstrassCurve.short_integral_weierstrass_model a b).Δ ≠ 0

namespace ClayShortIntegralModel

/-- The underlying integral Weierstrass curve. -/
def weierstrass_curve (C : ClayShortIntegralModel) : WeierstrassCurve ℤ :=
  WeierstrassCurve.short_integral_weierstrass_model C.a C.b

/--
The discriminant of the cubic `x^3 + ax + b` in Wiles's Clay PDF notation.

The Weierstrass discriminant of `y^2 = x^3 + ax + b` is `16` times this integer.
-/
def cubic_discriminant (C : ClayShortIntegralModel) : ℤ :=
  -4 * C.a ^ 3 - 27 * C.b ^ 2

/-- Nonsingularity of the underlying integral Weierstrass curve. -/
theorem nonsingular_weierstrass_curve (C : ClayShortIntegralModel) :
    C.weierstrass_curve.Δ ≠ 0 := by
  simpa [weierstrass_curve] using C.discriminant_ne_zero

/-- The Clay discriminant formula for `y^2 = x^3 + ax + b`. -/
theorem discriminant_eq (C : ClayShortIntegralModel) :
    C.weierstrass_curve.Δ = -16 * (4 * C.a ^ 3 + 27 * C.b ^ 2) := by
  simpa [weierstrass_curve] using WeierstrassCurve.short_integral_weierstrass_model.discriminant_eq C.a C.b

/--
Relation between the Weierstrass discriminant used by Mathlib and the cubic discriminant `Δ` used
in the Clay PDF.
-/
theorem weierstrass_discriminant_eq
    (C : ClayShortIntegralModel) :
    C.weierstrass_curve.Δ = 16 * C.cubic_discriminant := by
  rw [C.discriminant_eq]
  dsimp [cubic_discriminant]
  ring

/-- The cubic discriminant `Δ` in the Clay short model is nonzero. -/
theorem cubic_discriminant.ne_zero (C : ClayShortIntegralModel) :
    C.cubic_discriminant ≠ 0 := by
  intro hΔ
  apply C.nonsingular_weierstrass_curve
  rw [C.weierstrass_discriminant_eq, hΔ]
  norm_num

/-- The associated rational curve is elliptic over `ℚ`. -/
theorem is_elliptic_curve_over_q (C : ClayShortIntegralModel) :
    IsEllipticCurveOverQ C.weierstrass_curve :=
  WeierstrassCurve.is_elliptic_base_change_q
    C.weierstrass_curve C.nonsingular_weierstrass_curve

/-- The displayed short integral model as a Clay elliptic curve over `ℚ`. -/
def elliptic_curve_over_q (C : ClayShortIntegralModel) : ClayEllipticCurveOverQ :=
  { model := C.weierstrass_curve
    discriminant_ne_zero := C.nonsingular_weierstrass_curve }

/-- The Clay `N_p` attached to this short integral model. -/
noncomputable def affine_point_count_mod_prime (C : ClayShortIntegralModel) (p : Nat.Primes) : ℕ :=
  WeierstrassCurve.affine_point_count_mod_prime C.weierstrass_curve p

/-- The Clay coefficient `a_p = p - N_p` attached to this short integral model. -/
noncomputable def frobenius_trace_coefficient (C : ClayShortIntegralModel) (p : Nat.Primes) : ℤ :=
  WeierstrassCurve.frobenius_trace_coefficient C.weierstrass_curve p

/-- The incomplete Clay L-series attached to this short integral model. -/
noncomputable def incomplete_lseries (C : ClayShortIntegralModel) (s : ℂ) : ℂ :=
  C.weierstrass_curve.incomplete_lseries s

/-- The bad-prime condition `p | 2Δ` using the cubic discriminant notation from the Clay PDF. -/
def clay_bad_prime (C : ClayShortIntegralModel) (p : Nat.Primes) : Prop :=
  ((p : ℕ) : ℤ) ∣ 2 * C.cubic_discriminant

/--
The bad-prime condition used by the internal Weierstrass-discriminant Euler product.

This is the condition appearing in `WeierstrassCurve.incomplete_lseries` after expressing the
short Clay model as a Mathlib Weierstrass curve.
-/
def weierstrass_bad_prime (C : ClayShortIntegralModel) (p : Nat.Primes) : Prop :=
  ((p : ℕ) : ℤ) ∣ 2 * C.weierstrass_curve.Δ

/--
A prime omitted by the Clay cubic-discriminant condition is omitted by the internal
Weierstrass-discriminant Euler product.
-/
theorem clay_bad_prime_implies_weierstrass
    (C : ClayShortIntegralModel) (p : Nat.Primes) :
    C.clay_bad_prime p → C.weierstrass_bad_prime p := by
  intro hp
  rcases hp with ⟨k, hk⟩
  refine ⟨16 * k, ?_⟩
  rw [C.weierstrass_discriminant_eq]
  calc
    2 * (16 * C.cubic_discriminant) = 16 * (2 * C.cubic_discriminant) := by ring
    _ = 16 * (((p : ℕ) : ℤ) * k) := by rw [hk]
    _ = ((p : ℕ) : ℤ) * (16 * k) := by ring

/--
If a prime is good for the internal Weierstrass-discriminant Euler product, it is good in Wiles's
Clay cubic-discriminant notation.
-/
theorem weierstrass_good_implies_clay_good
    (C : ClayShortIntegralModel) (p : Nat.Primes) :
    ¬ C.weierstrass_bad_prime p → ¬ C.clay_bad_prime p := by
  intro hgood hbad
  exact hgood (C.clay_bad_prime_implies_weierstrass p hbad)

/--
For a prime `p`, the internal Weierstrass-discriminant condition `p ∣ 2Δ_W = 32Δ` and Wiles's
cubic-discriminant condition `p ∣ 2Δ` coincide: `p ∣ 2^4 * (2Δ)` forces `p ∣ 2` or `p ∣ 2Δ`.
Hence the two Euler products omit exactly the same primes.
-/
theorem weierstrass_bad_prime_iff_clay_bad_prime
    (C : ClayShortIntegralModel) (p : Nat.Primes) :
    C.weierstrass_bad_prime p ↔ C.clay_bad_prime p := by
  constructor
  · intro hbad
    have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    unfold weierstrass_bad_prime at hbad
    rw [C.weierstrass_discriminant_eq] at hbad
    have h : ((p : ℕ) : ℤ) ∣ 2 ^ 4 * (2 * C.cubic_discriminant) := by
      have hrw : (2 : ℤ) * (16 * C.cubic_discriminant) = 2 ^ 4 * (2 * C.cubic_discriminant) := by
        ring
      rwa [hrw] at hbad
    rcases hp.dvd_mul.mp h with h2 | h2
    · exact Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h2) _
    · exact h2
  · exact C.clay_bad_prime_implies_weierstrass p

end ClayShortIntegralModel

/--
Analytic continuation of the Clay Euler product attached to a fixed nonsingular integral
Weierstrass model `W`.

This is an explicit package for the Hasse-Weil analytic-continuation input that is not currently
available as a canonical Mathlib construction.
-/
structure LSeriesData (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0) where
  /-- The analytic continuation of the (incomplete) L-series. -/
  L : ℂ → ℂ
  /-- The continuation is analytic on all of `ℂ` (Clay PDF references modularity results). -/
  analytic : ∀ s : ℂ, AnalyticAt ℂ L s
  /--
  Convergence of the explicit Clay Euler product in the half-plane `Re(s) > 3/2`, as stated in
  the Clay PDF.
  -/
  euler_product_has_prod : ∀ s : ℂ, s.re > (3 / 2 : ℝ) →
    HasProd (fun p : Nat.Primes => WeierstrassCurve.clay_euler_product_factor W p s)
      (W.incomplete_lseries s)
  /-- Agreement with the Euler product in its region of convergence (Clay PDF: `Re(s) > 3/2`). -/
  agrees : ∀ s : ℂ, s.re > (3 / 2 : ℝ) → L s = W.incomplete_lseries s

/--
Holomorphic-continuation input for one nonsingular integral Weierstrass model: `L(C,s)` extends
to an entire function of `s`.

The witness records the continuation and its agreement with the Euler product on `Re(s) > 3/2`.
Comparison data relating the incomplete Euler product to Mathlib's formal Hasse-Weil series is
*not* part of `LSeriesData`; it lives in the separate package `HasseWeilLSeriesData`.
-/
def ClayBirchSwinnertonDyer.Support.LSeriesContinuation.for_curve
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) : Prop :=
  Nonempty (LSeriesData W hΔ)

/-- Holomorphic-continuation statement for all nonsingular integral Weierstrass models. -/
def ClayBirchSwinnertonDyer.Support.LSeriesContinuation : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ClayBirchSwinnertonDyer.Support.LSeriesContinuation.for_curve W hΔ

/--
Holomorphic-continuation statement for the displayed short integral models `y^2 = x^3 + ax + b`.
-/
def ClayBirchSwinnertonDyer.Support.ShortIntegralLSeriesContinuation : Prop :=
  ∀ C : ClayShortIntegralModel,
    Nonempty (LSeriesData C.weierstrass_curve C.nonsingular_weierstrass_curve)

/--
A continuation witness yields an entire function agreeing with the Euler product in the half-plane
`Re(s) > 3/2`.
-/
theorem ClayBirchSwinnertonDyer.Support.LSeriesContinuation.for_curve.exists_entire_continuation
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    (h : ClayBirchSwinnertonDyer.Support.LSeriesContinuation.for_curve W hΔ) :
    ∃ L : ℂ → ℂ,
      (∀ s : ℂ, AnalyticAt ℂ L s) ∧
        ∀ s : ℂ, s.re > (3 / 2 : ℝ) → L s = W.incomplete_lseries s := by
  rcases h with ⟨data⟩
  exact ⟨data.L, data.analytic, data.agrees⟩

/-- The global holomorphic-continuation statement applies to the displayed short models. -/
theorem ClayBirchSwinnertonDyer.Support.LSeriesContinuation.short_integral
    (h : ClayBirchSwinnertonDyer.Support.LSeriesContinuation) :
    ClayBirchSwinnertonDyer.Support.ShortIntegralLSeriesContinuation := by
  intro C
  exact h C.weierstrass_curve C.nonsingular_weierstrass_curve

/--
Uniqueness of the analytic continuation: if two candidate continuations are entire and agree with
the Euler product on the half-plane `Re(s) > 3/2`, then the resulting functions are equal.
-/
theorem LSeriesData.l_unique {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    (d₁ d₂ : LSeriesData W hΔ) :
    d₁.L = d₂.L := by
  classical
  let z₀ : ℂ := 2
  have hd₁ : AnalyticOnNhd ℂ d₁.L Set.univ := by
    intro z hz
    simpa using d₁.analytic z
  have hd₂ : AnalyticOnNhd ℂ d₂.L Set.univ := by
    intro z hz
    simpa using d₂.analytic z
  have hRe : ∀ᶠ z in 𝓝[≠] z₀, (3 / 2 : ℝ) < z.re := by
    have hnhds : ∀ᶠ z in 𝓝 z₀, (3 / 2 : ℝ) < z.re := by
      have hopen : IsOpen {z : ℂ | (3 / 2 : ℝ) < z.re} := by
        simpa using
          (isOpen_lt (f := fun _ : ℂ => (3 / 2 : ℝ)) (g := fun z : ℂ => z.re)
            continuous_const Complex.continuous_re)
      have hz₀ : z₀ ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} := by
        dsimp [z₀]
        norm_num
      exact hopen.mem_nhds hz₀
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hnhds
  have hEq : ∀ᶠ z in 𝓝[≠] z₀, d₁.L z = d₂.L z := by
    filter_upwards [hRe] with z hz
    have hz' : z.re > (3 / 2 : ℝ) := hz
    -- Both sides agree with the Euler product on `Re(s) > 3/2`.
    simp [d₁.agrees z hz', d₂.agrees z hz']
  have hFreq : ∃ᶠ z in 𝓝[≠] z₀, d₁.L z = d₂.L z :=
    (show (∀ᶠ z in 𝓝[≠] z₀, d₁.L z = d₂.L z) from hEq).frequently
  exact AnalyticOnNhd.eq_of_frequently_eq (f := d₁.L) (g := d₂.L) (z₀ := z₀) hd₁ hd₂ hFreq

/-- The order of vanishing at `s = 1` is independent of the chosen analytic continuation. -/
theorem LSeriesData.analytic_order_eq {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    (d₁ d₂ : LSeriesData W hΔ) :
    analyticOrderAt d₁.L 1 = analyticOrderAt d₂.L 1 := by
  rw [LSeriesData.l_unique d₁ d₂]

/--
Hasse-Weil L-series data for a fixed nonsingular integral Weierstrass model.

The formal Hasse-Weil L-series is `W.hasse_weil_lseries`.  The Clay PDF uses the incomplete Euler
product with bad primes omitted.  This package keeps the Clay analytic continuation as the
primitive object but additionally requires the finite correction factor relating it to the formal
Hasse-Weil L-series to be analytic and nonzero at `s = 1`, so the order of vanishing at `1` is
unchanged.

The correction factor is only required to be analytic *at* `s = 1`, not entire.  The true
correction is `∏_{p ∣ 2Δ} L_p(s)`, the product of the local factors omitted from the incomplete
Euler product.  For the fixed model `W` this product always includes `p = 2`, and it is a
meromorphic function with poles on the line `Re s = 1/2` whenever an omitted prime has good
reduction (for example `y² + y = x³ − x²`, curve 11a3, has good reduction at `2`) and poles on
`Re s = 0` whenever an omitted prime has multiplicative reduction.  Requiring the correction to be
entire would make this structure empty for most curves; requiring analyticity at `1` is exactly
what the order-of-vanishing comparison below uses.
-/
structure HasseWeilLSeriesData (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    extends LSeriesData W hΔ where
  /-- Finite analytic correction for the local factors omitted at primes `p ∣ 2Δ`. -/
  bad_prime_correction : ℂ → ℂ
  /-- The correction is analytic at `s = 1` (it is meromorphic, not entire, in general). -/
  bad_prime_correction_analytic : AnalyticAt ℂ bad_prime_correction 1
  /-- Comparison with Mathlib's formal Hasse-Weil series in the convergence half-plane. -/
  hasse_weil_eq_corrected :
    ∀ s : ℂ, s.re > (3 / 2 : ℝ) →
      W.hasse_weil_lseries s = bad_prime_correction s * W.incomplete_lseries s
  /-- The finite bad-prime correction factor does not change the order of vanishing at `s = 1`. -/
  bad_prime_correction_ne_zero_at_one : bad_prime_correction 1 ≠ 0

namespace HasseWeilLSeriesData

variable {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}

/-- In the Euler-product half-plane, the corrected Clay continuation agrees with `W.hasse_weil_lseries`. -/
theorem hasse_weil_lseries_agrees
    (data : HasseWeilLSeriesData W hΔ) {s : ℂ} (hs : s.re > (3 / 2 : ℝ)) :
    data.bad_prime_correction s * data.L s = W.hasse_weil_lseries s := by
  rw [data.agrees s hs]
  exact (data.hasse_weil_eq_corrected s hs).symm

/--
The finite bad-prime correction factor is analytic and nonzero at `s = 1`, so multiplying by it
does not change the analytic order at `1`.
-/
theorem analytic_order_hasse_weil_lseries_eq (data : HasseWeilLSeriesData W hΔ) :
    analyticOrderAt (fun z => data.bad_prime_correction z * data.L z) 1 =
      analyticOrderAt data.L 1 := by
  have hmul :
      analyticOrderAt (fun z => data.bad_prime_correction z * data.L z) (1 : ℂ) =
        analyticOrderAt data.bad_prime_correction (1 : ℂ) + analyticOrderAt data.L (1 : ℂ) := by
    have hmul_pointwise :
        analyticOrderAt (data.bad_prime_correction * data.L) (1 : ℂ) =
          analyticOrderAt data.bad_prime_correction (1 : ℂ) + analyticOrderAt data.L (1 : ℂ) := by
      exact
        analyticOrderAt_mul (z₀ := (1 : ℂ)) (f := data.bad_prime_correction) (g := data.L)
          data.bad_prime_correction_analytic (data.analytic 1)
    have hcong_mul :
        analyticOrderAt (fun z => data.bad_prime_correction z * data.L z) (1 : ℂ) =
          analyticOrderAt (data.bad_prime_correction * data.L) (1 : ℂ) := by
      refine analyticOrderAt_congr (z₀ := (1 : ℂ)) ?_
      filter_upwards with z
      rfl
    exact hcong_mul.trans hmul_pointwise
  have hfac : analyticOrderAt data.bad_prime_correction (1 : ℂ) = 0 :=
    data.bad_prime_correction_analytic.analyticOrderAt_eq_zero.2
      data.bad_prime_correction_ne_zero_at_one
  calc
    analyticOrderAt (fun z => data.bad_prime_correction z * data.L z) 1
        = analyticOrderAt data.bad_prime_correction 1 + analyticOrderAt data.L 1 := hmul
    _ = analyticOrderAt data.L 1 := by simp [hfac]

end HasseWeilLSeriesData

/--
Birch--Swinnerton-Dyer rank equality phrased for the Hasse-Weil L-series continuation
`bad_prime_correction(s) * L(C,s)`.

The preceding agreement theorem identifies this function with the formal Hasse-Weil L-series in
the convergence half-plane, while the nonzero correction condition
makes its order at `s = 1` equal to the Clay order.
-/
def HasseWeilRankEqualityForModel (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (data : HasseWeilLSeriesData W hΔ) : Prop :=
  analyticOrderAt (fun z => data.bad_prime_correction z * data.L z) 1 =
    WeierstrassCurve.rank (W.baseChange ℚ)

/-- Global Birch--Swinnerton-Dyer rank-equality existence using the Hasse-Weil L-series continuation. -/
def ClayBirchSwinnertonDyer.Formulations.Rank.HasseWeil : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∃ data : HasseWeilLSeriesData W hΔ,
      HasseWeilRankEqualityForModel W hΔ data

/--
The Clay Taylor-leading-term form for the ordinary incomplete L-series:
`L(z) = c (z - 1)^r + higher order terms`, with `c ≠ 0`.
-/
def TaylorLeadingTerm {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    (data : LSeriesData W hΔ) (r : ℕ) (c : ℂ) : Prop :=
  c ≠ 0 ∧
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 1 ∧ g 1 = c ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), data.L z = (z - 1) ^ r • g z

/-- A Clay Taylor-leading-term coefficient is nonzero by definition. -/
theorem TaylorLeadingTerm.ne_zero {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    {data : LSeriesData W hΔ} {r : ℕ} {c : ℂ}
    (hc : TaylorLeadingTerm data r c) :
    c ≠ 0 :=
  hc.1

/--
Finite analytic order at `s = 1` gives the Clay Taylor-leading-term form for the ordinary
L-series.
-/
theorem LSeriesData.exists_taylor_leading_term {W : WeierstrassCurve ℤ}
    {hΔ : W.Δ ≠ 0} (data : LSeriesData W hΔ)
    (hfin : analyticOrderAt data.L 1 ≠ (⊤ : ℕ∞)) :
    ∃ r : ℕ, (r : ℕ∞) = analyticOrderAt data.L 1 ∧
      ∃ c : ℂ, TaylorLeadingTerm data r c := by
  have hAnalytic : AnalyticAt ℂ data.L 1 := data.analytic 1
  have hEqNat : analyticOrderAt data.L 1 = analyticOrderNatAt data.L 1 := by
    simp [Nat.cast_analyticOrderNatAt (f := data.L) (z₀ := (1 : ℂ)) hfin]
  rcases (hAnalytic.analyticOrderAt_eq_natCast
      (n := analyticOrderNatAt data.L 1)).1 hEqNat with
    ⟨g, hg_an, hg_ne, hg_eq⟩
  have hOrderNat :
      (analyticOrderNatAt data.L 1 : ℕ∞) = analyticOrderAt data.L 1 := by
    simpa using Nat.cast_analyticOrderNatAt (f := data.L) (z₀ := (1 : ℂ)) hfin
  refine ⟨analyticOrderNatAt data.L 1, hOrderNat, g 1, ?_⟩
  exact ⟨hg_ne, g, hg_an, rfl, hg_eq⟩

/--
Data for a *completed* L-function `L*` (Clay PDF, “Remarks 1”).

This is optional/refined data, separate from the ordinary Millennium rank statement. The completed
series is related to the ordinary series by the standard local relation near `s = 1`:

`L*(s) = completion_factor(s) * L(s)`,

with `completion_factor` analytic and nonvanishing at `s = 1`.

**Warning (placeholder data).** Nothing pins `completion_factor` down: any function analytic and
nonzero at `1` is admitted, so `lstar` is determined by `L` only up to an arbitrary nonvanishing
factor near `s = 1` (`lstar := k • L` with any `k ≠ 0` is legal data).  The order of vanishing of
`lstar` at `1` is therefore meaningful (`CompletedLSeriesData.order_lstar_eq`), but its leading
coefficient `c*` is not.  A faithful completed L-function would need the actual archimedean and
bad-prime factors, which are not formalized here.
-/
structure CompletedLSeriesData (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    extends LSeriesData W hΔ where
  /-- The completed L-function `L*`. -/
  lstar : ℂ → ℂ
  /-- The completion is analytic on all of `ℂ`. -/
  analytic_star : ∀ s : ℂ, AnalyticAt ℂ lstar s
  /-- The analytic completion factor relating `L*` to `L` near `s = 1`. -/
  completion_factor : ℂ → ℂ
  /-- The completion factor is analytic at `s = 1`. -/
  completion_factor_analytic : AnalyticAt ℂ completion_factor 1
  /-- The completion factor is nonzero at `s = 1`. -/
  completion_factor_ne_zero : completion_factor 1 ≠ 0
  /-- Local relation `L*(s) = completion_factor(s) * L(s)` near `s = 1`. -/
  lstar_eq : ∀ᶠ z in 𝓝 (1 : ℂ), lstar z = completion_factor z * L z

/--
Since the completion factor is analytic and nonvanishing at `s = 1`, the completed L-function `L*`
has the same order of vanishing at `s = 1` as `L`.
-/
theorem CompletedLSeriesData.order_lstar_eq {W : WeierstrassCurve ℤ}
    {hΔ : W.Δ ≠ 0} (data : CompletedLSeriesData W hΔ) :
    analyticOrderAt data.lstar 1 = analyticOrderAt data.L 1 := by
  have hcong :
      analyticOrderAt data.lstar (1 : ℂ) =
        analyticOrderAt (fun z => data.completion_factor z * data.L z) (1 : ℂ) := by
    exact analyticOrderAt_congr (z₀ := (1 : ℂ)) data.lstar_eq
  have hmul :
      analyticOrderAt (fun z => data.completion_factor z * data.L z) (1 : ℂ) =
        analyticOrderAt data.completion_factor (1 : ℂ) + analyticOrderAt data.L (1 : ℂ) := by
    have hmul_pointwise :
        analyticOrderAt (data.completion_factor * data.L) (1 : ℂ) =
          analyticOrderAt data.completion_factor (1 : ℂ) + analyticOrderAt data.L (1 : ℂ) := by
      exact
      analyticOrderAt_mul (z₀ := (1 : ℂ)) (f := data.completion_factor) (g := data.L)
        data.completion_factor_analytic (data.analytic 1)
    have hcong_mul :
        analyticOrderAt (fun z => data.completion_factor z * data.L z) (1 : ℂ) =
          analyticOrderAt (data.completion_factor * data.L) (1 : ℂ) := by
      refine analyticOrderAt_congr (z₀ := (1 : ℂ)) ?_
      filter_upwards with z
      rfl
    exact hcong_mul.trans hmul_pointwise
  have hfac : analyticOrderAt data.completion_factor (1 : ℂ) = 0 :=
    (data.completion_factor_analytic.analyticOrderAt_eq_zero).2 data.completion_factor_ne_zero
  calc
    analyticOrderAt data.lstar 1
        = analyticOrderAt (fun z => data.completion_factor z * data.L z) 1 := hcong
    _ = analyticOrderAt data.completion_factor 1 + analyticOrderAt data.L 1 := hmul
    _ = analyticOrderAt data.L 1 := by simp [hfac]

/--
The Clay Millennium statement (rank part): for any non-singular integral Weierstrass model,
the order of vanishing of `L(C,s)` at `s = 1` equals the Mordell–Weil rank of `C(ℚ)`.
-/
def ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∀ data : LSeriesData W hΔ,
      analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ)

/-- Birch--Swinnerton-Dyer rank equality for one fixed integral Weierstrass model and one chosen L-series. -/
def BirchSwinnertonDyerRankEqualityForModel (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (data : LSeriesData W hΔ) : Prop :=
  analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ)

/--
For fixed Hasse-Weil L-series data, the Hasse-Weil rank equality is equivalent to the Clay
incomplete-L-series rank equality.
-/
theorem HasseWeilRankEqualityForModel.iff_incomplete_lseries
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    (data : HasseWeilLSeriesData W hΔ) :
    HasseWeilRankEqualityForModel W hΔ data ↔
      BirchSwinnertonDyerRankEqualityForModel W hΔ data.toLSeriesData := by
  simp [HasseWeilRankEqualityForModel, BirchSwinnertonDyerRankEqualityForModel,
    data.analytic_order_hasse_weil_lseries_eq]

/--
The Birch--Swinnerton-Dyer rank equality plus finite Mordell-Weil rank gives the exact Clay Taylor form:
`L(s) = c(s - 1)^r + higher terms`, `c ≠ 0`, and `r = rank C(ℚ)`.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.exists_taylor_leading_term
    (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : LSeriesData W hΔ)
    (hfin : WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)) :
    ∃ r : ℕ, (r : ℕ∞) = WeierstrassCurve.rank (W.baseChange ℚ) ∧
      ∃ c : ℂ, TaylorLeadingTerm data r c := by
  have hOrder : analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ) :=
    hbsd W hΔ data
  have hfinOrder : analyticOrderAt data.L 1 ≠ (⊤ : ℕ∞) := by
    simpa [hOrder] using hfin
  rcases data.exists_taylor_leading_term hfinOrder with ⟨r, hr, c, hc⟩
  exact ⟨r, by simpa [hOrder] using hr, c, hc⟩

/--
Birch--Swinnerton-Dyer rank statement with analytic continuation included for every nonsingular integral
Weierstrass model.
-/
def ClayBirchSwinnertonDyer.Formulations.Rank.Existence : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∃ data : LSeriesData W hΔ, BirchSwinnertonDyerRankEqualityForModel W hΔ data

/-- The Hasse-Weil L-series statement gives Birch--Swinnerton-Dyer rank-existence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.HasseWeil.rank_existence
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.HasseWeil) :
    ClayBirchSwinnertonDyer.Formulations.Rank.Existence := by
  intro W hΔ
  rcases h W hΔ with ⟨data, hdata⟩
  exact ⟨data.toLSeriesData,
    (HasseWeilRankEqualityForModel.iff_incomplete_lseries data).1 hdata⟩

/-- Birch--Swinnerton-Dyer rank statement for one elliptic curve over `ℚ`, represented by an integral model. -/
def ClayBirchSwinnertonDyer.Formulations.Rank.Curve (C : ClayEllipticCurveOverQ) : Prop :=
  ∃ data : LSeriesData C.model C.discriminant_ne_zero,
    BirchSwinnertonDyerRankEqualityForModel C.model C.discriminant_ne_zero data

/-- Birch--Swinnerton-Dyer rank statement for every elliptic curve over `ℚ`. -/
def ClayBirchSwinnertonDyer.Formulations.Rank.OverQ : Prop :=
  ∀ C : ClayEllipticCurveOverQ, ClayBirchSwinnertonDyer.Formulations.Rank.Curve C

/--
The integral-model rank-existence statement is equivalent to the elliptic-curve-over-`ℚ`
formulation.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.Existence.iff_curves_over_q :
    ClayBirchSwinnertonDyer.Formulations.Rank.Existence ↔ ClayBirchSwinnertonDyer.Formulations.Rank.OverQ := by
  constructor
  · intro h C
    exact h C.model C.discriminant_ne_zero
  · intro h W hΔ
    exact h ⟨W, hΔ⟩

/--
Nonvacuous Clay short-model Birch--Swinnerton-Dyer statement: for every `y^2 = x^3 + ax + b` with `a b : ℤ` and
nonzero discriminant, provide the analytic L-series data and prove the rank statement.
-/
def ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral : Prop :=
  ∀ C : ClayShortIntegralModel,
    ∃ data : LSeriesData C.weierstrass_curve C.nonsingular_weierstrass_curve,
      BirchSwinnertonDyerRankEqualityForModel C.weierstrass_curve
        C.nonsingular_weierstrass_curve data

/-- The elliptic-curve-over-`ℚ` Birch--Swinnerton-Dyer statement implies the displayed short-model statement. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.OverQ.short_integral_models
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.OverQ) :
    ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral := by
  intro C
  simpa [ClayBirchSwinnertonDyer.Formulations.Rank.Curve, ClayShortIntegralModel.elliptic_curve_over_q] using
    h C.elliptic_curve_over_q

/--
The exact Taylor-expansion form from the Clay PDF:
`L(C,s) = c(s - 1)^r +` higher-order terms, with `c ≠ 0` and
`r = rank(C(ℚ))`.

This formulation keeps the analytic continuation data explicit and records the rank as a natural
number witness, matching the PDF's integer exponent.
-/
def ClayBirchSwinnertonDyer.Formulations.Taylor.Integral : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∃ data : LSeriesData W hΔ,
      ∃ r : ℕ, (r : ℕ∞) = WeierstrassCurve.rank (W.baseChange ℚ) ∧
        ∃ c : ℂ, TaylorLeadingTerm data r c

/-- Clay Taylor-expansion Birch--Swinnerton-Dyer statement for one elliptic curve over `ℚ`. -/
def ClayBirchSwinnertonDyer.Formulations.Taylor.Curve (C : ClayEllipticCurveOverQ) : Prop :=
  ∃ data : LSeriesData C.model C.discriminant_ne_zero,
    ∃ r : ℕ, (r : ℕ∞) = C.rank ∧ ∃ c : ℂ, TaylorLeadingTerm data r c

/-- Clay Taylor-expansion Birch--Swinnerton-Dyer statement for every elliptic curve over `ℚ`. -/
def ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ : Prop :=
  ∀ C : ClayEllipticCurveOverQ, ClayBirchSwinnertonDyer.Formulations.Taylor.Curve C

/--
Taylor-leading-term Birch--Swinnerton-Dyer form for one nonsingular integral Weierstrass model, using the Hasse-Weil
L-series package as the analytic witness.

The witness ties the Clay incomplete Euler product to the formal Hasse-Weil L-series by the
explicit bad-prime correction factor.
-/
def HasseWeilTaylorLeadingTermForModel
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (data : HasseWeilLSeriesData W hΔ) : Prop :=
  ∃ r : ℕ, (r : ℕ∞) = WeierstrassCurve.rank (W.baseChange ℚ) ∧
    ∃ c : ℂ, TaylorLeadingTerm data.toLSeriesData r c

/--
Global Taylor-expansion Birch--Swinnerton-Dyer statement using Hasse-Weil L-series data.
-/
def ClayBirchSwinnertonDyer.Formulations.Taylor.HasseWeil : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∃ data : HasseWeilLSeriesData W hΔ,
      HasseWeilTaylorLeadingTermForModel W hΔ data

/--
The Hasse-Weil L-series Taylor statement implies the integral-model Taylor statement because the
associated formal L-series is part of the Hasse-Weil data.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.HasseWeil.integral_taylor
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.HasseWeil) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.Integral := by
  intro W hΔ
  rcases h W hΔ with ⟨data, r, hrank, c, hlead⟩
  exact ⟨data.toLSeriesData, r, hrank, c, hlead⟩

/--
The integral-model Taylor statement is equivalent to the elliptic-curve-over-`ℚ` formulation.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.iff_curves_over_q :
    ClayBirchSwinnertonDyer.Formulations.Taylor.Integral ↔ ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ := by
  constructor
  · intro h C
    simpa [ClayBirchSwinnertonDyer.Formulations.Taylor.Curve, ClayEllipticCurveOverQ.rank,
      ClayEllipticCurveOverQ.rational_curve] using h C.model C.discriminant_ne_zero
  · intro h W hΔ
    simpa [ClayBirchSwinnertonDyer.Formulations.Taylor.Curve, ClayEllipticCurveOverQ.rank,
      ClayEllipticCurveOverQ.rational_curve] using h ⟨W, hΔ⟩

/--
Clay Birch--Swinnerton-Dyer statement:
for every elliptic curve over `ℚ`, the Taylor expansion of its Clay `L(C,s)` at `s = 1` has
leading term `c(s - 1)^r` with `c ≠ 0` and `r = rank(C(ℚ))`.

The statement is *existential* in the analytic continuation.  A proof must, for every curve,
construct an `LSeriesData` witness (an entire continuation agreeing with the Euler product on
`Re(s) > 3/2`, together with convergence of the Euler product there: modularity and the Hasse
bound), exhibit a finite rank `r` (the Mordell--Weil theorem), and then prove the Clay order of
vanishing statement.  This matches Wiles's prose, which treats the continuation as known, but it
makes the target strictly harder than the rank conjecture on its own.  The formulation
`ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries` quantifies universally over
continuation data and isolates the Birch--Swinnerton-Dyer content.  By `LSeriesData.l_unique` the
continuation is unique whenever it exists, so nothing depends on the choice of witness.
-/
def ClayBirchSwinnertonDyer : Prop :=
  ∀ C : ClayEllipticCurveOverQ,
    ∃ data : LSeriesData C.model C.discriminant_ne_zero,
      ∃ r : ℕ, (r : ℕ∞) = C.rank ∧ ∃ c : ℂ, TaylorLeadingTerm data r c

/-- `ClayBirchSwinnertonDyer` is equivalent to the integral-model Taylor statement. -/
theorem ClayBirchSwinnertonDyer.iff_taylor :
    ClayBirchSwinnertonDyer ↔ ClayBirchSwinnertonDyer.Formulations.Taylor.Integral :=
  by
    simpa [ClayBirchSwinnertonDyer, ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ, ClayBirchSwinnertonDyer.Formulations.Taylor.Curve] using
      ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.iff_curves_over_q.symm

/-- The Clay Birch--Swinnerton-Dyer statement gives the integral Weierstrass-model Taylor form. -/
theorem ClayBirchSwinnertonDyer.integral_taylor
    (h : ClayBirchSwinnertonDyer) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.Integral :=
  ClayBirchSwinnertonDyer.iff_taylor.1 h

/-- Build the Clay Birch--Swinnerton-Dyer statement from the integral Weierstrass-model Taylor form. -/
theorem ClayBirchSwinnertonDyer.of_integral_taylor
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.Integral) :
    ClayBirchSwinnertonDyer :=
  ClayBirchSwinnertonDyer.iff_taylor.2 h

/-- The Hasse-Weil L-series Taylor statement implies the elliptic-curve-over-`ℚ` Taylor form. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.HasseWeil.curves_over_q
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.HasseWeil) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ :=
  ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.iff_curves_over_q.1 h.integral_taylor

/-- Unfold the Clay Birch--Swinnerton-Dyer statement as the elliptic-curve-over-`ℚ` Taylor statement. -/
theorem ClayBirchSwinnertonDyer.curves_over_q
    (h : ClayBirchSwinnertonDyer) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ :=
  by
    simpa [ClayBirchSwinnertonDyer, ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ, ClayBirchSwinnertonDyer.Formulations.Taylor.Curve] using h

/--
The exact Clay Taylor-expansion form restricted to the short integral models displayed in the PDF:
`y^2 = x^3 + ax + b`, nonzero discriminant, and
`L(C,s) = c(s - 1)^r +` higher-order terms with `c ≠ 0` and `r = rank(C(ℚ))`.
-/
def ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral : Prop :=
  ∀ C : ClayShortIntegralModel,
    ∃ data : LSeriesData C.weierstrass_curve C.nonsingular_weierstrass_curve,
      ∃ r : ℕ,
        (r : ℕ∞) = WeierstrassCurve.rank (C.weierstrass_curve.baseChange ℚ) ∧
          ∃ c : ℂ, TaylorLeadingTerm data r c

/-- The elliptic-curve-over-`ℚ` Taylor statement implies the displayed short-model Taylor statement. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ.short_integral_models
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.OverQ) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral := by
  intro C
  simpa [ClayBirchSwinnertonDyer.Formulations.Taylor.Curve, ClayEllipticCurveOverQ.rank,
    ClayEllipticCurveOverQ.rational_curve, ClayShortIntegralModel.elliptic_curve_over_q] using
    h C.elliptic_curve_over_q

/-- The Clay Birch--Swinnerton-Dyer statement gives the Taylor form for the short integral models in the PDF. -/
theorem ClayBirchSwinnertonDyer.short_integral_taylor
    (h : ClayBirchSwinnertonDyer) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral :=
  h.curves_over_q.short_integral_models

/-- Birch--Swinnerton-Dyer rank-existence gives the rank statement for the displayed short integral models. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.Existence.short_integral_models
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.Existence) :
    ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral := by
  intro C
  exact h C.weierstrass_curve C.nonsingular_weierstrass_curve

/-- Taylor-expansion Birch--Swinnerton-Dyer gives the Taylor statement for the displayed short integral models. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.short_integral_models
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.Integral) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral := by
  intro C
  exact h C.weierstrass_curve C.nonsingular_weierstrass_curve

/-- The global Birch--Swinnerton-Dyer statement is exactly the collection of the per-curve statements. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.iff_models :
    ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries ↔
      ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0, ∀ data : LSeriesData W hΔ,
        BirchSwinnertonDyerRankEqualityForModel W hΔ data := by
  rfl

/--
For a fixed curve, if Birch--Swinnerton-Dyer holds for one analytic continuation, then it holds for every analytic
continuation.
-/
theorem BirchSwinnertonDyerRankEqualityForModel.transfer_continuation
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    {data₀ data : LSeriesData W hΔ}
    (h₀ : BirchSwinnertonDyerRankEqualityForModel W hΔ data₀) :
    BirchSwinnertonDyerRankEqualityForModel W hΔ data := by
  exact (LSeriesData.analytic_order_eq data data₀).trans h₀

/--
It is enough to prove Birch--Swinnerton-Dyer for one analytic continuation for each nonsingular curve; the uniqueness
theorem then transfers the rank equality to every continuation.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.rank_existence
    (h :
      ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
        ∃ data : LSeriesData W hΔ, BirchSwinnertonDyerRankEqualityForModel W hΔ data) :
    ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries := by
  intro W hΔ data
  rcases h W hΔ with ⟨data₀, h₀⟩
  exact BirchSwinnertonDyerRankEqualityForModel.transfer_continuation (data := data) h₀

/-- The existence-including Birch--Swinnerton-Dyer rank statement implies the universal continuation form. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.Existence.conjecture
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.Existence) :
    ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries :=
  ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.rank_existence h

/-- The Clay Taylor-expansion statement implies the rank-existence Birch--Swinnerton-Dyer statement. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.rank_existence
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.Integral) :
    ClayBirchSwinnertonDyer.Formulations.Rank.Existence := by
  intro W hΔ
  rcases h W hΔ with ⟨data, r, hrank, c, hc⟩
  rcases hc with ⟨hcne, g, hgan, hgc, hEq⟩
  have hAnalytic : AnalyticAt ℂ data.L 1 := data.analytic 1
  have hOrder : analyticOrderAt data.L 1 = (r : ℕ∞) := by
    refine (hAnalytic.analyticOrderAt_eq_natCast (n := r)).2 ?_
    exact ⟨g, hgan, by simpa [hgc] using hcne, hEq⟩
  refine ⟨data, ?_⟩
  dsimp [BirchSwinnertonDyerRankEqualityForModel]
  exact hOrder.trans hrank

/-- The short-integral-model Taylor statement implies the short-integral-model rank statement. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral.rank_existence
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral) :
    ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral := by
  intro C
  rcases h C with ⟨data, r, hrank, c, hc⟩
  rcases hc with ⟨hcne, g, hgan, hgc, hEq⟩
  have hAnalytic : AnalyticAt ℂ data.L 1 := data.analytic 1
  have hOrder : analyticOrderAt data.L 1 = (r : ℕ∞) := by
    refine (hAnalytic.analyticOrderAt_eq_natCast (n := r)).2 ?_
    exact ⟨g, hgan, by simpa [hgc] using hcne, hEq⟩
  refine ⟨data, ?_⟩
  dsimp [BirchSwinnertonDyerRankEqualityForModel]
  exact hOrder.trans hrank

/--
The rank-existence Birch--Swinnerton-Dyer statement gives the Clay Taylor-expansion form once Mordell-Weil ranks are
known to be finite for the integral models under consideration.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.Existence.taylor_birch_swinnerton_dyer
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.Existence)
    (hfin : ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
      WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)) :
    ClayBirchSwinnertonDyer.Formulations.Taylor.Integral := by
  intro W hΔ
  rcases h W hΔ with ⟨data, hbsd⟩
  have hOrder : analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ) := hbsd
  have hfinOrder : analyticOrderAt data.L 1 ≠ (⊤ : ℕ∞) := by
    simpa [hOrder] using hfin W hΔ
  rcases data.exists_taylor_leading_term hfinOrder with ⟨r, hr, c, hc⟩
  exact ⟨data, r, by simpa [hOrder] using hr, c, hc⟩

/--
Equivalence between the exact Clay Taylor form and the rank-existence form plus finite rank.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.iff_rank_existence_and_finite_rank :
    ClayBirchSwinnertonDyer.Formulations.Taylor.Integral ↔
      ClayBirchSwinnertonDyer.Formulations.Rank.Existence ∧
        ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
          WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞) := by
  constructor
  · intro h
    refine ⟨h.rank_existence, ?_⟩
    intro W hΔ
    rcases h W hΔ with ⟨data, r, hrank, c, hc⟩
    rw [← hrank]
    simp
  · intro h
    exact h.1.taylor_birch_swinnerton_dyer h.2

/--
`ClayBirchSwinnertonDyer` is exactly the order-of-vanishing rank statement, with existence of the
analytic continuation and finiteness of the Mordell--Weil rank made explicit.

This theorem states that the Taylor-leading-term form is the direct rank/order statement together
with finite Mordell--Weil rank.
-/
theorem ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank :
    ClayBirchSwinnertonDyer ↔
      ClayBirchSwinnertonDyer.Formulations.Rank.Existence ∧
        ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
          WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞) :=
  ClayBirchSwinnertonDyer.iff_taylor.trans
    ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.iff_rank_existence_and_finite_rank

/--
The Taylor-leading-term Birch--Swinnerton-Dyer statement contains the direct order-of-vanishing rank statement and
the finite Mordell-Weil rank condition.
-/
theorem ClayBirchSwinnertonDyer.rank_existence_and_finite_rank
    (h : ClayBirchSwinnertonDyer) :
      ClayBirchSwinnertonDyer.Formulations.Rank.Existence ∧
        ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
          WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞) :=
  ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank.1 h

/--
Build the Clay Birch--Swinnerton-Dyer statement from the direct order-of-vanishing rank form plus finite
Mordell-Weil rank.
-/
theorem ClayBirchSwinnertonDyer.of_rank_existence_and_finite_rank
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.Existence ∧
        ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
          WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)) :
    ClayBirchSwinnertonDyer :=
  ClayBirchSwinnertonDyer.iff_rank_existence_and_finite_rank.2 h

/-- Extract the direct rank-existence/order-of-vanishing form from the Taylor statement. -/
theorem ClayBirchSwinnertonDyer.rank_existence
    (h : ClayBirchSwinnertonDyer) :
    ClayBirchSwinnertonDyer.Formulations.Rank.Existence :=
  h.rank_existence_and_finite_rank.1

/--
The Taylor statement gives the universal continuation-independent rank equality for every
chosen Clay analytic continuation.
-/
theorem ClayBirchSwinnertonDyer.order_of_vanishing_conjecture
    (h : ClayBirchSwinnertonDyer) :
    ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries :=
  h.rank_existence.conjecture

/-- Extract finite Mordell--Weil rank for each nonsingular integral model. -/
theorem ClayBirchSwinnertonDyer.finite_rank
    (h : ClayBirchSwinnertonDyer)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞) :=
  h.rank_existence_and_finite_rank.2 W hΔ

/-- Apply the global Taylor statement to the displayed short integral models. -/
theorem ClayBirchSwinnertonDyer.short_integral_rank
    (h : ClayBirchSwinnertonDyer) :
    ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral :=
  h.rank_existence.short_integral_models

/--
Equivalence between the short-model Taylor form and the short-model rank form plus finite
Mordell-Weil rank for the displayed short integral models.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral.iff_rank_existence_and_finite_rank :
    ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral ↔
      ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral ∧
        ∀ C : ClayShortIntegralModel,
          WeierstrassCurve.rank (C.weierstrass_curve.baseChange ℚ) ≠ (⊤ : ℕ∞) := by
  constructor
  · intro h
    refine ⟨h.rank_existence, ?_⟩
    intro C
    rcases h C with ⟨data, r, hrank, c, hc⟩
    rw [← hrank]
    simp
  · intro h C
    rcases h.1 C with ⟨data, hbsd⟩
    have hOrder :
        analyticOrderAt data.L 1 =
          WeierstrassCurve.rank (C.weierstrass_curve.baseChange ℚ) := hbsd
    have hfinOrder : analyticOrderAt data.L 1 ≠ (⊤ : ℕ∞) := by
      simpa [hOrder] using h.2 C
    rcases data.exists_taylor_leading_term hfinOrder with ⟨r, hr, c, hc⟩
    exact ⟨data, r, by simpa [hOrder] using hr, c, hc⟩

/--
The existence-including rank statement is the universal continuation form together with existence
of a continuation for every nonsingular curve.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.Existence.iff_conjecture_and_models :
    ClayBirchSwinnertonDyer.Formulations.Rank.Existence ↔
      ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries ∧
        ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0, Nonempty (LSeriesData W hΔ) := by
  constructor
  · intro h
    refine ⟨h.conjecture, ?_⟩
    intro W hΔ
    rcases h W hΔ with ⟨data, _hdata⟩
    exact ⟨data⟩
  · rintro ⟨hbsd, hexists⟩ W hΔ
    rcases hexists W hΔ with ⟨data⟩
    exact ⟨data, hbsd W hΔ data⟩

/--
The existence-including Birch--Swinnerton-Dyer rank statement is the universal rank statement together with Wiles's
holomorphic-continuation input for `L(C,s)`.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.Existence.iff_conjecture_and_continuation :
    ClayBirchSwinnertonDyer.Formulations.Rank.Existence ↔
      ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries ∧ ClayBirchSwinnertonDyer.Support.LSeriesContinuation := by
  simpa [ClayBirchSwinnertonDyer.Support.LSeriesContinuation,
    ClayBirchSwinnertonDyer.Support.LSeriesContinuation.for_curve] using
      ClayBirchSwinnertonDyer.Formulations.Rank.Existence.iff_conjecture_and_models

/--
Completed-L-function rank form of Birch--Swinnerton-Dyer.

This is the same rank statement, but phrased for a completed L-function `L*`.  The equality with
the ordinary `L`-function rank statement follows from
`CompletedLSeriesData.order_lstar_eq`.
-/
def ClayBirchSwinnertonDyer.Formulations.Completed.Rank : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∀ data : CompletedLSeriesData W hΔ,
      analyticOrderAt data.lstar 1 = WeierstrassCurve.rank (W.baseChange ℚ)

/-- The ordinary rank statement implies the completed-L rank statement. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.completed
    (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) :
    ClayBirchSwinnertonDyer.Formulations.Completed.Rank := by
  intro W hΔ data
  rw [data.order_lstar_eq]
  exact hbsd W hΔ data.toLSeriesData

/--
For a fixed completed L-series, the ordinary and completed orders of vanishing give the same Birch--Swinnerton-Dyer
rank equality.
-/
theorem CompletedLSeriesData.rank_equality_iff_ordinary_lseries {W : WeierstrassCurve ℤ}
    {hΔ : W.Δ ≠ 0} (data : CompletedLSeriesData W hΔ) :
    analyticOrderAt data.lstar 1 = WeierstrassCurve.rank (W.baseChange ℚ) ↔
      analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ) := by
  rw [data.order_lstar_eq]

/--
The analytic leading coefficient of the completed L-function at `s = 1`.

`c` is a leading coefficient if locally
`L*(z) = (z - 1)^n g(z)`, with `g` analytic and nonzero at `1`, and `c = g(1)`.
-/
def CompletedLeadingCoeff {W : WeierstrassCurve ℤ}
    {hΔ : W.Δ ≠ 0} (data : CompletedLSeriesData W hΔ) (c : ℂ) : Prop :=
  ∃ n : ℕ,
    (n : ℕ∞) = analyticOrderAt data.lstar 1 ∧
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
          (∀ᶠ z in 𝓝 (1 : ℂ), data.lstar z = (z - 1) ^ n • g z) ∧
          c = g 1

/--
If the completed L-function has finite analytic order at `1`, then it has a leading coefficient
in the usual local Taylor-form sense.
-/
theorem CompletedLSeriesData.exists_leading_coeff {W : WeierstrassCurve ℤ}
    {hΔ : W.Δ ≠ 0} (data : CompletedLSeriesData W hΔ)
    (hfin : analyticOrderAt data.lstar 1 ≠ (⊤ : ℕ∞)) :
    ∃ c : ℂ, CompletedLeadingCoeff data c := by
  have hAnalytic : AnalyticAt ℂ data.lstar 1 := data.analytic_star 1
  have hEqNat : analyticOrderAt data.lstar 1 = analyticOrderNatAt data.lstar 1 := by
    simp [Nat.cast_analyticOrderNatAt (f := data.lstar) (z₀ := (1 : ℂ)) hfin]
  rcases (hAnalytic.analyticOrderAt_eq_natCast
      (n := analyticOrderNatAt data.lstar 1)).1 hEqNat with
    ⟨g, hg_an, hg_ne, hg_eq⟩
  have hOrderNat :
      (analyticOrderNatAt data.lstar 1 : ℕ∞) = analyticOrderAt data.lstar 1 := by
    simpa using Nat.cast_analyticOrderNatAt (f := data.lstar) (z₀ := (1 : ℂ)) hfin
  exact ⟨g 1, analyticOrderNatAt data.lstar 1, hOrderNat, g, hg_an, hg_ne, hg_eq, rfl⟩

/-- A completed leading coefficient is nonzero. -/
theorem CompletedLeadingCoeff.ne_zero {W : WeierstrassCurve ℤ}
    {hΔ : W.Δ ≠ 0} {data : CompletedLSeriesData W hΔ} {c : ℂ}
    (hc : CompletedLeadingCoeff data c) :
    c ≠ 0 := by
  rcases hc with ⟨_n, _hOrder, g, _hg_an, hg_ne, _hg_eq, hc_eq⟩
  rw [hc_eq]
  exact hg_ne

/-- Finite analytic order gives a nonzero completed leading coefficient. -/
theorem CompletedLSeriesData.exists_nonzero_leading_coeff
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0} (data : CompletedLSeriesData W hΔ)
    (hfin : analyticOrderAt data.lstar 1 ≠ (⊤ : ℕ∞)) :
    ∃ c : ℂ, CompletedLeadingCoeff data c ∧ c ≠ 0 := by
  rcases data.exists_leading_coeff hfin with ⟨c, hc⟩
  exact ⟨c, hc, hc.ne_zero⟩

/-!
## Refined conjecture (Clay PDF, “Remarks 1”)

The Clay PDF also gives a refined leading-coefficient formula for a *completed* L-series `L*`.
We include that formula as a separate conjecture using the arithmetic invariants appearing in the
Clay statement.

**Warning: this section is a schema, not a statement of the refined conjecture.**  The
Tate--Shafarevich group, regulator, period and Tamagawa numbers are recorded as *unconstrained
data* (`RefinedInvariants`), and the completed L-function is pinned down only up to an arbitrary
nonvanishing factor near `s = 1` (`CompletedLSeriesData`).  Consequently
`ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment`, for an existentially chosen
`assignment`, reduces to the statement that the leading coefficient of `L*` at `s = 1` is a positive
real number: given any such coefficient `c`, choosing `Sha := Unit`, `period := 1`, all Tamagawa
factors `1` and `regulator := c * |C(ℚ)_tors|^2` produces *valid* invariants satisfying the formula.
A faithful refined conjecture requires actual definitions of these invariants and of the true
completed L-function, none of which exist in Mathlib yet.  The rank part of the conjecture is
unaffected by this warning.
-/

/-- The order of the torsion subgroup `C(ℚ)_tors`, as a natural number (`0` if infinite). -/
noncomputable def torsion_order (W : WeierstrassCurve ℤ) : ℕ :=
  Nat.card ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point))

/--
Under Mordell--Weil finite generation, the torsion subgroup of `C(ℚ)` is finite.

This is actual abelian-group theory from Mathlib: a finitely generated torsion abelian group is
finite, applied to the torsion subgroup of the Mordell--Weil group.
-/
theorem mordell_weil_torsion_subgroup_finite {W : WeierstrassCurve ℤ}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    Finite ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point)) := by
  classical
  haveI : AddGroup.FG ((W.baseChange ℚ).toProjective.Point) := by
    simpa [WeierstrassCurve.MordellWeil, WeierstrassCurve.MordellWeilGroup] using hMW
  haveI : Module.Finite ℤ ((W.baseChange ℚ).toProjective.Point) :=
    (Module.Finite.iff_addGroup_fg).2
      (by infer_instance : AddGroup.FG ((W.baseChange ℚ).toProjective.Point))
  let T : Submodule ℤ ((W.baseChange ℚ).toProjective.Point) :=
    Submodule.torsion ℤ ((W.baseChange ℚ).toProjective.Point)
  have hTfg : T.FG := by
    exact Submodule.FG.of_le_of_isNoetherian (T := (⊤ : Submodule ℤ ((W.baseChange ℚ).toProjective.Point)))
      (by simp)
  haveI : Module.Finite ℤ T := Module.Finite.of_fg hTfg
  haveI : Finite T := Module.finite_of_fg_torsion T (Submodule.torsion_isTorsion (R := ℤ))
  have hset :
      (T : Set ((W.baseChange ℚ).toProjective.Point)) =
        (AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point) : Set ((W.baseChange ℚ).toProjective.Point)) := by
    simpa [T] using
      congrArg
        (fun S : AddSubgroup ((W.baseChange ℚ).toProjective.Point) =>
          (S : Set ((W.baseChange ℚ).toProjective.Point)))
        (Submodule.torsion_int (G := ((W.baseChange ℚ).toProjective.Point)))
  exact Finite.of_equiv T (Equiv.setCongr hset)

/-- Under Mordell--Weil finite generation, the torsion order `|C(ℚ)_tors|` is positive. -/
theorem torsion_order_pos_of_mordell_weil {W : WeierstrassCurve ℤ}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    0 < torsion_order W := by
  classical
  haveI : Finite ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point)) :=
    mordell_weil_torsion_subgroup_finite (W := W) hMW
  haveI : Nonempty ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point)) :=
    ⟨0⟩
  simp [torsion_order]

/-- Under Mordell--Weil finite generation, the torsion denominator in refined Birch--Swinnerton-Dyer is nonzero. -/
theorem torsion_order_ne_zero_of_mordell_weil {W : WeierstrassCurve ℤ}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    torsion_order W ≠ 0 :=
  (torsion_order_pos_of_mordell_weil (W := W) hMW).ne'

/-- The finite set of bad-reduction primes `p | 2Δ`, built from the prime factors of `|2Δ|`. -/
noncomputable def bad_reduction_primes (W : WeierstrassCurve ℤ) : Finset Nat.Primes :=
  ((2 * W.Δ).natAbs.primeFactors.attach).image
    (fun p => (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))

/-- For nonsingular curves, the canonical bad-reduction set is exactly `{p : p | 2Δ}`. -/
theorem mem_bad_reduction_primes_iff_dvd_two_discriminant {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) (p : Nat.Primes) :
    p ∈ bad_reduction_primes W ↔ ((p : ℕ) : ℤ) ∣ (2 * W.Δ) := by
  classical
  let n : ℕ := (2 * W.Δ).natAbs
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact Int.natAbs_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hΔ)
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, _hq, hqeq⟩
    have hpq : p.1 = q.1 := congrArg Subtype.val hqeq.symm
    have hdivNat : p.1 ∣ n := by
      rw [hpq]
      exact Nat.dvd_of_mem_primeFactors q.2
    have hdivInt : ((p : ℕ) : ℤ) ∣ (n : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdivNat
    exact Int.dvd_natAbs.mp hdivInt
  · intro hp
    have hdivIntAbs : ((p : ℕ) : ℤ) ∣ (n : ℤ) :=
      Int.dvd_natAbs.mpr hp
    have hdivNat : (p : ℕ) ∣ n :=
      Int.natCast_dvd_natCast.mp hdivIntAbs
    have hmemNat : (p : ℕ) ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨p.2, hdivNat, hn0⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨⟨p.1, hmemNat⟩, Finset.mem_attach _ _, by simp⟩

/-- At a bad-reduction prime, the incomplete Euler product uses the omitted factor `1`. -/
theorem clay_euler_product_factor_eq_one_of_bad_reduction_prime
    {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) {p : Nat.Primes}
    (hp : p ∈ bad_reduction_primes W) (s : ℂ) :
    WeierstrassCurve.clay_euler_product_factor W p s = 1 := by
  have hdiv : ((p : ℕ) : ℤ) ∣ (2 * W.Δ) := (mem_bad_reduction_primes_iff_dvd_two_discriminant hΔ p).1 hp
  simp [WeierstrassCurve.clay_euler_product_factor, hdiv]

/-- At a good-reduction prime, the Euler factor is the explicit Clay factor. -/
theorem clay_euler_product_factor_eq_explicit_of_good_reduction_prime
    {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) {p : Nat.Primes}
    (hp : p ∉ bad_reduction_primes W) (s : ℂ) :
    WeierstrassCurve.clay_euler_product_factor W p s =
      ((1 : ℂ) - (WeierstrassCurve.frobenius_trace_coefficient W p : ℂ) * (p ^ (-s) : ℂ) +
        (p : ℂ) ^ (1 - 2 * s))⁻¹ := by
  have hnotdiv : ¬ ((p : ℕ) : ℤ) ∣ (2 * W.Δ) := by
    intro hdiv
    exact hp ((mem_bad_reduction_primes_iff_dvd_two_discriminant hΔ p).2 hdiv)
  simp [WeierstrassCurve.clay_euler_product_factor, hnotdiv]

/-- The incomplete L-series Euler product, split using the finite bad-reduction prime set. -/
theorem incomplete_lseries_eq_euler_product_split_bad_reduction_primes
    {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) (s : ℂ) :
    W.incomplete_lseries s =
      ∏' p : Nat.Primes,
        if p ∈ bad_reduction_primes W then
          (1 : ℂ)
        else
          ((1 : ℂ) - (WeierstrassCurve.frobenius_trace_coefficient W p : ℂ) * (p ^ (-s) : ℂ) +
            (p : ℂ) ^ (1 - 2 * s))⁻¹ := by
  rw [WeierstrassCurve.incomplete_lseries.eq_clay_euler_product]
  refine tprod_congr fun p => ?_
  by_cases hp : p ∈ bad_reduction_primes W
  · rw [if_pos hp, clay_euler_product_factor_eq_one_of_bad_reduction_prime hΔ hp s]
  · rw [if_neg hp, clay_euler_product_factor_eq_explicit_of_good_reduction_prime hΔ hp s]

/--
The arithmetic invariants appearing in the refined Birch--Swinnerton-Dyer formula (Clay PDF, “Remarks 1”).

Notation correspondence (PDF → Lean fields):
- `X_C` → `Sha`, recorded as a finite additive group datum
- `|X_C|` → `Sha_order`, tied to `Nat.card Sha`
- `R_∞` → `regulator`
- `w_∞` → `period`
- `w_p` → `tamagawa_factor p`
- `∏_{p | 2Δ} w_p` → `tamagawa_product`, using the canonical `bad_reduction_primes W`

**Warning (placeholder data).** None of these fields is defined from the curve: `Sha` is an
arbitrary finite abelian group, and `regulator`, `period`, `tamagawa_factor` are arbitrary reals
(constrained only to be positive by `RefinedInvariants.Valid`).  See the warning at the start of
this section.
-/
structure RefinedInvariants (W : WeierstrassCurve ℤ) where
  /-- The Tate-Shafarevich group datum; mathlib does not construct the actual group here. -/
  Sha : Type
  /-- Group structure on the recorded Tate-Shafarevich group datum. -/
  Sha_group : AddCommGroup Sha
  /-- Finiteness of the recorded Tate-Shafarevich group datum. -/
  Sha_finite : Finite Sha
  /-- The finite order `|Sha|` appearing in the refined formula. -/
  Sha_order : ℕ
  /-- The displayed order agrees with the finite cardinality of the recorded `Sha` datum. -/
  Sha_order_eq_card : Sha_order = Nat.card Sha
  regulator : ℝ
  period : ℝ
  /-- The Tamagawa number `wₚ` at a prime `p`. -/
  tamagawa_factor : Nat.Primes → ℝ

/-- The recorded Tate-Shafarevich order is positive because it is the order of a finite group. -/
theorem RefinedInvariants.sha_order_pos {W : WeierstrassCurve ℤ}
    (inv : RefinedInvariants W) : 0 < inv.Sha_order := by
  classical
  haveI : AddCommGroup inv.Sha := inv.Sha_group
  haveI : Finite inv.Sha := inv.Sha_finite
  haveI : Nonempty inv.Sha := ⟨0⟩
  rw [inv.Sha_order_eq_card]
  exact Finite.card_pos

/--
Validity and positivity requirements for the refined Birch--Swinnerton-Dyer arithmetic factors.

These conditions give the fields of `RefinedInvariants` their intended arithmetic shape: the
orders and local/global factors in the denominator/product are finite positive quantities, not
arbitrary real numbers.
-/
structure RefinedInvariants.Valid {W : WeierstrassCurve ℤ}
    (inv : RefinedInvariants W) : Prop where
  /-- The Tate--Shafarevich order factor is positive. -/
  Sha_order_pos : 0 < inv.Sha_order
  /-- The regulator is positive. -/
  regulator_pos : 0 < inv.regulator
  /-- The real period is positive. -/
  period_pos : 0 < inv.period
  /-- Each Tamagawa factor is positive. -/
  tamagawa_factor_pos : ∀ p : Nat.Primes, 0 < inv.tamagawa_factor p
  /-- The torsion order denominator is nonzero. -/
  torsion_order_ne_zero : torsion_order W ≠ 0

/-- The finite Tamagawa product `∏_{p | 2Δ} wₚ` (Clay PDF, “Remarks 1”). -/
noncomputable def RefinedInvariants.tamagawa_product {W : WeierstrassCurve ℤ}
    (inv : RefinedInvariants W) : ℝ :=
  ∏ p ∈ bad_reduction_primes W, inv.tamagawa_factor p

/--
Any finite set of primes satisfying the same divisibility specification gives the canonical
Tamagawa product.
-/
theorem RefinedInvariants.tamagawa_product_eq_bad_prime_specification {W : WeierstrassCurve ℤ}
    (hΔ : W.Δ ≠ 0) (inv : RefinedInvariants W) (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, p ∈ S ↔ ((p : ℕ) : ℤ) ∣ (2 * W.Δ)) :
    inv.tamagawa_product = ∏ p ∈ S, inv.tamagawa_factor p := by
  have hS_eq : S = bad_reduction_primes W := by
    ext p
    rw [hS p, mem_bad_reduction_primes_iff_dvd_two_discriminant hΔ p]
  rw [RefinedInvariants.tamagawa_product, ← hS_eq]

namespace RefinedInvariants.Valid

/--
Build valid refined invariants from positivity of the arithmetic factors plus the Mordell--Weil
finite-generation hypothesis.
-/
theorem of_mordell_weil {W : WeierstrassCurve ℤ} {inv : RefinedInvariants W}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ))
    (hSha : 0 < inv.Sha_order)
    (hReg : 0 < inv.regulator)
    (hPeriod : 0 < inv.period)
    (hTam : ∀ p : Nat.Primes, 0 < inv.tamagawa_factor p) :
    RefinedInvariants.Valid inv :=
  { Sha_order_pos := hSha
    regulator_pos := hReg
    period_pos := hPeriod
    tamagawa_factor_pos := hTam
    torsion_order_ne_zero := torsion_order_ne_zero_of_mordell_weil (W := W) hMW }

/-- Valid refined invariants have nonzero real torsion denominator. -/
theorem torsion_denominator_ne_zero {W : WeierstrassCurve ℤ} {inv : RefinedInvariants W}
    (h : RefinedInvariants.Valid inv) :
    ((torsion_order W : ℝ) ^ 2) ≠ 0 := by
  have hreal : (torsion_order W : ℝ) ≠ 0 := by
    exact_mod_cast h.torsion_order_ne_zero
  exact pow_ne_zero 2 hreal

/-- The Tamagawa product of valid refined invariants is nonnegative. -/
theorem tamagawa_product_nonneg {W : WeierstrassCurve ℤ} {inv : RefinedInvariants W}
    (h : RefinedInvariants.Valid inv) :
    0 ≤ inv.tamagawa_product := by
  classical
  dsimp [RefinedInvariants.tamagawa_product]
  exact Finset.prod_nonneg fun p _hp => le_of_lt (h.tamagawa_factor_pos p)

/-- The Tamagawa product of valid refined invariants is positive. -/
theorem tamagawa_product_pos {W : WeierstrassCurve ℤ} {inv : RefinedInvariants W}
    (h : RefinedInvariants.Valid inv) :
    0 < inv.tamagawa_product := by
  classical
  dsimp [RefinedInvariants.tamagawa_product]
  exact Finset.prod_pos fun p _hp => h.tamagawa_factor_pos p

end RefinedInvariants.Valid

/-- Arithmetic right-hand side in the refined Birch--Swinnerton-Dyer leading-coefficient formula. -/
noncomputable def RefinedInvariants.predicted_coeff {W : WeierstrassCurve ℤ}
    (inv : RefinedInvariants W) : ℝ :=
  ((inv.Sha_order : ℝ) * inv.regulator * inv.period * inv.tamagawa_product) /
    ((torsion_order W : ℝ) ^ 2)

/-- For valid refined invariants, the predicted leading coefficient is positive. -/
theorem RefinedInvariants.predicted_coeff_pos {W : WeierstrassCurve ℤ}
    {inv : RefinedInvariants W} (h : RefinedInvariants.Valid inv) :
    0 < inv.predicted_coeff := by
  dsimp [RefinedInvariants.predicted_coeff]
  have hSha : 0 < (inv.Sha_order : ℝ) := by exact_mod_cast h.Sha_order_pos
  have hTam : 0 < inv.tamagawa_product := h.tamagawa_product_pos
  have hden : 0 < ((torsion_order W : ℝ) ^ 2) := by
    have hreal : (torsion_order W : ℝ) ≠ 0 := by exact_mod_cast h.torsion_order_ne_zero
    exact sq_pos_of_ne_zero hreal
  have hnum : 0 < (inv.Sha_order : ℝ) * inv.regulator * inv.period * inv.tamagawa_product := by
    exact mul_pos (mul_pos (mul_pos hSha h.regulator_pos) h.period_pos) hTam
  exact div_pos hnum hden

/-- For valid refined invariants, the predicted leading coefficient is nonzero. -/
theorem RefinedInvariants.predicted_coeff_ne_zero {W : WeierstrassCurve ℤ}
    {inv : RefinedInvariants W} (h : RefinedInvariants.Valid inv) :
    inv.predicted_coeff ≠ 0 :=
  ne_of_gt (inv.predicted_coeff_pos h)

/--
For Mordell--Weil curves, positivity of the visible refined Birch--Swinnerton-Dyer factors is enough to prove the
predicted leading coefficient is positive; the torsion denominator is derived from finite
generation of the Mordell--Weil group.
-/
theorem RefinedInvariants.predicted_coeff_pos_mordell_weil
    {W : WeierstrassCurve ℤ} {inv : RefinedInvariants W}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ))
    (hSha : 0 < inv.Sha_order)
    (hReg : 0 < inv.regulator)
    (hPeriod : 0 < inv.period)
    (hTam : ∀ p : Nat.Primes, 0 < inv.tamagawa_factor p) :
    0 < inv.predicted_coeff :=
  inv.predicted_coeff_pos
    (RefinedInvariants.Valid.of_mordell_weil hMW hSha hReg hPeriod hTam)

/--
Choice of the refined arithmetic invariants for each nonsingular integral Weierstrass model.

The Clay refined formula uses the Tate--Shafarevich order, regulator, period, and Tamagawa factors
attached to the curve.  The assignment makes that curvewise choice explicit.
-/
structure RefinedInvariantAssignment where
  invariants : ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → RefinedInvariants W
  well_formed : ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    RefinedInvariants.Valid (invariants W hΔ)

/-- Leading-coefficient formula for one completed L-series and one chosen invariant datum. -/
def RefinedBirchSwinnertonDyerFormula {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0}
    (data : CompletedLSeriesData W hΔ) (inv : RefinedInvariants W) : Prop :=
  ∃ c : ℝ,
    CompletedLeadingCoeff data (c : ℂ) ∧
      c = inv.predicted_coeff

/--
Refined Birch–Swinnerton–Dyer conjecture: the rank part together with the predicted leading
coefficient for the completed L-series.

We express the leading coefficient identity in the same algebraic shape as the PDF:
`c* = |X_C| R_∞ w_∞ ∏ w_p / |C(ℚ)_tors|^2`.

**Warning.** Because `assignment` and `CompletedLSeriesData` are unconstrained placeholder data,
`∃ assignment, Refined.Conjecture assignment` has no arithmetic content beyond the rank part and
the positivity of the leading coefficient; see the warning at the start of this section.  This
proposition is not a Millennium target of this repository.
-/
def ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture (assignment : RefinedInvariantAssignment) : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0,
    ∀ data : CompletedLSeriesData W hΔ,
      analyticOrderAt data.lstar 1 = WeierstrassCurve.rank (W.baseChange ℚ) ∧
        RefinedBirchSwinnertonDyerFormula data (assignment.invariants W hΔ)

/--
Refined Birch--Swinnerton-Dyer with completed L-function existence included for every nonsingular integral
Weierstrass model.
-/
def ClayBirchSwinnertonDyer.Formulations.Refined.WithLSeries
    (assignment : RefinedInvariantAssignment) : Prop :=
  ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment ∧
    ∀ W : WeierstrassCurve ℤ, ∀ hΔ : W.Δ ≠ 0, Nonempty (CompletedLSeriesData W hΔ)

/-- The existence-including refined statement contains the universal refined formula. -/
theorem ClayBirchSwinnertonDyer.Formulations.Refined.WithLSeries.conjecture
    {assignment : RefinedInvariantAssignment}
    (h : ClayBirchSwinnertonDyer.Formulations.Refined.WithLSeries assignment) :
    ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment :=
  h.1

/-- The existence-including refined statement provides a completed L-function for each curve. -/
theorem ClayBirchSwinnertonDyer.Formulations.Refined.WithLSeries.exists_completed_lseries
    {assignment : RefinedInvariantAssignment}
    (h : ClayBirchSwinnertonDyer.Formulations.Refined.WithLSeries assignment)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    Nonempty (CompletedLSeriesData W hΔ) :=
  h.2 W hΔ

/-!
The former proposition `Refined.AllInvariants` (the refined formula for *every* valid choice of
invariants) was removed: since the invariants are free data, it was refuted by any single completed
L-series datum with two different regulators.
-/

/-- The refined Birch--Swinnerton-Dyer conjecture contains the completed-L rank statement as its first component. -/
theorem ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture.completed_rank
    {assignment : RefinedInvariantAssignment}
    (hrefined : ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment) :
    ClayBirchSwinnertonDyer.Formulations.Completed.Rank := by
  intro W hΔ data
  exact (hrefined W hΔ data).1

/--
In the refined Birch--Swinnerton-Dyer statement, the analytic leading coefficient is positive for the chosen
arithmetic invariants.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture.exists_positive_coeff
    {assignment : RefinedInvariantAssignment}
    (h : ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment)
    {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : CompletedLSeriesData W hΔ) :
    ∃ c : ℝ, CompletedLeadingCoeff data (c : ℂ) ∧
      c = (assignment.invariants W hΔ).predicted_coeff ∧ 0 < c := by
  rcases (h W hΔ data).2 with ⟨c, hc, heq⟩
  refine ⟨c, hc, heq, ?_⟩
  rw [heq]
  exact (assignment.invariants W hΔ).predicted_coeff_pos
    (assignment.well_formed W hΔ)

/-- The refined Birch--Swinnerton-Dyer leading coefficient is nonzero for the chosen arithmetic invariants. -/
theorem ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture.exists_nonzero_coeff
    {assignment : RefinedInvariantAssignment}
    (h : ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment)
    {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : CompletedLSeriesData W hΔ) :
    ∃ c : ℝ, CompletedLeadingCoeff data (c : ℂ) ∧
      c = (assignment.invariants W hΔ).predicted_coeff ∧ c ≠ 0 := by
  rcases h.exists_positive_coeff hΔ data with ⟨c, hc, heq, hpos⟩
  exact ⟨c, hc, heq, ne_of_gt hpos⟩

/-- The analytic completed leading coefficient obtained from refined Birch--Swinnerton-Dyer is nonzero. -/
theorem ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture.exists_nonzero_leading_coeff
    {assignment : RefinedInvariantAssignment}
    (h : ClayBirchSwinnertonDyer.Formulations.Refined.Conjecture assignment)
    {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : CompletedLSeriesData W hΔ) :
    ∃ c : ℝ, CompletedLeadingCoeff data (c : ℂ) ∧ (c : ℂ) ≠ 0 := by
  rcases h.exists_nonzero_coeff hΔ data with ⟨c, hc, _heq, hne⟩
  exact ⟨c, hc, by exact_mod_cast hne⟩

/-!
## Easy analytic consequences (proved)

These are unconditional *lemmas* about `analyticOrderAt`, proving the “in particular …” part of
the Clay write-up at the level of vanishing order vs. rank.

We also prove the final step “rank ≠ 0 ↔ C(ℚ) infinite” from the standard Mordell–Weil finite
generation hypothesis (`WeierstrassCurve.MordellWeil`).
-/

/-- For one curve and one chosen analytic continuation, Birch--Swinnerton-Dyer implies `L(E,1)=0 ↔ rank(E(ℚ))≠0`. -/
theorem BirchSwinnertonDyerRankEqualityForModel.vanishes_at_one_iff_positive_rank
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0} {data : LSeriesData W hΔ}
    (hbsd : BirchSwinnertonDyerRankEqualityForModel W hΔ data) :
    data.L 1 = 0 ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 := by
  have hAnalytic : AnalyticAt ℂ data.L 1 := data.analytic 1
  have hOrder : analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ) := hbsd
  have hOrder_ne_zero_iff : analyticOrderAt data.L 1 ≠ 0 ↔ data.L 1 = 0 := by
    -- `analyticOrderAt_ne_zero` says `order ≠ 0 ↔ analytic ∧ value = 0`.
    simpa [hAnalytic] using (analyticOrderAt_ne_zero (f := data.L) (z₀ := (1 : ℂ)))
  constructor
  · intro hL
    have : analyticOrderAt data.L 1 ≠ 0 := hOrder_ne_zero_iff.mpr hL
    simpa [hOrder] using this
  · intro hr
    have : analyticOrderAt data.L 1 ≠ 0 := by
      simpa [hOrder] using hr
    exact hOrder_ne_zero_iff.mp this

/-- Under Birch--Swinnerton-Dyer, vanishing of `L(E, 1)` is equivalent to positive Mordell--Weil rank. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.vanishes_at_one_iff_positive_rank
    (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : LSeriesData W hΔ) :
    data.L 1 = 0 ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 := by
  exact BirchSwinnertonDyerRankEqualityForModel.vanishes_at_one_iff_positive_rank (hbsd W hΔ data)

/--
If the rank is finite (i.e. not `⊤` in `ℕ∞`), then the order statement can be unpacked into the
explicit “Taylor expansion” form used in the Clay PDF:
`L(s) = (s - 1)^n • g(s)` near `s = 1` with `g(1) ≠ 0`.

This is a general lemma about `analyticOrderAt`, specialized to the Birch--Swinnerton-Dyer context.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.exists_taylor_form_of_finite_rank
    (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : LSeriesData W hΔ)
    (hfin : WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)) :
    ∃ n : ℕ,
      (n : ℕ∞) = WeierstrassCurve.rank (W.baseChange ℚ) ∧
        ∃ g : ℂ → ℂ,
          AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
            ∀ᶠ z in 𝓝 (1 : ℂ), data.L z = (z - 1) ^ n • g z := by
  have hAnalytic : AnalyticAt ℂ data.L 1 := data.analytic 1
  have hOrder : analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ) :=
    hbsd W hΔ data
  have hOrderNeTop : analyticOrderAt data.L 1 ≠ (⊤ : ℕ∞) := by
    simpa [hOrder] using hfin
  refine ⟨analyticOrderNatAt data.L 1, ?_, ?_⟩
  · have hn : (analyticOrderNatAt data.L 1 : ℕ∞) = analyticOrderAt data.L 1 := by
      simpa using (Nat.cast_analyticOrderNatAt (f := data.L) (z₀ := (1 : ℂ)) hOrderNeTop)
    simp [hn, hOrder]
  · have hEqNat : analyticOrderAt data.L 1 = analyticOrderNatAt data.L 1 := by
      simp [Nat.cast_analyticOrderNatAt (f := data.L) (z₀ := (1 : ℂ)) hOrderNeTop]
    rcases (hAnalytic.analyticOrderAt_eq_natCast (n := analyticOrderNatAt data.L 1)).1 hEqNat with
      ⟨g, hg_an, hg_ne, hg_eq⟩
    exact ⟨g, hg_an, hg_ne, hg_eq⟩

/-!
## Mordell–Weil finiteness vs. rank (proved under `MordellWeil`)

The Clay PDF’s “in particular” consequence uses the Mordell–Weil theorem: for a finitely
generated abelian group, `rank = 0` iff the group is finite.

Mathlib already has the necessary general algebra for finitely generated abelian groups; we
instantiate it here for the Mordell–Weil group of a Weierstrass curve.
-/

/-- Mordell--Weil finite-generation hypothesis for one integral Weierstrass curve. -/
def MordellWeil.FiniteGeneration (W : WeierstrassCurve ℤ) : Prop :=
  WeierstrassCurve.MordellWeil (W.baseChange ℚ)

/--
Mordell--Weil decomposition for one curve:
`C(ℚ) ≃ ℤ^r × C(ℚ)_tors`, with finite torsion and the recorded `r` equal to the
Mordell--Weil rank used in the Birch--Swinnerton-Dyer statement.
-/
def MordellWeil.Decomposition (W : WeierstrassCurve ℤ) : Prop :=
  MordellWeil.FiniteGeneration W ∧
    WeierstrassCurve.MordellWeilDecomposition (W.baseChange ℚ)

/-- Global nonsingular-curve form of the Clay Mordell--Weil decomposition sentence. -/
def MordellWeil.Decomposition.Global : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    MordellWeil.Decomposition W

/-- Global nonsingular-curve form of finite Mordell--Weil rank. -/
def MordellWeil.FiniteRank.Global : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)

/--
Rank-zero consequence of Mordell--Weil finite generation:
rank zero exactly when the rational point set is finite.
-/
def MordellWeil.RankZeroFinitePointCriterion (W : WeierstrassCurve ℤ) : Prop :=
  MordellWeil.FiniteGeneration W →
    (WeierstrassCurve.rank (W.baseChange ℚ) = 0 ↔
      Finite ((W.baseChange ℚ).toProjective.Point))

/--
Torsion consequence of Mordell--Weil finite generation:
the torsion subgroup `C(ℚ)_tors` is finite.
-/
def MordellWeil.TorsionFinite (W : WeierstrassCurve ℤ) : Prop :=
  MordellWeil.FiniteGeneration W →
    Finite ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point))

/-- Global nonsingular-curve form of the Clay Mordell--Weil rank-zero/finite-points consequence. -/
def MordellWeil.RankZeroFinitePointCriterion.Global : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    MordellWeil.RankZeroFinitePointCriterion W

/-- Global nonsingular-curve form of finite torsion in `C(ℚ)_tors`. -/
def MordellWeil.TorsionFinite.Global : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    MordellWeil.TorsionFinite W

/-- A Clay decomposition witness carries Mordell--Weil finite generation. -/
theorem MordellWeil.Decomposition.finite_generation {W : WeierstrassCurve ℤ}
    (h : MordellWeil.Decomposition W) :
    WeierstrassCurve.MordellWeil (W.baseChange ℚ) :=
  h.1

/-- A Clay decomposition witness gives finite Mordell--Weil rank. -/
theorem MordellWeil.Decomposition.finite_rank {W : WeierstrassCurve ℤ}
    (h : MordellWeil.Decomposition W) :
    WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞) := by
  rcases h.2 with ⟨data⟩
  exact data.rank_finite

/-- A Clay decomposition witness gives finite torsion in `C(ℚ)_tors`. -/
theorem MordellWeil.Decomposition.finite_torsion {W : WeierstrassCurve ℤ}
    (h : MordellWeil.Decomposition W) :
    Finite ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point)) := by
  rcases h.2 with ⟨data⟩
  simpa [WeierstrassCurve.mordell_weil_torsion_subgroup,
    WeierstrassCurve.MordellWeilGroup] using data.torsion_finite

/-- The Mordell-Weil decomposition gives finite torsion. -/
theorem MordellWeil.Decomposition.torsion_finite
    {W : WeierstrassCurve ℤ} (h : MordellWeil.Decomposition W) :
    MordellWeil.TorsionFinite W := by
  intro _hMW
  exact h.finite_torsion

/-- Global decomposition implies finite Mordell--Weil rank. -/
theorem MordellWeil.Decomposition.Global.finite_rank
    (h : MordellWeil.Decomposition.Global) :
    MordellWeil.FiniteRank.Global := by
  intro W hΔ
  exact (h W hΔ).finite_rank

/-- Global decomposition implies finite torsion for every nonsingular integral model. -/
theorem MordellWeil.Decomposition.Global.finite_torsion
    (h : MordellWeil.Decomposition.Global) :
    MordellWeil.TorsionFinite.Global := by
  intro W hΔ
  exact (h W hΔ).torsion_finite

/-- A finitely generated Mordell--Weil group has rank zero exactly when its point set is finite. -/
theorem MordellWeil.rank_zero_iff_finite_points {W : WeierstrassCurve ℤ}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    WeierstrassCurve.rank (W.baseChange ℚ) = 0 ↔ Finite ((W.baseChange ℚ).toProjective.Point) := by
  classical
  let G : Type := (W.baseChange ℚ).toProjective.Point
  haveI : AddGroup.FG G := by
    simpa [WeierstrassCurve.MordellWeil, WeierstrassCurve.MordellWeilGroup, G] using hMW
  let Q : Type := G ⧸ AddCommGroup.torsion G
  haveI : AddGroup.FG Q := by
    dsimp [Q]
    infer_instance
  haveI : Module.Finite ℤ Q :=
    (Module.Finite.iff_addGroup_fg).2 (by infer_instance : AddGroup.FG Q)
  haveI : IsAddTorsionFree Q := by
    dsimp [Q]
    infer_instance
  haveI : NoZeroSMulDivisors ℤ Q := by infer_instance
  haveI : Module.Free ℤ Q := by infer_instance
  constructor
  · intro hRank0
    have hRankCard : Module.rank ℚ (TensorProduct ℤ ℚ Q) = 0 := by
      have hto : Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ Q)) = 0 := by
        have h' := hRank0
        unfold WeierstrassCurve.rank at h'
        dsimp [WeierstrassCurve.MordellWeilGroup, G, Q] at h'
        exact h'
      exact (Cardinal.toENat_eq_zero).1 hto
    have hBase :
        Module.rank ℚ (TensorProduct ℤ ℚ Q) = Cardinal.lift (Module.rank ℤ Q) := by
      exact Module.rank_baseChange (R := ℚ) (S := ℤ) (M' := Q)
    have hRankZ : Module.rank ℤ Q = 0 := by
      simpa [hBase] using hRankCard
    have hQsub : Subsingleton Q :=
      (rank_zero_iff (R := ℤ) (M := Q)).1 hRankZ
    have hTors : AddMonoid.IsTorsion G := by
      intro g
      haveI : Subsingleton Q := hQsub
      have hgQ : (QuotientAddGroup.mk g : Q) = 0 := Subsingleton.elim _ _
      have hgT : g ∈ AddCommGroup.torsion G :=
        (QuotientAddGroup.eq_zero_iff (N := AddCommGroup.torsion G) g).1 hgQ
      exact (AddCommGroup.mem_torsion g).1 hgT
    haveI : Finite G := AddCommGroup.finite_of_fg_torsion (G := G) hTors
    simpa [G] using (show Finite G from (by infer_instance))
  · intro hFin
    haveI : Finite G := by
      simpa [G] using hFin
    haveI : Finite Q := by
      dsimp [Q]
      infer_instance
    have hzero : ∀ q : Q, q = 0 := by
      intro q
      obtain ⟨n, hnpos, hnq⟩ :=
        (isOfFinAddOrder_of_finite q).exists_nsmul_eq_zero
      have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hnpos
      have hinj : Function.Injective fun a : Q => n • a :=
        IsAddTorsionFree.nsmul_right_injective (M := Q) hn0
      have : n • q = n • (0 : Q) := by simpa using hnq
      exact hinj this
    haveI : Subsingleton Q := (subsingleton_iff_forall_eq 0).2 hzero
    haveI : Subsingleton (TensorProduct ℤ ℚ Q) := by infer_instance
    have hRankCard : Module.rank ℚ (TensorProduct ℤ ℚ Q) = 0 :=
      (rank_zero_iff (R := ℚ) (M := TensorProduct ℤ ℚ Q)).2 (by infer_instance)
    have hto : Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ Q)) = 0 :=
      (Cardinal.toENat_eq_zero).2 hRankCard
    unfold WeierstrassCurve.rank
    dsimp [WeierstrassCurve.MordellWeilGroup, G, Q]
    exact hto

/-- A Clay decomposition witness gives rank zero iff finitely many rational points. -/
theorem MordellWeil.Decomposition.rank_zero_iff_finite_points
    {W : WeierstrassCurve ℤ} (h : MordellWeil.Decomposition W) :
    WeierstrassCurve.rank (W.baseChange ℚ) = 0 ↔
      Finite ((W.baseChange ℚ).toProjective.Point) :=
  MordellWeil.rank_zero_iff_finite_points (W := W) h.finite_generation

/-- The Mordell-Weil decomposition gives the rank-zero/finite-points criterion. -/
theorem MordellWeil.Decomposition.rank_zero_finite_point_criterion
    {W : WeierstrassCurve ℤ} (h : MordellWeil.Decomposition W) :
    MordellWeil.RankZeroFinitePointCriterion W := by
  intro _hMW
  exact h.rank_zero_iff_finite_points

/-- Global decomposition gives the rank-zero/finite-points criterion for every nonsingular model. -/
theorem MordellWeil.Decomposition.Global.rank_zero_finite_point_criterion
    (h : MordellWeil.Decomposition.Global) :
    MordellWeil.RankZeroFinitePointCriterion.Global := by
  intro W hΔ
  exact (h W hΔ).rank_zero_finite_point_criterion

/-- The Mordell--Weil rank-zero/finite-points consequence for one curve. -/
theorem MordellWeil.rank_zero_finite_point_criterion {W : WeierstrassCurve ℤ} :
    MordellWeil.RankZeroFinitePointCriterion W := by
  intro hMW
  exact MordellWeil.rank_zero_iff_finite_points (W := W) hMW

/-- The Mordell--Weil rank-zero/finite-points consequence for all nonsingular curves. -/
theorem MordellWeil.rank_zero_finite_point_criterion_global :
    MordellWeil.RankZeroFinitePointCriterion.Global := by
  intro W _hΔ
  exact MordellWeil.rank_zero_finite_point_criterion (W := W)

/-- The finite-torsion consequence for one curve. -/
theorem MordellWeil.torsion_finite {W : WeierstrassCurve ℤ} :
    MordellWeil.TorsionFinite W := by
  intro hMW
  exact mordell_weil_torsion_subgroup_finite (W := W) hMW

/-- The finite-torsion consequence for all nonsingular curves. -/
theorem MordellWeil.torsion_finite_global :
    MordellWeil.TorsionFinite.Global := by
  intro W _hΔ
  exact MordellWeil.torsion_finite (W := W)

/--
Under finite generation of the Mordell–Weil group, “rank ≠ 0” is equivalent to “infinitely many
rational points”.
-/
theorem MordellWeil.infinite_points_iff_rank_ne_zero {W : WeierstrassCurve ℤ}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    Infinite ((W.baseChange ℚ).toProjective.Point) ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 := by
  have hFin :
      WeierstrassCurve.rank (W.baseChange ℚ) = 0 ↔ Finite ((W.baseChange ℚ).toProjective.Point) :=
    MordellWeil.rank_zero_iff_finite_points (W := W) hMW
  constructor
  · intro hInf
    have : ¬ Finite ((W.baseChange ℚ).toProjective.Point) :=
      (not_finite_iff_infinite).2 hInf
    exact fun h0 => this (hFin.mp h0)
  · intro hne
    have : ¬ Finite ((W.baseChange ℚ).toProjective.Point) := by
      intro hF
      exact hne (hFin.mpr hF)
    exact (not_finite_iff_infinite).1 this

/--
Nonzero-rank consequence of Mordell--Weil finite generation:
positive/nonzero Mordell--Weil rank exactly when `C(ℚ)` is infinite.
-/
def MordellWeil.PositiveRankInfinitePointCriterion (W : WeierstrassCurve ℤ) : Prop :=
  MordellWeil.FiniteGeneration W →
    (WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 ↔
      Infinite ((W.baseChange ℚ).toProjective.Point))

/-- Global nonsingular-curve form of nonzero Mordell--Weil rank iff infinitely many points. -/
def MordellWeil.PositiveRankInfinitePointCriterion.Global : Prop :=
  ∀ W : WeierstrassCurve ℤ, ∀ _hΔ : W.Δ ≠ 0,
    MordellWeil.PositiveRankInfinitePointCriterion W

/-- The nonzero-rank/infinite-points consequence for one curve. -/
theorem MordellWeil.rank_ne_zero_iff_infinite_points {W : WeierstrassCurve ℤ} :
    MordellWeil.PositiveRankInfinitePointCriterion W := by
  intro hMW
  exact (MordellWeil.infinite_points_iff_rank_ne_zero (W := W) hMW).symm

/-- The nonzero-rank/infinite-points consequence for all nonsingular curves. -/
theorem MordellWeil.rank_ne_zero_infinite_point_criterion_global :
    MordellWeil.PositiveRankInfinitePointCriterion.Global := by
  intro W _hΔ
  exact MordellWeil.rank_ne_zero_iff_infinite_points (W := W)

/-- A Clay decomposition witness gives nonzero rank iff infinitely many rational points. -/
theorem MordellWeil.Decomposition.rank_ne_zero_iff_infinite_points
    {W : WeierstrassCurve ℤ} (h : MordellWeil.Decomposition W) :
    WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 ↔
      Infinite ((W.baseChange ℚ).toProjective.Point) :=
  (MordellWeil.infinite_points_iff_rank_ne_zero (W := W) h.finite_generation).symm

/-- The Mordell-Weil decomposition gives the nonzero-rank/infinite-points criterion. -/
theorem MordellWeil.Decomposition.rank_ne_zero_infinite_point_criterion
    {W : WeierstrassCurve ℤ} (h : MordellWeil.Decomposition W) :
    MordellWeil.PositiveRankInfinitePointCriterion W := by
  intro _hMW
  exact h.rank_ne_zero_iff_infinite_points

/-- Global decomposition implies the nonzero-rank/infinite-points consequence. -/
theorem MordellWeil.Decomposition.Global.rank_ne_zero_infinite_point_criterion
    (h : MordellWeil.Decomposition.Global) :
    MordellWeil.PositiveRankInfinitePointCriterion.Global := by
  intro W hΔ
  exact (h W hΔ).rank_ne_zero_infinite_point_criterion

/--
For one curve and one chosen analytic continuation, Birch--Swinnerton-Dyer plus Mordell--Weil finite generation gives
the Clay PDF consequence `L(C,1)=0 ↔ C(ℚ)` is infinite.
-/
theorem BirchSwinnertonDyerRankEqualityForModel.vanishes_at_one_iff_infinite_points
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0} {data : LSeriesData W hΔ}
    (hbsd : BirchSwinnertonDyerRankEqualityForModel W hΔ data)
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    data.L 1 = 0 ↔ Infinite ((W.baseChange ℚ).toProjective.Point) := by
  have hRank :
      data.L 1 = 0 ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 :=
    hbsd.vanishes_at_one_iff_positive_rank
  exact hRank.trans (MordellWeil.infinite_points_iff_rank_ne_zero (W := W) hMW).symm

/--
“`L(1) = 0` iff `C(ℚ)` is infinite”, as stated in the Clay write-up, under the assumptions
`ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries` and Mordell–Weil finite generation.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.vanishes_at_one_iff_infinite_points
     (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
     (data : LSeriesData W hΔ) (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
     data.L 1 = 0 ↔ Infinite ((W.baseChange ℚ).toProjective.Point) := by
  exact BirchSwinnertonDyerRankEqualityForModel.vanishes_at_one_iff_infinite_points (hbsd W hΔ data) hMW

/-- Logical complement of the Clay “`L(1)=0` iff infinitely many points” statement. -/
theorem Iff.ne_zero_iff_finite
    {α : Type} {z : ℂ} (h : z = 0 ↔ Infinite α) :
    z ≠ 0 ↔ Finite α := by
  constructor
  · intro hz
    exact not_infinite_iff_finite.mp (fun hInf => hz (h.mpr hInf))
  · intro hFin hz
    exact (not_finite_iff_infinite.mpr (h.mp hz)) hFin

/--
For one curve and one chosen analytic continuation, Birch--Swinnerton-Dyer plus Mordell--Weil finite generation gives
the Clay PDF nonvanishing consequence: `L(C,1) ≠ 0` iff `C(ℚ)` is finite.
-/
theorem BirchSwinnertonDyerRankEqualityForModel.nonvanishing_at_one_iff_finite_points
    {W : WeierstrassCurve ℤ} {hΔ : W.Δ ≠ 0} {data : LSeriesData W hΔ}
    (hbsd : BirchSwinnertonDyerRankEqualityForModel W hΔ data)
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    data.L 1 ≠ 0 ↔ Finite ((W.baseChange ℚ).toProjective.Point) :=
  Iff.ne_zero_iff_finite
    (hbsd.vanishes_at_one_iff_infinite_points hMW)

/--
“`L(1) ≠ 0` iff `C(ℚ)` is finite”, as stated in the Clay write-up, under Birch--Swinnerton-Dyer and
Mordell--Weil finite generation.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.nonvanishing_at_one_iff_finite_points
     (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
     (data : LSeriesData W hΔ) (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
     data.L 1 ≠ 0 ↔ Finite ((W.baseChange ℚ).toProjective.Point) :=
  BirchSwinnertonDyerRankEqualityForModel.nonvanishing_at_one_iff_finite_points (hbsd W hΔ data) hMW

/--
Clay PDF “in particular” consequence, globally:
`L(C,1)=0` iff `C(ℚ)` is infinite, for every nonsingular integral Weierstrass model and every
chosen analytic continuation, with Mordell--Weil finite generation explicit.
-/
def ClayBirchSwinnertonDyer.Consequences.PointCriteria.VanishingIffInfinite : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (data : LSeriesData W hΔ),
    WeierstrassCurve.MordellWeil (W.baseChange ℚ) →
      (data.L 1 = 0 ↔ Infinite ((W.baseChange ℚ).toProjective.Point))

/--
Clay PDF “in particular” consequence for the displayed short integral models
`y^2 = x^3 + ax + b`.
-/
def ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralVanishingIffInfinite : Prop :=
  ∀ (C : ClayShortIntegralModel)
    (data : LSeriesData C.weierstrass_curve C.nonsingular_weierstrass_curve),
    WeierstrassCurve.MordellWeil (C.weierstrass_curve.baseChange ℚ) →
      (data.L 1 = 0 ↔ Infinite ((C.weierstrass_curve.baseChange ℚ).toProjective.Point))

/--
Clay PDF “in particular” nonvanishing consequence:
`L(C,1) ≠ 0` iff `C(ℚ)` is finite.
-/
def ClayBirchSwinnertonDyer.Consequences.PointCriteria.NonvanishingIffFinite : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (data : LSeriesData W hΔ),
    WeierstrassCurve.MordellWeil (W.baseChange ℚ) →
      (data.L 1 ≠ 0 ↔ Finite ((W.baseChange ℚ).toProjective.Point))

/--
Clay PDF “in particular” nonvanishing consequence for the displayed short integral models.
-/
def ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralNonvanishingIffFinite : Prop :=
  ∀ (C : ClayShortIntegralModel)
    (data : LSeriesData C.weierstrass_curve C.nonsingular_weierstrass_curve),
    WeierstrassCurve.MordellWeil (C.weierstrass_curve.baseChange ℚ) →
      (data.L 1 ≠ 0 ↔ Finite ((C.weierstrass_curve.baseChange ℚ).toProjective.Point))

/-- The Birch--Swinnerton-Dyer rank statement yields the PDF's “in particular” consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.vanishes_iff_infinite_points
    (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.VanishingIffInfinite := by
  intro W hΔ data
  exact fun hMW => ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.vanishes_at_one_iff_infinite_points hbsd hΔ data hMW

/-- The Clay PDF “in particular” consequence implies its nonvanishing/finite-points form. -/
theorem ClayBirchSwinnertonDyer.Consequences.PointCriteria.VanishingIffInfinite.nonvanishing_iff_finite_points
    (h : ClayBirchSwinnertonDyer.Consequences.PointCriteria.VanishingIffInfinite) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.NonvanishingIffFinite := by
  intro W hΔ data hMW
  exact Iff.ne_zero_iff_finite (h W hΔ data hMW)

/-- The universal Birch--Swinnerton-Dyer rank statement implies the nonvanishing/finite-points consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.nonvanishing_iff_finite_points
    (hbsd : ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.NonvanishingIffFinite :=
  hbsd.vanishes_iff_infinite_points.nonvanishing_iff_finite_points

/-- Taylor-expansion Birch--Swinnerton-Dyer yields the PDF's “in particular” consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.vanishes_iff_infinite_points
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.Integral) :
  ClayBirchSwinnertonDyer.Consequences.PointCriteria.VanishingIffInfinite :=
  ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries.vanishes_iff_infinite_points
    (ClayBirchSwinnertonDyer.Formulations.Rank.Existence.conjecture h.rank_existence)

/-- Taylor-expansion Birch--Swinnerton-Dyer yields the nonvanishing/finite-points consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.Integral.nonvanishing_iff_finite_points
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.Integral) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.NonvanishingIffFinite :=
  h.vanishes_iff_infinite_points.nonvanishing_iff_finite_points

/-- Short-integral-model Birch--Swinnerton-Dyer yields the short-model “in particular” consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral.vanishes_iff_infinite_points
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralVanishingIffInfinite := by
  intro C data
  exact fun hMW => by
    rcases h C with ⟨data₀, h₀⟩
    have hdata :
        BirchSwinnertonDyerRankEqualityForModel C.weierstrass_curve
          C.nonsingular_weierstrass_curve data :=
      BirchSwinnertonDyerRankEqualityForModel.transfer_continuation (data := data) h₀
    exact BirchSwinnertonDyerRankEqualityForModel.vanishes_at_one_iff_infinite_points hdata hMW

/-- The short-model “in particular” consequence implies its nonvanishing/finite-points form. -/
theorem ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralVanishingIffInfinite.nonvanishing_iff_finite_points
    (h : ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralVanishingIffInfinite) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralNonvanishingIffFinite := by
  intro C data hMW
  exact Iff.ne_zero_iff_finite (h C data hMW)

/-- The short-model rank statement implies the short-model nonvanishing/finite-points consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral.nonvanishing_iff_finite_points
    (h : ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralNonvanishingIffFinite :=
  h.vanishes_iff_infinite_points.nonvanishing_iff_finite_points

/-- Short-model Taylor Birch--Swinnerton-Dyer yields the short-model “in particular” consequence. -/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral.vanishes_iff_infinite_points
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralVanishingIffInfinite :=
  ClayBirchSwinnertonDyer.Formulations.Rank.ShortIntegral.vanishes_iff_infinite_points h.rank_existence

/--
The exact short-model Taylor statement implies the short-model nonvanishing/finite-points
consequence.
-/
theorem ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral.nonvanishing_iff_finite_points
    (h : ClayBirchSwinnertonDyer.Formulations.Taylor.ShortIntegral) :
    ClayBirchSwinnertonDyer.Consequences.PointCriteria.ShortIntegralNonvanishingIffFinite :=
  h.vanishes_iff_infinite_points.nonvanishing_iff_finite_points

/-!
## Main theorem

This final declaration records the Birch--Swinnerton-Dyer target directly. Replace the placeholder
proof when one is available.
-/

/-- Clay Millennium Prize target for Birch--Swinnerton-Dyer. -/
theorem clay_prize_birch_swinnerton_dyer :
    ClayBirchSwinnertonDyer := by
  sorry

end MillenniumBirchSwinnertonDyer
