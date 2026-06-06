import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Problems.BirchSwinnertonDyer.BSD_specific

open Polynomial
open scoped BigOperators
open scoped Classical
open scoped Topology

namespace WeierstrassCurve

/--
The incomplete Euler product `L(C,s)` from the Clay PDF (equation on page 2):

`L(C,s) = ∏_{p ∤ 2Δ} (1 - aₚ p^{-s} + p^{1-2s})^{-1}`.

We implement “omit primes `p | 2Δ`” by inserting a factor `1` at those primes.

Note: we do **not** prove convergence of this infinite product.
-/
noncomputable def incompleteLSeries (W : WeierstrassCurve ℤ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes,
    if ((p : ℕ) : ℤ) ∣ (2 * W.Δ) then
      (1 : ℂ)
    else
      (aeval (p ^ (-s) : ℂ) (W.baseChange (ZMod (p : ℕ))).localEulerFactor)⁻¹

/--
Auxiliary map used to show `WeierstrassCurve.Affine.Point` is finite over a finite ring: forget a
point's proof data and remember only its affine coordinates (or `none` for the point at infinity).
-/
noncomputable def pointToOption {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    W.toAffine.Point → Option (R × R)
  | 0 => none
  | Affine.Point.some (x := x) (y := y) _ => some (x, y)

/--
`pointToOption` is injective: an affine point is determined by whether it is the point at infinity
and, otherwise, by its `(x,y)`-coordinates.
-/
theorem pointToOption_injective {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    Function.Injective (pointToOption W) := by
  intro P Q h
  cases P <;> cases Q <;> cases h <;> rfl

/--
Over a finite ring, the type of affine points of a Weierstrass curve is finite.

This is an elementary finiteness lemma used to define `Nₚ`/`aₚ` in the Clay Euler product.
-/
theorem finite_toAffine_Point {R : Type} [CommRing R] [Finite R] (W : WeierstrassCurve R) :
    Finite W.toAffine.Point := by
  classical
  exact Finite.of_injective (pointToOption W) (pointToOption_injective W)

/--
The Clay quantity `Nₚ` (Clay PDF, p.2): the number of affine solutions modulo `p`
(i.e. the number of points excluding the point at infinity).
-/
noncomputable def Np (W : WeierstrassCurve ℤ) (p : Nat.Primes) : ℕ :=
  (W.baseChange (ZMod (p : ℕ))).numPoints - 1

/-- The Clay coefficient `aₚ := p - Nₚ` (Clay PDF, p.2). -/
noncomputable def ap (W : WeierstrassCurve ℤ) (p : Nat.Primes) : ℤ :=
  (p : ℤ) - (Np W p : ℤ)

private lemma one_le_numPoints_zmod (W : WeierstrassCurve ℤ) (p : Nat.Primes) :
    1 ≤ (W.baseChange (ZMod (p : ℕ))).numPoints := by
  classical
  have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
  letI : NeZero (p : ℕ) := ⟨hp0⟩
  haveI : Finite ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) :=
    finite_toAffine_Point (W := W.baseChange (ZMod (p : ℕ)))
  letI : Fintype ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) := Fintype.ofFinite _
  have hcard :
      (W.baseChange (ZMod (p : ℕ))).numPoints =
        Fintype.card ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) := by
    simp [WeierstrassCurve.numPoints]
  have hpos :
      0 < Fintype.card ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) :=
    Fintype.card_pos_iff.mpr ⟨(0 : (W.baseChange (ZMod (p : ℕ))).toAffine.Point)⟩
  have hge :
      1 ≤ Fintype.card ((W.baseChange (ZMod (p : ℕ))).toAffine.Point) :=
    Nat.succ_le_iff.mp hpos
  simpa [hcard] using hge
 
/--
Relate the Clay coefficient `aₚ` to Mathlib’s `frobeniusTrace` for the reduction modulo `p`.

This identifies the `aₚ` appearing in the Clay Euler factor with the standard trace-of-Frobenius
quantity used in the definition of the local Euler polynomial.
-/
theorem ap_eq_frobeniusTrace (W : WeierstrassCurve ℤ) (p : Nat.Primes) :
    ap W p = (W.baseChange (ZMod (p : ℕ))).frobeniusTrace := by
  classical
  have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
  letI : NeZero (p : ℕ) := ⟨hp0⟩
  have hpoints : 1 ≤ (W.baseChange (ZMod (p : ℕ))).numPoints := one_le_numPoints_zmod W p
  have hNp : (Np W p : ℤ) = (W.baseChange (ZMod (p : ℕ))).numPoints - 1 := by
    simp [WeierstrassCurve.Np, Int.ofNat_sub hpoints]
  simp [WeierstrassCurve.ap, WeierstrassCurve.frobeniusTrace, WeierstrassCurve.numPoints, hNp,
    ZMod.card]
  ring

/--
For primes `p ∤ 2Δ`, the Euler factor appearing in `incompleteLSeries` agrees with the explicit
Clay expression `1 - aₚ p^{-s} + p^{1-2s}` (Clay PDF, p.2).
-/
theorem localEulerFactor_aeval_eq_clay
    (W : WeierstrassCurve ℤ) (p : Nat.Primes) (s : ℂ) (hp : ¬ ((p : ℕ) : ℤ) ∣ (2 * W.Δ)) :
    aeval (p ^ (-s) : ℂ) ((W.baseChange (ZMod (p : ℕ))).localEulerFactor) =
      (1 : ℂ) - (ap W p : ℂ) * (p ^ (-s) : ℂ) + (p : ℂ) ^ (1 - 2 * s) := by
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
      (W.baseChange (ZMod (p : ℕ))).frobeniusTrace = ap W p :=
    (ap_eq_frobeniusTrace W p).symm
  have hEval :
      aeval (p ^ (-s) : ℂ) ((W.baseChange (ZMod (p : ℕ))).localEulerFactor) =
        (1 : ℂ) - (ap W p : ℂ) * (p ^ (-s) : ℂ) + (p : ℂ) * (p ^ (-s) : ℂ) ^ 2 := by
    simp [WeierstrassCurve.localEulerFactor, hEll, hap, aeval_X, mul_comm, ZMod.card]
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

end WeierstrassCurve

namespace MillenniumBirchSwinnertonDyer

open Complex

/-!
# Birch and Swinnerton–Dyer Conjecture

This file states the Clay Millennium problem “Birch and Swinnerton–Dyer conjecture” in Lean,
following the official Clay problem description:
`Problems/BirchSwinnertonDyer/references/clay/birchswin.pdf`.

## Clay statement (rank part)

For an elliptic curve `C/ℚ` given by an integral Weierstrass model, the Clay PDF defines an
**incomplete** Euler product

`L(C, s) := ∏_{p ∤ 2Δ} (1 - aₚ p^{-s} + p^{1-2s})^{-1}`

and states the Millennium conjecture as:

*The order of vanishing of `L(C, s)` at `s = 1` equals `rank(C(ℚ))`.*

In Lean we express “order of vanishing at `s = 1`” using `analyticOrderAt`.

## About this formalization

Mathlib does not currently provide the analytic continuation of Hasse–Weil `L`-functions of
elliptic curves, so we parameterize the statement by a data package `ClayLSeriesData` containing:

* a function `L : ℂ → ℂ`,
* a proof that it is analytic (entire),
* and a proof that it agrees with the incomplete Euler product on the half-plane `Re(s) > 3/2`
  (the Clay PDF states this Euler product converges there).

The conjecture then only asserts the equality of vanishing order and rank.

## Not yet formalized from the Clay PDF

The Clay write-up contains additional content that is not (currently) formalized here, including:

* convergence of the Euler product and construction of the analytic continuation;
* the decomposition `C(ℚ) ≃ ℤ^r ⊕ C(ℚ)_tors` (Mordell–Weil theorem) as a theorem in Mathlib;
* proving finiteness of the Tate–Shafarevich group, and giving the arithmetic definitions of the
  regulator/period/Tamagawa factors used in the refined conjecture (Clay PDF, “Remarks 1”).
-/

/--
Data describing the analytic continuation of the Clay Euler product attached to a fixed integral
Weierstrass model `W`.

This is data (not an axiom): supplying it amounts to giving a specific `L`-function together with
its expected analytic properties.
-/
structure ClayLSeriesData (W : WeierstrassCurve ℤ) where
  /-- The analytic continuation of the (incomplete) L-series. -/
  L : ℂ → ℂ
  /-- The continuation is analytic on all of `ℂ` (Clay PDF references modularity results). -/
  analytic : ∀ s : ℂ, AnalyticAt ℂ L s
  /-- Agreement with the Euler product in its region of convergence (Clay PDF: `Re(s) > 3/2`). -/
  agrees : ∀ s : ℂ, s.re > (3 / 2 : ℝ) → L s = W.incompleteLSeries s

/--
Uniqueness of the analytic continuation: if two candidate continuations are entire and agree with
the Euler product on the half-plane `Re(s) > 3/2`, then the resulting functions are equal.
-/
theorem ClayLSeriesData.L_unique {W : WeierstrassCurve ℤ} (d₁ d₂ : ClayLSeriesData W) :
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

/--
Data for a *completed* L-function `L*` (Clay PDF, “Remarks 1”).

We do not construct the completion factor (Gamma/period factors); instead we record the standard
local relation near `s = 1`:

`L*(s) = completionFactor(s) * L(s)`,

with `completionFactor` analytic and nonvanishing at `s = 1`.
-/
structure ClayCompletedLSeriesData (W : WeierstrassCurve ℤ) extends ClayLSeriesData W where
  /-- The completed L-function `L*`. -/
  Lstar : ℂ → ℂ
  /-- The completion is analytic on all of `ℂ`. -/
  analytic_star : ∀ s : ℂ, AnalyticAt ℂ Lstar s
  /-- The analytic completion factor relating `L*` to `L` near `s = 1`. -/
  completionFactor : ℂ → ℂ
  /-- The completion factor is analytic at `s = 1`. -/
  completionFactor_analytic : AnalyticAt ℂ completionFactor 1
  /-- The completion factor is nonzero at `s = 1`. -/
  completionFactor_ne_zero : completionFactor 1 ≠ 0
  /-- Local relation `L*(s) = completionFactor(s) * L(s)` near `s = 1`. -/
  Lstar_eq : ∀ᶠ z in 𝓝 (1 : ℂ), Lstar z = completionFactor z * L z

/--
Since the completion factor is analytic and nonvanishing at `s = 1`, the completed L-function `L*`
has the same order of vanishing at `s = 1` as `L`.
-/
theorem ClayCompletedLSeriesData.analyticOrderAt_Lstar_eq {W : WeierstrassCurve ℤ}
    (data : ClayCompletedLSeriesData W) :
    analyticOrderAt data.Lstar 1 = analyticOrderAt data.L 1 := by
  have hcong :
      analyticOrderAt data.Lstar (1 : ℂ) =
        analyticOrderAt (data.completionFactor * data.L) (1 : ℂ) := by
    simpa using (analyticOrderAt_congr (z₀ := (1 : ℂ)) data.Lstar_eq)
  have hmul :
      analyticOrderAt (data.completionFactor * data.L) (1 : ℂ) =
        analyticOrderAt data.completionFactor (1 : ℂ) + analyticOrderAt data.L (1 : ℂ) := by
    simpa using
      analyticOrderAt_mul (z₀ := (1 : ℂ)) (f := data.completionFactor) (g := data.L)
        data.completionFactor_analytic (data.analytic 1)
  have hfac : analyticOrderAt data.completionFactor (1 : ℂ) = 0 :=
    (data.completionFactor_analytic.analyticOrderAt_eq_zero).2 data.completionFactor_ne_zero
  calc
    analyticOrderAt data.Lstar 1
        = analyticOrderAt (data.completionFactor * data.L) 1 := hcong
    _ = analyticOrderAt data.completionFactor 1 + analyticOrderAt data.L 1 := hmul
    _ = analyticOrderAt data.L 1 := by simp [hfac]

/--
The Clay Millennium statement (rank part): for any non-singular integral Weierstrass model,
the order of vanishing of `L(C,s)` at `s = 1` equals the Mordell–Weil rank of `C(ℚ)`.
-/
def BirchSwinnertonDyerConjecture : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 →
    ∀ data : ClayLSeriesData W,
      analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ)

/-!
## Refined conjecture (Clay PDF, “Remarks 1”)

The Clay PDF also records a refined leading-coefficient formula for a *completed* L-series `L*`.
We include that formula as a separate conjecture, parameterized by a package of invariants.

This is still “data-only”: we do not construct the Tate–Shafarevich group, regulator, Tamagawa
factors, or the completed L-series in Mathlib here.
-/

/-- The order of the torsion subgroup `C(ℚ)_tors`, as a natural number (`0` if infinite). -/
noncomputable def torsionOrder (W : WeierstrassCurve ℤ) : ℕ :=
  Nat.card ↥(AddCommGroup.torsion ((W.baseChange ℚ).toProjective.Point))

/--
The arithmetic invariants appearing in the refined BSD formula (Clay PDF, “Remarks 1”).

Notation correspondence (PDF → Lean fields):
- `|X_C|` → `Sha_order`
- `R_∞` → `regulator`
- `w_∞` → `period`
- `w_p` → `tamagawaFactor p`
- `∏_{p | 2Δ} w_p` → `tamagawaProduct`
- `c*` → `leadingCoefficient`
-/
structure RefinedInvariants (W : WeierstrassCurve ℤ) where
  Sha_order : ℕ
  regulator : ℝ
  period : ℝ
  /-- The Tamagawa number `wₚ` at a prime `p`. -/
  tamagawaFactor : Nat.Primes → ℝ
  /-- A finite list of the “bad” primes: those dividing `2Δ`. -/
  badPrimes : Finset Nat.Primes
  /-- Specification: `badPrimes` is exactly the primes dividing `2Δ`. -/
  badPrimes_spec : ∀ p : Nat.Primes, p ∈ badPrimes ↔ ((p : ℕ) : ℤ) ∣ (2 * W.Δ)
  leadingCoefficient : ℝ

/-- The finite Tamagawa product `∏_{p | 2Δ} wₚ` (Clay PDF, “Remarks 1”). -/
noncomputable def RefinedInvariants.tamagawaProduct {W : WeierstrassCurve ℤ}
    (inv : RefinedInvariants W) : ℝ :=
  ∏ p ∈ inv.badPrimes, inv.tamagawaFactor p

/--
Refined Birch–Swinnerton–Dyer conjecture: the rank part together with the predicted leading
coefficient for the completed L-series.

We express the leading coefficient identity in the same algebraic shape as the PDF:
`c* = |X_C| R_∞ w_∞ ∏ w_p / |C(ℚ)_tors|^2`.
-/
def RefinedBirchSwinnertonDyerConjecture : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 →
    ∀ data : ClayCompletedLSeriesData W,
      analyticOrderAt data.Lstar 1 = WeierstrassCurve.rank (W.baseChange ℚ) ∧
        ∀ inv : RefinedInvariants W,
          inv.leadingCoefficient =
            ((inv.Sha_order : ℝ) * inv.regulator * inv.period * inv.tamagawaProduct) /
              ((torsionOrder W : ℝ) ^ 2)

/-!
## Easy analytic consequences (proved)

These are unconditional *lemmas* about `analyticOrderAt`, recording the “in particular …” part of
the Clay write-up at the level of vanishing order vs. rank.

We also prove the final step “rank ≠ 0 ↔ C(ℚ) infinite” *under the standard Mordell–Weil finite
generation hypothesis* (`WeierstrassCurve.MordellWeil`). The full Mordell–Weil theorem is not
currently available as a theorem in Mathlib.
-/

theorem L_one_eq_zero_iff_rank_ne_zero
    (hbsd : BirchSwinnertonDyerConjecture) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : ClayLSeriesData W) :
    data.L 1 = 0 ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 := by
  have hAnalytic : AnalyticAt ℂ data.L 1 := data.analytic 1
  have hOrder : analyticOrderAt data.L 1 = WeierstrassCurve.rank (W.baseChange ℚ) :=
    hbsd W hΔ data
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

/--
If the rank is finite (i.e. not `⊤` in `ℕ∞`), then the order statement can be unpacked into the
explicit “Taylor expansion” form used in the Clay PDF:
`L(s) = (s - 1)^n • g(s)` near `s = 1` with `g(1) ≠ 0`.

This is a general lemma about `analyticOrderAt`, specialized to the BSD context.
-/
theorem exists_taylor_form_of_finite_rank
    (hbsd : BirchSwinnertonDyerConjecture) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
    (data : ClayLSeriesData W) (hfin : WeierstrassCurve.rank (W.baseChange ℚ) ≠ (⊤ : ℕ∞)) :
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

theorem rank_eq_zero_iff_finite_points {W : WeierstrassCurve ℤ}
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
      exact (AddCommGroup.mem_torsion G g).1 hgT
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

/--
Under finite generation of the Mordell–Weil group, “rank ≠ 0” is equivalent to “infinitely many
rational points”.
-/
theorem infinite_points_iff_rank_ne_zero {W : WeierstrassCurve ℤ}
    (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
    Infinite ((W.baseChange ℚ).toProjective.Point) ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 := by
  have hFin :
      WeierstrassCurve.rank (W.baseChange ℚ) = 0 ↔ Finite ((W.baseChange ℚ).toProjective.Point) :=
    rank_eq_zero_iff_finite_points (W := W) hMW
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
“`L(1) = 0` iff `C(ℚ)` is infinite”, as stated in the Clay write-up, under the assumptions
`BirchSwinnertonDyerConjecture` and Mordell–Weil finite generation.
-/
theorem L_one_eq_zero_iff_infinite_points
     (hbsd : BirchSwinnertonDyerConjecture) {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0)
     (data : ClayLSeriesData W) (hMW : WeierstrassCurve.MordellWeil (W.baseChange ℚ)) :
     data.L 1 = 0 ↔ Infinite ((W.baseChange ℚ).toProjective.Point) := by
  have hRank : data.L 1 = 0 ↔ WeierstrassCurve.rank (W.baseChange ℚ) ≠ 0 :=
    L_one_eq_zero_iff_rank_ne_zero hbsd hΔ data
  exact hRank.trans (infinite_points_iff_rank_ne_zero (W := W) hMW).symm

end MillenniumBirchSwinnertonDyer
