import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

namespace Millennium

open Complex
open Filter
open scoped BigOperators
open scoped Topology

/-!
# The Riemann Hypothesis

This file states the Clay Millennium problem “Riemann Hypothesis” in Lean, following the
Clay problem description:
`Problems/RiemannHypothesis/references/clay/riemann.pdf`.

We reuse Mathlib's analytic continuation of the Riemann zeta function `riemannZeta : ℂ → ℂ` and
state a few standard facts mentioned in the Clay write-up (Dirichlet series and Euler product for
`re s > 1`, the functional equation for the completed zeta function, and the definition of
Riemann's `ξ`-function).

`ClayRiemannHypothesis` below states the Clay critical-line formulation.  It is equivalent to the
real-part statement `ClayRiemannHypothesis.Formulations.RealPart`, to Mathlib's
`_root_.RiemannHypothesis`, and to Riemann's original `ξ(t)` wording
`ClayRiemannHypothesis.Formulations.XiZeros`; the zero correspondence between `ξ(t)` and the
nontrivial zeros of `ζ(s)` needed for the last equivalence is proved in
`ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds`.
-/

/-!
## Zeta: series, Euler product, pole at `s = 1`
-/

/-- The Dirichlet series definition of `ζ(s)` is valid for `re s > 1` (Clay PDF, Section I). -/
theorem riemannZeta.eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa using zeta_eq_tsum_one_div_nat_cpow hs

/-- The Euler product `ζ(s) = ∏_p (1 - p^{-s})^{-1}` holds for `re s > 1` (Clay PDF, Section II). -/
theorem riemannZeta.euler_product_has_prod {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  _root_.riemannZeta_eulerProduct_hasProd hs

/--
Nonvanishing consequence of the Euler-product half-plane:
`ζ(s)` has no zeros for `Re(s) > 1`.
-/
theorem riemannZeta.ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 :=
  _root_.riemannZeta_ne_zero_of_one_lt_re hs

/--
The zeta function is differentiable away from `s = 1` (meromorphic continuation).

This is a Mathlib theorem (`differentiableAt_riemannZeta`) referenced by the Clay PDF (Section I).
-/
theorem riemannZeta.differentiable_at {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-- The residue of `ζ(s)` at `s = 1` is `1` (Clay PDF, Section I). -/
theorem riemannZeta.residue_one :
    Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

/-!
## Completed zeta and the functional equation
-/

/-- The completed zeta function `Λ(s)` from Mathlib (Clay PDF, equation (1)). -/
noncomputable def completed_zeta (s : ℂ) : ℂ :=
  completedRiemannZeta s

/--
The entire part `Λ₀(s)` of Mathlib's completed zeta function.

Mathlib represents the meromorphic completed zeta function as a total function, so products such
as `s * (s - 1) * completedRiemannZeta s` have pole-artifact values at `s = 0` and `s = 1`.
The Riemann `ξ` function below therefore uses the pole-cancelled entire expression built from
`completedRiemannZeta₀`.
-/
noncomputable def completed_zeta_entire (s : ℂ) : ℂ :=
  completedRiemannZeta₀ s

/-- Functional equation in the symmetric form `Λ(1 - s) = Λ(s)` (Clay PDF, equation (1)). -/
theorem completed_zeta.one_sub (s : ℂ) : completed_zeta (1 - s) = completed_zeta s := by
  simpa [completed_zeta] using completedRiemannZeta_one_sub s

/-- Functional equation for the entire completed-zeta part. -/
theorem completed_zeta_entire.one_sub (s : ℂ) :
    completed_zeta_entire (1 - s) = completed_zeta_entire s := by
  simpa [completed_zeta_entire] using completedRiemannZeta₀_one_sub s

/-!
## Riemann's `ξ(t)` function (Clay PDF, Section I)
-/

/-- The zeta-plane argument corresponding to Riemann's variable `t`: `s = 1/2 + i t`. -/
noncomputable def xi_argument (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * t

/-- The `t`-parameter corresponding to a zeta-plane point `s`, inverse to `xi_argument`. -/
noncomputable def zeta_zero_parameter (s : ℂ) : ℂ :=
  -Complex.I * (s - (1 / 2 : ℂ))

/-- The `s = 1/2 + i t` substitution inverts `zeta_zero_parameter` on `s`. -/
theorem xi_argument.comp_zeta_zero_parameter (s : ℂ) :
    xi_argument (zeta_zero_parameter s) = s := by
  simp [xi_argument, zeta_zero_parameter]
  rw [← mul_assoc, Complex.I_mul_I]
  ring_nf

/-- The `zeta_zero_parameter` coordinate inverts `xi_argument` on Riemann's parameter `t`. -/
theorem zeta_zero_parameter.comp_xi_argument (t : ℂ) :
    zeta_zero_parameter (xi_argument t) = t := by
  simp [xi_argument, zeta_zero_parameter]
  rw [← mul_assoc, Complex.I_mul_I]
  ring_nf

/-- The gamma factor `π^{-s/2} Γ(s/2)` in Bombieri's Clay formula for `ξ(t)`. -/
noncomputable def xi_gamma_factor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2)

/-- This gamma factor is Mathlib's archimedean factor `Gammaℝ`. -/
theorem xi_gamma_factor.eq_gamma_real (s : ℂ) : xi_gamma_factor s = Gammaℝ s :=
  by simp [xi_gamma_factor, Gammaℝ_def]

/--
Riemann's `ξ`-function, as a function of the complex variable `t`, using the substitution
`s = 1/2 + i t` from the Clay PDF.

The formula is the entire pole-cancelled form of
`1 / 2 * s * (s - 1) * completed_zeta s`.  Using `completed_zeta` directly would introduce
spurious Lean point-values at the poles `s = 0` and `s = 1`.
-/
noncomputable def xi (t : ℂ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * t
  (1 / 2 : ℂ) * (s * (s - 1) * completed_zeta_entire s + 1)

/--
Bombieri's Clay PDF formula
`ξ(t) = 1/2 * s * (s - 1) * π^{-s/2} * Γ(s/2) * ζ(s)`, with `s = 1/2 + i t`.

The global definition `xi` above uses the pole-cancelled entire completed-zeta expression; this
definition records the expanded meromorphic PDF expression.

**Warning: do not state the Riemann Hypothesis with this function.**  Mathlib's `riemannZeta` and
`Gammaℝ` are total functions.  At the trivial zeros `s = -2, -4, …` the factor `Γ(s/2)` has a pole
in mathematics but the junk value `0` in Lean, and `ζ(s) = 0` there as well, so
`expanded_xi_formula` has spurious zeros at the non-real points `t = -i (s - 1/2)` for `s` a
negative even integer, where `xi` is nonzero.  The two functions agree exactly away from
`s ∈ {0, 1}` and the trivial zeros (`expanded_xi_formula.eq_xi_of_ne`).
-/
noncomputable def expanded_xi_formula (t : ℂ) : ℂ :=
  let s : ℂ := xi_argument t
  (1 / 2 : ℂ) * s * (s - 1) * (xi_gamma_factor s * riemannZeta s)

/-- `xi` written using the coordinate `xi_argument`. -/
theorem xi.eq_xi_argument (t : ℂ) :
    xi t =
      (1 / 2 : ℂ) *
        (xi_argument t * (xi_argument t - 1) * completed_zeta_entire (xi_argument t) + 1) := by
  simp [xi, xi_argument]

/--
In the half-plane `re s > 0` and away from `s = 1`, Bombieri's expanded PDF formula agrees with the
pole-cancelled entire definition used by `xi`.

The hypothesis `0 < re s` excludes the whole left half-plane, in particular the trivial zeros,
where the two functions differ (see the warning on `expanded_xi_formula`).  The sharp version is
`expanded_xi_formula.eq_xi_of_ne`.
-/
theorem expanded_xi_formula.eq_xi {t : ℂ}
    (ht : 0 < (xi_argument t).re) (hone : xi_argument t ≠ 1) :
    expanded_xi_formula t = xi t := by
  let s : ℂ := xi_argument t
  have hzero : s ≠ 0 := by
    intro hs0
    have hpos : 0 < s.re := ht
    rw [hs0] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hGamma : Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (s := s) (by simp [s]; exact ht)
  have hcompleted : xi_gamma_factor s * riemannZeta s = completed_zeta s := by
    calc
      xi_gamma_factor s * riemannZeta s = Gammaℝ s * riemannZeta s := by
        rw [xi_gamma_factor.eq_gamma_real]
      _ = Gammaℝ s * (completedRiemannZeta s / Gammaℝ s) := by
        rw [riemannZeta_def_of_ne_zero hzero]
      _ = completedRiemannZeta s := by
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ _ hGamma
      _ = completed_zeta s := rfl
  have hcancel :
      (1 / 2 : ℂ) * s * (s - 1) * completed_zeta s =
        (1 / 2 : ℂ) * (s * (s - 1) * completed_zeta_entire s + 1) := by
    have hOneSub : 1 - s ≠ 0 := sub_ne_zero.mpr hone.symm
    change (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s =
        (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)
    rw [completedRiemannZeta_eq]
    field_simp [hzero, hOneSub]
    ring
  calc
    expanded_xi_formula t = (1 / 2 : ℂ) * s * (s - 1) * completed_zeta s := by
      simp [expanded_xi_formula, s, hcompleted]
    _ = (1 / 2 : ℂ) * (s * (s - 1) * completed_zeta_entire s + 1) := hcancel
    _ = xi t := by
      simpa [s] using (xi.eq_xi_argument t).symm

/-- The function `xi` is even: `ξ(-t) = ξ(t)`, from the functional equation `Λ(1-s)=Λ(s)`. -/
theorem xi.even (t : ℂ) : xi (-t) = xi t := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * t
  have hs_neg : (1 / 2 : ℂ) + Complex.I * (-t) = 1 - s := by
    -- `s(-t) = 1 - s(t)`
    simp [s]
    ring
  -- A simp-normal form of `hs_neg` matching the expansions produced by `simp`.
  have hs_neg' : (1 / 2 : ℂ) + -(Complex.I * t) = 1 - s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hs_neg
  have hs_neg'' : (2⁻¹ : ℂ) + -(Complex.I * t) = 1 - s := by
    simpa using hs_neg'
  -- `s(-t) = 1 - s(t)` and `Λ₀(1 - s) = Λ₀(s)` imply evenness.
  calc
    xi (-t)
        = (1 / 2 : ℂ) *
            ((1 - s) * ((1 - s) - 1) * completed_zeta_entire (1 - s) + 1) := by
            -- Expand the `let`-binding in `xi` and rewrite the substituted value using `hs_neg`.
            dsimp [xi]
            simp [hs_neg'']
    _   = (1 / 2 : ℂ) *
            ((1 - s) * ((1 - s) - 1) * completed_zeta_entire s + 1) := by
            simp [completed_zeta_entire.one_sub]
    _   = (1 / 2 : ℂ) * (s * (s - 1) * completed_zeta_entire s + 1) := by
            -- The polynomial factor is invariant under `s ↦ 1 - s`.
            ring
    _   = xi t := by
            simp [xi, s, completed_zeta_entire]

/-!
## Zeros and the Clay statement
-/

/-- Trivial zeros: the negative even integers `-2, -4, -6, ...`. -/
def IsTrivialZero (s : ℂ) : Prop :=
  ∃ n : ℕ, s = -2 * (n + 1)

/-- A “nontrivial” zero is a zero that is not a trivial zero and not the pole at `s = 1`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬IsTrivialZero s ∧ s ≠ 1

/-- `Gammaℝ s` vanishes (in Lean) exactly at `s = 0` and at the trivial zeros. -/
theorem gammaReal_ne_zero_of_ne {s : ℂ} (h0 : s ≠ 0) (htriv : ¬ IsTrivialZero s) :
    Gammaℝ s ≠ 0 := by
  intro hG
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
  rcases n with _ | m
  · exact h0 (by simpa using hn)
  · exact htriv ⟨m, by rw [hn]; push_cast; ring⟩

/--
Sharp form of `expanded_xi_formula.eq_xi`: Bombieri's expanded PDF formula agrees with `xi`
exactly when `s = 1/2 + i t` is neither a pole location (`s ≠ 0`, `s ≠ 1`) nor a trivial zero
(where the Lean junk value `Gammaℝ s = 0` makes the expanded formula vanish spuriously).
-/
theorem expanded_xi_formula.eq_xi_of_ne {t : ℂ}
    (h0 : xi_argument t ≠ 0) (h1 : xi_argument t ≠ 1)
    (htriv : ¬ IsTrivialZero (xi_argument t)) :
    expanded_xi_formula t = xi t := by
  let s : ℂ := xi_argument t
  have hzero : s ≠ 0 := h0
  have hGamma : Gammaℝ s ≠ 0 := gammaReal_ne_zero_of_ne h0 htriv
  have hcompleted : xi_gamma_factor s * riemannZeta s = completed_zeta s := by
    calc
      xi_gamma_factor s * riemannZeta s = Gammaℝ s * riemannZeta s := by
        rw [xi_gamma_factor.eq_gamma_real]
      _ = Gammaℝ s * (completedRiemannZeta s / Gammaℝ s) := by
        rw [riemannZeta_def_of_ne_zero hzero]
      _ = completedRiemannZeta s := by
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ _ hGamma
      _ = completed_zeta s := rfl
  have hcancel :
      (1 / 2 : ℂ) * s * (s - 1) * completed_zeta s =
        (1 / 2 : ℂ) * (s * (s - 1) * completed_zeta_entire s + 1) := by
    have hOneSub : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
    change (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s =
        (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)
    rw [completedRiemannZeta_eq]
    field_simp [hzero, hOneSub]
    ring
  calc
    expanded_xi_formula t = (1 / 2 : ℂ) * s * (s - 1) * completed_zeta s := by
      simp [expanded_xi_formula, s, hcompleted]
    _ = (1 / 2 : ℂ) * (s * (s - 1) * completed_zeta_entire s + 1) := hcancel
    _ = xi t := by
      simpa [s] using (xi.eq_xi_argument t).symm

/-- A nontrivial zero cannot lie in the Euler-product half-plane `Re(s) > 1`. -/
theorem IsNontrivialZero.re_le_one {s : ℂ} (hs : IsNontrivialZero s) : s.re ≤ 1 := by
  by_contra hle
  exact (riemannZeta.ne_zero_of_one_lt_re (lt_of_not_ge hle)) hs.1

/-- The critical strip `{ s | 0 < re s ∧ re s < 1 }` (Clay PDF, Section I). -/
def CriticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The critical line `{ s | re s = 1/2 }` (Clay PDF, Section I). -/
def CriticalLine : Set ℂ :=
  {s : ℂ | s.re = 1 / 2}

/-- The critical line lies in the critical strip. -/
theorem CriticalLine.mem_critical_strip {s : ℂ} (hs : s ∈ CriticalLine) : s ∈ CriticalStrip := by
  constructor
  · rw [CriticalLine] at hs
    rw [hs]
    norm_num
  · rw [CriticalLine] at hs
    rw [hs]
    norm_num

/-- A complex number is real, in the sense used for Riemann's complex `t` variable. -/
def IsRealComplex (t : ℂ) : Prop :=
  t.im = 0

/-- Under `s = 1/2 + i t`, the real part of `s` is `1/2 - im(t)`. -/
theorem xi_argument.re (t : ℂ) : (xi_argument t).re = 1 / 2 - t.im := by
  simp [xi_argument, sub_eq_add_neg]

/-- The Clay condition that `t` is real is exactly the critical-line condition for `1/2 + i t`. -/
theorem xi_argument.mem_critical_line_iff_real (t : ℂ) :
    xi_argument t ∈ CriticalLine ↔ IsRealComplex t := by
  simp [CriticalLine, IsRealComplex, xi_argument, sub_eq_add_neg]

/--
For a zeta-plane point `s`, the corresponding Riemann parameter `t` is real exactly when `s` lies
on the critical line.
-/
theorem zeta_zero_parameter.is_real_iff_mem_critical_line (s : ℂ) :
    IsRealComplex (zeta_zero_parameter s) ↔ s ∈ CriticalLine := by
  constructor
  · intro ht
    have hLine : xi_argument (zeta_zero_parameter s) ∈ CriticalLine :=
      (xi_argument.mem_critical_line_iff_real (zeta_zero_parameter s)).2 ht
    simpa [xi_argument.comp_zeta_zero_parameter s] using hLine
  · intro hs
    have hLine : xi_argument (zeta_zero_parameter s) ∈ CriticalLine := by
      simpa [xi_argument.comp_zeta_zero_parameter s] using hs
    exact (xi_argument.mem_critical_line_iff_real (zeta_zero_parameter s)).1 hLine

/--
The Clay statement: all nontrivial zeros of `ζ(s)` have real part `1/2`.

This is equivalent to Mathlib's `_root_.RiemannHypothesis`.
-/
def ClayRiemannHypothesis.Formulations.RealPart : Prop :=
  ∀ (s : ℂ), IsNontrivialZero s → s.re = 1 / 2

/--
Clay's critical-line wording of the Riemann Hypothesis:
every nontrivial zero of `ζ(s)` lies on the critical line `re s = 1/2`.
-/
def ClayRiemannHypothesis : Prop :=
  ∀ (s : ℂ), IsNontrivialZero s → s ∈ CriticalLine

/--
Clay's original `ξ`-function wording of the Riemann Hypothesis:
all zeros of `ξ(t)` are real.
-/
def ClayRiemannHypothesis.Formulations.XiZeros : Prop :=
  ∀ (t : ℂ), xi t = 0 → IsRealComplex t

/-- The `ξ`-wording says directly that every zero of `ξ(t)` has real `t`. -/
theorem ClayRiemannHypothesis.Formulations.XiZeros.zero_real
    (h : ClayRiemannHypothesis.Formulations.XiZeros) {t : ℂ} (ht : xi t = 0) :
    IsRealComplex t :=
  h t ht

/--
The `ξ`-wording sends every zero of `ξ(t)` to the critical line under `s = 1/2 + i t`.
-/
theorem ClayRiemannHypothesis.Formulations.XiZeros.arg_mem_critical_line
    (h : ClayRiemannHypothesis.Formulations.XiZeros) {t : ℂ} (ht : xi t = 0) :
    xi_argument t ∈ CriticalLine :=
  (xi_argument.mem_critical_line_iff_real t).2 (h t ht)

/--
Analytic zero correspondence between Riemann's `ξ(t)` and nontrivial zeros of `ζ(s)`, expressed
with the coordinate change `s = 1/2 + i t`.

This is a theorem, proved below as `ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds`;
it is kept as a named proposition so that the two directions can be referred to separately.
-/
def ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence : Prop :=
  (∀ t : ℂ, xi t = 0 → IsNontrivialZero (xi_argument t)) ∧
    (∀ s : ℂ, IsNontrivialZero s → xi (zeta_zero_parameter s) = 0)

/-- A zero of `ξ(t)` gives the corresponding nontrivial zero of `ζ(s)`. -/
theorem ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.zeta_zero
    (hCorr : ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence) {t : ℂ} (ht : xi t = 0) :
    IsNontrivialZero (xi_argument t) :=
  hCorr.1 t ht

/-- A nontrivial zero of `ζ(s)` gives the corresponding zero of `ξ(t)`. -/
theorem ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.xi_zero
    (hCorr : ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence) {s : ℂ} (hs : IsNontrivialZero s) :
    xi (zeta_zero_parameter s) = 0 :=
  hCorr.2 s hs

/-- For `s ∉ {0, 1}`, the pole-cancelled expression used by `xi` equals `s (s - 1) Λ(s)`. -/
theorem ClayRiemannHypothesis.Support.xi_polynomial_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s * (s - 1) * completedRiemannZeta₀ s + 1 = s * (s - 1) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- `Λ` does not vanish at the trivial zeros: there the zero of `ζ` comes from the pole of `Γ`. -/
theorem ClayRiemannHypothesis.Support.completedRiemannZeta_ne_zero_of_trivial_zero (n : ℕ) :
    completedRiemannZeta (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  have hs : (1 - (-2 * ((n : ℂ) + 1))) = 2 * (n : ℂ) + 3 := by ring
  rw [hs]
  have hre : 1 < (2 * (n : ℂ) + 3).re := by
    simp only [add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hζ := riemannZeta_ne_zero_of_one_lt_re hre
  have hne : (2 * (n : ℂ) + 3) ≠ 0 := by
    intro h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [riemannZeta_def_of_ne_zero hne] at hζ
  intro h
  apply hζ
  rw [h, zero_div]

/-- `xi` written with Mathlib's `completedRiemannZeta₀`. -/
theorem ClayRiemannHypothesis.Support.xi_eq_completedRiemannZeta₀ (t : ℂ) :
    xi t = (1 / 2 : ℂ) *
      (xi_argument t * (xi_argument t - 1) * completedRiemannZeta₀ (xi_argument t) + 1) :=
  xi.eq_xi_argument t

/-- A zero of `ξ(t)` is a nontrivial zero of `ζ` at `s = 1/2 + i t`. -/
theorem ClayRiemannHypothesis.Support.xi_zero_imp_nontrivial_zero (t : ℂ) (ht : xi t = 0) :
    IsNontrivialZero (xi_argument t) := by
  set s := xi_argument t with hs
  rw [ClayRiemannHypothesis.Support.xi_eq_completedRiemannZeta₀] at ht
  have h0 : s ≠ 0 := by
    intro h
    rw [← hs, h] at ht
    norm_num at ht
  have h1 : s ≠ 1 := by
    intro h
    rw [← hs, h] at ht
    norm_num at ht
  rw [← hs, ClayRiemannHypothesis.Support.xi_polynomial_eq h0 h1] at ht
  have hΛ : completedRiemannZeta s = 0 := by
    have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    simpa [h0, h1'] using ht
  refine ⟨?_, ?_, h1⟩
  · rw [riemannZeta_def_of_ne_zero h0, hΛ, zero_div]
  · rintro ⟨n, hn⟩
    exact ClayRiemannHypothesis.Support.completedRiemannZeta_ne_zero_of_trivial_zero n (hn ▸ hΛ)

/-- A nontrivial zero `s` of `ζ` gives a zero of `ξ` at `t = -i (s - 1/2)`. -/
theorem ClayRiemannHypothesis.Support.nontrivial_zero_imp_xi_zero (s : ℂ)
    (hs : IsNontrivialZero s) :
    xi (zeta_zero_parameter s) = 0 := by
  obtain ⟨hζ, htriv, h1⟩ := hs
  have h0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hζ
    norm_num at hζ
  rw [ClayRiemannHypothesis.Support.xi_eq_completedRiemannZeta₀,
    xi_argument.comp_zeta_zero_parameter, ClayRiemannHypothesis.Support.xi_polynomial_eq h0 h1]
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero h0] at hζ
    rcases div_eq_zero_iff.mp hζ with h | h
    · exact h
    · exact absurd h (gammaReal_ne_zero_of_ne h0 htriv)
  rw [hΛ]
  ring

/-- The analytic zero correspondence between `ξ(t)` and the nontrivial zeros of `ζ(s)` holds. -/
theorem ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds :
    ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence :=
  ⟨ClayRiemannHypothesis.Support.xi_zero_imp_nontrivial_zero,
    ClayRiemannHypothesis.Support.nontrivial_zero_imp_xi_zero⟩

/--
Riemann's `ξ(t)` wording and the critical-line zeta wording are equivalent, via the zero
correspondence `ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds`.
-/
theorem ClayRiemannHypothesis.Formulations.XiZeros.iff_zeta :
    ClayRiemannHypothesis.Formulations.XiZeros ↔ ClayRiemannHypothesis := by
  have hCorr := ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds
  constructor
  · intro hXi s hs
    have htZero : xi (zeta_zero_parameter s) = 0 :=
      hCorr.xi_zero hs
    have htReal : IsRealComplex (zeta_zero_parameter s) := hXi _ htZero
    exact (zeta_zero_parameter.is_real_iff_mem_critical_line s).1 htReal
  · intro hZeta t ht
    exact (xi_argument.mem_critical_line_iff_real t).1
      (hZeta (xi_argument t) (hCorr.zeta_zero ht))

/-- The `ξ(t)` wording gives the zeta zero wording. -/
theorem ClayRiemannHypothesis.Formulations.XiZeros.critical_line
    (h : ClayRiemannHypothesis.Formulations.XiZeros) :
    ClayRiemannHypothesis :=
  ClayRiemannHypothesis.Formulations.XiZeros.iff_zeta.1 h

/-- The critical-line zeta wording gives the `ξ(t)` wording. -/
theorem ClayRiemannHypothesis.xi_zeros (h : ClayRiemannHypothesis) :
    ClayRiemannHypothesis.Formulations.XiZeros :=
  ClayRiemannHypothesis.Formulations.XiZeros.iff_zeta.2 h

/-- The critical-line wording is equivalent to the real-part formulation. -/
theorem ClayRiemannHypothesis.iff_real_part :
    ClayRiemannHypothesis ↔ ClayRiemannHypothesis.Formulations.RealPart := by
  constructor
  · intro h s hs
    simpa [ClayRiemannHypothesis, CriticalLine] using h s hs
  · intro h s hs
    simpa [ClayRiemannHypothesis, CriticalLine] using h s hs

/-- The Clay critical-line statement is equivalent to Riemann's original `ξ(t)` zero wording. -/
theorem ClayRiemannHypothesis.iff_xi :
    ClayRiemannHypothesis ↔ ClayRiemannHypothesis.Formulations.XiZeros :=
  ClayRiemannHypothesis.Formulations.XiZeros.iff_zeta.symm

/-- Rephrase critical-line membership as the equation `re s = 1 / 2`. -/
theorem ClayRiemannHypothesis.real_part
    (h : ClayRiemannHypothesis) :
    ClayRiemannHypothesis.Formulations.RealPart :=
  ClayRiemannHypothesis.iff_real_part.1 h

/-- Translate the `ξ(t)` wording back to zeta zeros. -/
theorem ClayRiemannHypothesis.Formulations.XiZeros.zeta_zeros
    (h : ClayRiemannHypothesis.Formulations.XiZeros) :
    ClayRiemannHypothesis :=
  ClayRiemannHypothesis.iff_xi.2 h

/-- Under the Clay critical-line statement, every nontrivial zero has real part `1 / 2`. -/
theorem ClayRiemannHypothesis.zero_re_eq_half
    (h : ClayRiemannHypothesis) {s : ℂ} (hs : IsNontrivialZero s) :
    s.re = 1 / 2 :=
  h.real_part s hs

/-- Under RH, every nontrivial zero belongs to the critical line. -/
theorem ClayRiemannHypothesis.Formulations.RealPart.zero_mem_critical_line
    (h : ClayRiemannHypothesis.Formulations.RealPart) {s : ℂ} (hs : IsNontrivialZero s) :
    s ∈ CriticalLine := by
  simpa [CriticalLine] using h s hs

/-- Under the Clay critical-line statement, every nontrivial zero belongs to the critical line. -/
theorem ClayRiemannHypothesis.zero_mem_critical_line
    (h : ClayRiemannHypothesis) {s : ℂ} (hs : IsNontrivialZero s) :
    s ∈ CriticalLine :=
  h s hs

/-- Under the Clay critical-line statement, every nontrivial zero lies in the critical strip. -/
theorem ClayRiemannHypothesis.zero_mem_critical_strip
    (h : ClayRiemannHypothesis) {s : ℂ} (hs : IsNontrivialZero s) :
    s ∈ CriticalStrip :=
  CriticalLine.mem_critical_strip (h.zero_mem_critical_line hs)

/-- The real-part RH statement is equivalent to the standard nontrivial-zero formulation. -/
theorem ClayRiemannHypothesis.Formulations.RealPart.iff_mathlib :
    ClayRiemannHypothesis.Formulations.RealPart ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h s hs0 htriv hs1
    exact h s ⟨hs0, htriv, hs1⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-- The real-part RH statement implies the standard nontrivial-zero formulation. -/
theorem ClayRiemannHypothesis.Formulations.RealPart.mathlib : ClayRiemannHypothesis.Formulations.RealPart → _root_.RiemannHypothesis :=
  ClayRiemannHypothesis.Formulations.RealPart.iff_mathlib.1

/-- Mathlib's standard nontrivial-zero formulation implies the real-part RH statement. -/
theorem ClayRiemannHypothesis.Formulations.RealPart.of_mathlib : _root_.RiemannHypothesis → ClayRiemannHypothesis.Formulations.RealPart :=
  ClayRiemannHypothesis.Formulations.RealPart.iff_mathlib.2

/-- Translate Mathlib's standard RH formulation into the Clay critical-line statement. -/
theorem ClayRiemannHypothesis.of_mathlib
    (h : _root_.RiemannHypothesis) :
    ClayRiemannHypothesis :=
  ClayRiemannHypothesis.iff_real_part.2 (ClayRiemannHypothesis.Formulations.RealPart.of_mathlib h)

/-- Translate the Clay critical-line statement into Mathlib's standard RH formulation. -/
theorem ClayRiemannHypothesis.mathlib
    (h : ClayRiemannHypothesis) :
    _root_.RiemannHypothesis :=
  ClayRiemannHypothesis.Formulations.RealPart.mathlib h.real_part

/-!
Prime-number theory infrastructure used in the Clay write-up: we reuse Mathlib's standard
definitions of the Chebyshev functions and the prime counting function.
-/

/-- The Chebyshev `ψ(x)` function `∑_{n ≤ x} Λ(n)` from Mathlib. -/
noncomputable def psi_function (x : ℝ) : ℝ :=
  Chebyshev.psi x

/-- The Chebyshev `θ(x)` function `∑_{p ≤ x} log p` from Mathlib. -/
noncomputable def theta_function (x : ℝ) : ℝ :=
  Chebyshev.theta x

/-- The prime counting function `π(⌊x⌋₊)` from Mathlib. -/
noncomputable def prime_counting_function (x : ℝ) : ℕ :=
  Nat.primeCounting ⌊x⌋₊

/-!
## Chebyshev identities (from the Clay narrative)

Chebyshev defines `θ(x) = ∑_{p ≤ x} log p` and `ψ(x) = ∑_{p^k ≤ x} log p`; the Clay PDF writes this
as `ψ(x) = θ(x) + θ(√x) + θ(∛x) + ...` (finite for fixed `x`). Mathlib proves the corresponding
finite-sum identities.
-/

/-- `ψ(x) = ∑_{n=1}^{⌊log x / log 2⌋} θ(x^{1/n})` for `x ≥ 0` (Clay PDF, Section II). -/
theorem psi_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    psi_function x =
      ∑ n ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, theta_function (x ^ ((1 : ℝ) / n)) := by
  simpa [psi_function, theta_function] using Chebyshev.psi_eq_sum_theta (x := x) hx

/-- `ψ(x) = θ(x) + ∑_{n=2}^{⌊log x / log 2⌋} θ(x^{1/n})` for `x ≥ 2` (Clay PDF, Section II). -/
theorem psi_eq_theta_add_sum {x : ℝ} (hx : 2 ≤ x) :
    psi_function x =
      theta_function x +
        ∑ n ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊, theta_function (x ^ ((1 : ℝ) / n)) := by
  simpa [psi_function, theta_function] using Chebyshev.psi_eq_theta_add_sum_theta (x := x) hx

/-- `θ(x)` is the logarithm of the primorial `∏_{p ≤ x} p` (Mathlib: `Chebyshev.theta_eq_log_primorial`). -/
theorem theta_eq_log_primorial (x : ℝ) : theta_function x = Real.log (primorial ⌊x⌋₊) := by
  simpa [theta_function] using Chebyshev.theta_eq_log_primorial x

/-!
## Gauss' logarithmic integral and Riemann's `Π(x)`
-/

/--
The logarithmic integral `Li(x)` used by Gauss.

The Clay PDF defines it as a Cauchy principal value `∫₀ˣ dt / log t`. For a non-singular
definition we use the common variant `∫₂ˣ dt / log t`.
-/
noncomputable def logarithmic_integral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- The prime counting function `π(x)` as a real number. -/
noncomputable def prime_counting_real (x : ℝ) : ℝ :=
  (prime_counting_function x : ℝ)

/--
Riemann's weighted prime counting function `Π(x)` from the Clay PDF (equation (5)):
`Π(x) = π(x) + (1/2)π(√x) + (1/3)π(x^{1/3}) + ...`.

We implement this as a finite sum with upper limit `⌊log x / log 2⌋`, since `π(x^{1/n}) = 0`
once `x^{1/n} < 2`.
-/
noncomputable def riemann_pi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    prime_counting_real (x ^ ((1 : ℝ) / n)) / n

/-!
## Dirichlet series for `Λ(n)` and the logarithmic derivative of `ζ(s)`
-/

/--
For `re s > 1`, the Dirichlet series of the von Mangoldt function `Λ` agrees with the negative
logarithmic derivative `-ζ'(s)/ζ(s)` (Clay PDF, Section II).
-/
theorem von_mangoldt_lseries_eq_negative_log_derivative_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s := by
  simpa using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs

/-!
## More provable consequences from Mathlib
-/

/--
Euler product written in the “`exp ∘ log`” form.

This corresponds to the Clay PDF’s equation (2), but avoids any issues about choosing a branch of
the complex logarithm by stating an identity after applying `exp`.
-/
theorem riemann_zeta_euler_product_exp_log {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  _root_.riemannZeta_eulerProduct_exp_log hs

/-- Chebyshev's classical explicit upper bound `θ(x) ≤ log 4 · x`. -/
theorem theta_le_log4_mul_self {x : ℝ} (hx : 0 ≤ x) :
    theta_function x ≤ Real.log 4 * x := by
  simpa [theta_function] using Chebyshev.theta_le_log4_mul_x (x := x) hx

/-- Trivial inequality `θ(x) ≤ ψ(x)` (since `ψ` includes prime powers). -/
theorem theta_le_psi (x : ℝ) : theta_function x ≤ psi_function x := by
  simpa [theta_function, psi_function] using Chebyshev.theta_le_psi x

/-- Chebyshev’s explicit bound on `|ψ(x) - θ(x)|` (one of the standard comparison estimates). -/
theorem abs_psi_sub_theta_le_sqrt_log {x : ℝ} (hx : 1 ≤ x) :
    |psi_function x - theta_function x| ≤ 2 * Real.sqrt x * Real.log x := by
  simpa [psi_function, theta_function] using Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx

/-- Explicit upper bound on `ψ(x)` from Mathlib’s Chebyshev development. -/
theorem psi_function_le {x : ℝ} (hx : 1 ≤ x) :
    psi_function x ≤ Real.log 4 * x + 2 * Real.sqrt x * Real.log x := by
  simpa [psi_function] using Chebyshev.psi_le (x := x) hx

/-- A coarser (but simpler) linear bound `ψ(x) ≤ (log 4 + 4) x`. -/
theorem psi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    psi_function x ≤ (Real.log 4 + 4) * x := by
  simpa [psi_function] using Chebyshev.psi_le_const_mul_self (x := x) hx

/-- Every trivial zero is a zero of `ζ`. -/
theorem IsTrivialZero.riemann_zeta_eq_zero {s : ℂ} (hs : IsTrivialZero s) : riemannZeta s = 0 := by
  rcases hs with ⟨n, rfl⟩
  simpa using riemannZeta_neg_two_mul_nat_add_one n

/-!
## Main theorem

This final theorem records the Riemann Hypothesis target directly. Replace the placeholder proof
when one is available.
-/

/-- Clay Millennium Prize target for the Riemann Hypothesis. -/
theorem clay_prize_riemann_hypothesis :
    ClayRiemannHypothesis := by
  sorry

end Millennium
