import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

set_option diagnostics true
set_option diagnostics.threshold 3000
set_option linter.unusedVariables false

namespace Millennium

open Complex
open Filter
open scoped BigOperators
open scoped Topology

/-!
# The Riemann Hypothesis

This file states the Clay Millennium problem “Riemann Hypothesis” in Lean, following the official
Clay problem description:
`Problems/RiemannHypothesis/references/clay/riemann.pdf`.

We reuse Mathlib's analytic continuation of the Riemann zeta function `riemannZeta : ℂ → ℂ` and
record a few standard facts mentioned in the Clay write-up (Dirichlet series and Euler product for
`re s > 1`, the functional equation for the completed zeta function, and the definition of
Riemann's `ξ`-function).

The Millennium problem itself is the statement `RiemannHypothesis` below.
-/

/-!
## Zeta: series, Euler product, pole at `s = 1`
-/

/-- The Dirichlet series definition of `ζ(s)` is valid for `re s > 1` (Clay PDF, Section I). -/
theorem riemannZeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa using zeta_eq_tsum_one_div_nat_cpow hs

/-- The Euler product `ζ(s) = ∏_p (1 - p^{-s})^{-1}` holds for `re s > 1` (Clay PDF, Section II). -/
theorem riemannZeta_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  _root_.riemannZeta_eulerProduct_hasProd hs

/--
The zeta function is differentiable away from `s = 1` (meromorphic continuation).

This is a Mathlib theorem (`differentiableAt_riemannZeta`) referenced by the Clay PDF (Section I).
-/
theorem differentiableAt_riemannZeta' {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-- The residue of `ζ(s)` at `s = 1` is `1` (Clay PDF, Section I). -/
theorem riemannZeta_residue_one' :
    Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

/-!
## Completed zeta and the functional equation
-/

/-- The completed zeta function `Λ(s)` from Mathlib (Clay PDF, equation (1)). -/
noncomputable abbrev completedZeta (s : ℂ) : ℂ :=
  completedRiemannZeta s

/-- Functional equation in the symmetric form `Λ(1 - s) = Λ(s)` (Clay PDF, equation (1)). -/
theorem completedZeta_one_sub (s : ℂ) : completedZeta (1 - s) = completedZeta s := by
  simpa [completedZeta] using completedRiemannZeta_one_sub s

/-!
## Riemann's `ξ(t)` function (Clay PDF, Section I)
-/

/--
Riemann's `ξ`-function, as a function of the complex variable `t`, using the substitution
`s = 1/2 + i t` from the Clay PDF.
-/
noncomputable def xi (t : ℂ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * t
  (1 / 2 : ℂ) * s * (s - 1) * completedZeta s

/-- The function `xi` is even: `ξ(-t) = ξ(t)`, from the functional equation `Λ(1-s)=Λ(s)`. -/
theorem xi_even (t : ℂ) : xi (-t) = xi t := by
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
  -- `s(-t) = 1 - s(t)` and `Λ(1 - s) = Λ(s)` imply evenness.
  calc
    xi (-t)
        = (1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * completedZeta (1 - s) := by
            -- Expand the `let`-binding in `xi` and rewrite the substituted value using `hs_neg`.
            dsimp [xi]
            simp [hs_neg'']
    _   = (1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * completedZeta s := by
            simp [completedZeta_one_sub]
    _   = (1 / 2 : ℂ) * s * (s - 1) * completedZeta s := by
            -- The polynomial factor is invariant under `s ↦ 1 - s`.
            ring
    _   = xi t := by
            simp [xi, s, completedZeta]

/-!
## Zeros and the Clay statement
-/

/-- Trivial zeros: the negative even integers `-2, -4, -6, ...`. -/
def IsTrivialZero (s : ℂ) : Prop :=
  ∃ n : ℕ, s = -2 * (n + 1)

/-- A “nontrivial” zero is a zero that is not a trivial zero and not the pole at `s = 1`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬IsTrivialZero s ∧ s ≠ 1

/-- The critical strip `{ s | 0 < re s ∧ re s < 1 }` (Clay PDF, Section I). -/
def CriticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The critical line `{ s | re s = 1/2 }` (Clay PDF, Section I). -/
def CriticalLine : Set ℂ :=
  {s : ℂ | s.re = 1 / 2}

/--
The Clay statement: all nontrivial zeros of `ζ(s)` have real part `1/2`.

This is equivalent to Mathlib's `_root_.RiemannHypothesis`.
-/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), IsNontrivialZero s → s.re = 1 / 2

/-- The Clay statement `RiemannHypothesis` is equivalent to Mathlib’s `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_iff_mathlib : RiemannHypothesis ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h s hs0 htriv hs1
    exact h s ⟨hs0, htriv, hs1⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-!
Prime-number theory infrastructure used in the Clay write-up: we reuse Mathlib's standard
definitions of the Chebyshev functions and the prime counting function.
-/

/-- The Chebyshev `ψ(x)` function `∑_{n ≤ x} Λ(n)` from Mathlib. -/
noncomputable abbrev psiFunction (x : ℝ) : ℝ :=
  Chebyshev.psi x

/-- The Chebyshev `θ(x)` function `∑_{p ≤ x} log p` from Mathlib. -/
noncomputable abbrev thetaFunction (x : ℝ) : ℝ :=
  Chebyshev.theta x

/-- The prime counting function `π(⌊x⌋₊)` from Mathlib. -/
noncomputable def primeCountingFunction (x : ℝ) : ℕ :=
  Nat.primeCounting ⌊x⌋₊

/-!
## Chebyshev identities (from the Clay narrative)

Chebyshev defines `θ(x) = ∑_{p ≤ x} log p` and `ψ(x) = ∑_{p^k ≤ x} log p`; the Clay PDF writes this
as `ψ(x) = θ(x) + θ(√x) + θ(∛x) + ...` (finite for fixed `x`). Mathlib proves the corresponding
finite-sum identities.
-/

/-- `ψ(x) = ∑_{n=1}^{⌊log x / log 2⌋} θ(x^{1/n})` for `x ≥ 0` (Clay PDF, Section II). -/
theorem psiFunction_eq_sum_thetaFunction {x : ℝ} (hx : 0 ≤ x) :
    psiFunction x =
      ∑ n ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, thetaFunction (x ^ ((1 : ℝ) / n)) := by
  simpa [psiFunction, thetaFunction] using Chebyshev.psi_eq_sum_theta (x := x) hx

/-- `ψ(x) = θ(x) + ∑_{n=2}^{⌊log x / log 2⌋} θ(x^{1/n})` for `x ≥ 2` (Clay PDF, Section II). -/
theorem psiFunction_eq_theta_add_sum_thetaFunction {x : ℝ} (hx : 2 ≤ x) :
    psiFunction x =
      thetaFunction x +
        ∑ n ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊, thetaFunction (x ^ ((1 : ℝ) / n)) := by
  simpa [psiFunction, thetaFunction] using Chebyshev.psi_eq_theta_add_sum_theta (x := x) hx

/-- `θ(x)` is the logarithm of the primorial `∏_{p ≤ x} p` (Mathlib: `Chebyshev.theta_eq_log_primorial`). -/
theorem thetaFunction_eq_log_primorial (x : ℝ) : thetaFunction x = Real.log (primorial ⌊x⌋₊) := by
  simpa [thetaFunction] using Chebyshev.theta_eq_log_primorial x

/-!
## Gauss' logarithmic integral and Riemann's `Π(x)`
-/

/--
The logarithmic integral `Li(x)` used by Gauss.

The Clay PDF defines it as a Cauchy principal value `∫₀ˣ dt / log t`. For a non-singular
definition we use the common variant `∫₂ˣ dt / log t`.
-/
noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- The prime counting function `π(x)` as a real number. -/
noncomputable def primeCountingReal (x : ℝ) : ℝ :=
  (primeCountingFunction x : ℝ)

/--
Riemann's weighted prime counting function `Π(x)` from the Clay PDF (equation (5)):
`Π(x) = π(x) + (1/2)π(√x) + (1/3)π(x^{1/3}) + ...`.

We implement this as a finite sum with upper limit `⌊log x / log 2⌋`, since `π(x^{1/n}) = 0`
once `x^{1/n} < 2`.
-/
noncomputable def riemannPi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    primeCountingReal (x ^ ((1 : ℝ) / n)) / n

/-!
## Dirichlet series for `Λ(n)` and the logarithmic derivative of `ζ(s)`
-/

/--
For `re s > 1`, the Dirichlet series of the von Mangoldt function `Λ` agrees with the negative
logarithmic derivative `-ζ'(s)/ζ(s)` (Clay PDF, Section II).
-/
theorem LSeries_vonMangoldt_eq_negLogDeriv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
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
theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  _root_.riemannZeta_eulerProduct_exp_log hs

/-- Chebyshev's classical explicit upper bound `θ(x) ≤ log 4 · x`. -/
theorem thetaFunction_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) :
    thetaFunction x ≤ Real.log 4 * x := by
  simpa [thetaFunction] using Chebyshev.theta_le_log4_mul_x (x := x) hx

/-- Trivial inequality `θ(x) ≤ ψ(x)` (since `ψ` includes prime powers). -/
theorem thetaFunction_le_psiFunction (x : ℝ) : thetaFunction x ≤ psiFunction x := by
  simpa [thetaFunction, psiFunction] using Chebyshev.theta_le_psi x

/-- Chebyshev’s explicit bound on `|ψ(x) - θ(x)|` (one of the standard comparison estimates). -/
theorem abs_psiFunction_sub_thetaFunction_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |psiFunction x - thetaFunction x| ≤ 2 * Real.sqrt x * Real.log x := by
  simpa [psiFunction, thetaFunction] using Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx

/-- Explicit upper bound on `ψ(x)` from Mathlib’s Chebyshev development. -/
theorem psiFunction_le {x : ℝ} (hx : 1 ≤ x) :
    psiFunction x ≤ Real.log 4 * x + 2 * Real.sqrt x * Real.log x := by
  simpa [psiFunction] using Chebyshev.psi_le (x := x) hx

/-- A coarser (but simpler) linear bound `ψ(x) ≤ (log 4 + 4) x`. -/
theorem psiFunction_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    psiFunction x ≤ (Real.log 4 + 4) * x := by
  simpa [psiFunction] using Chebyshev.psi_le_const_mul_self (x := x) hx

/-- Every trivial zero is a zero of `ζ`. -/
theorem IsTrivialZero.riemannZeta_eq_zero {s : ℂ} (hs : IsTrivialZero s) : riemannZeta s = 0 := by
  rcases hs with ⟨n, rfl⟩
  simpa using riemannZeta_neg_two_mul_nat_add_one n

end Millennium
