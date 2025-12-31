import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.IsPrimePow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting

set_option diagnostics true
set_option diagnostics.threshold 3000
set_option linter.unusedVariables false

namespace Millennium

/-!
# Riemann Hypothesis Millennium Problem

This file formalizes the Millennium Prize problem on the Riemann Hypothesis. This is the first Millennium problem I had learnt in my undergrad and I was excited to formalize it in Lean.

The Riemann Hypothesis states that all non-trivial zeros of the Riemann zeta function lie on the
critical line, which is the vertical line in the complex plane with real part 1/2.

## Key concepts formalized in this file:

1. RiemannZeta: The Riemann zeta function ζ(s), defined for complex s
2. NontrivialZeros: Zeros of ζ(s) that are not negative even integers
3. CriticalStrip: The region in the complex plane where 0 < Re(s) < 1
4. CriticalLine: The line Re(s) = 1/2 within the critical strip
5. Prime-related functions connected to the zeta function:
   - vonMangoldt function Λ(n)
   - Chebyshev psi function ψ(x)
   - Prime counting function π(x)
6. Li's Criterion: An equivalent formulation of the Riemann Hypothesis using specific coefficients

The Riemann Hypothesis has enormous implications for the distribution of prime numbers. Its truth
would confirm that primes follow the most regular possible distribution allowed by the counting
function constraints.

## References
- Riemann, B. (1859). "Über die Anzahl der Primzahlen unter einer gegebenen Größe"
- Edwards, H.M. (1974). "Riemann's Zeta Function"
- Bombieri, E. (2000). "Problems of the Millennium: the Riemann Hypothesis"
-/

/-- A complex number is a nontrivial zero of the Riemann zeta function if:
  1. It's a zero of the Riemann zeta function
  2. It's not a negative even integer (which would make it a trivial zero)
  3. It's not the pole at `s = 1`

  The trivial zeros occur at s = -2, -4, -6, ... and are less interesting for the hypothesis. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ (n : ℕ), s = -2 * (n + 1)) ∧ s ≠ 1

/-- The critical strip is the region of the complex plane where 0 < Re(s) < 1.
    All nontrivial zeros of the Riemann zeta function lie in this strip.

    This is a fundamental region for studying the behavior of the zeta function,
    particularly regarding its zeros. -/
def CriticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The critical line is the vertical line in the complex plane with real part 1/2.
    According to the Riemann Hypothesis, all nontrivial zeros lie on this line.

    If true, this would represent a remarkable pattern in the distribution of zeros,
    with profound implications for number theory. -/
def CriticalLine : Set ℂ :=
  {s : ℂ | s.re = 1 / 2}

/-!
Prime-number theory infrastructure: we reuse Mathlib's standard definitions.
-/

/-- The von Mangoldt function `Λ(n)` from Mathlib. -/
noncomputable abbrev vonMangoldt (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-- The Chebyshev `ψ(x)` function from Mathlib. -/
noncomputable abbrev psiFunction (x : ℝ) : ℝ :=
  Chebyshev.psi x

/-- The prime counting function `π(⌊x⌋₊)` from Mathlib. -/
noncomputable def primeCountingFunction (x : ℝ) : ℕ :=
  Nat.primeCounting ⌊x⌋₊

/-- The Li coefficients, used in the Li criterion

    These coefficients, introduced by Xian-Jin Li, provide an alternative formulation
    of the Riemann Hypothesis in terms of positivity conditions. -/
noncomputable def LiCoefficients (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    Complex.re (∑' m : ℕ, if m ≤ n then
               (-1)^(n-m) * (n.choose m) * (iteratedDeriv m (fun s => (riemannZeta (s+1))⁻¹) 0)
             else 0)

/-- # The Riemann Hypothesis: All nontrivial zeros of the Riemann zeta function have real part equal to 1/2.

    This is the central conjecture that has remained unproven since Riemann's
    original paper in 1859, despite substantial numerical evidence supporting it. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), IsNontrivialZero s → s.re = 1 / 2

theorem riemannHypothesis_iff_mathlib : RiemannHypothesis ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h s hs0 htriv hs1
    exact h s ⟨hs0, htriv, hs1⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-!
The Millennium problem is the statement `RiemannHypothesis`. The following two properties are
standard refinements often discussed alongside it; we record them as `Prop`s (no `sorry` proofs).
-/

/-- All zeros of the Riemann zeta function outside the critical strip are simple zeros. -/
def ZerosOutsideCriticalStripAreSimple : Prop :=
  ∀ s : ℂ, ¬CriticalStrip s → riemannZeta s = 0 → deriv riemannZeta s ≠ 0

/-- All trivial zeros of the Riemann zeta function are simple zeros. -/
def TrivialZerosAreSimple : Prop :=
  ∀ n : ℕ, n > 0 → deriv riemannZeta (-2 * ↑n) ≠ 0

/-- # The Riemann Hypothesis states that all zeros of the Riemann zeta function in the critical strip are simple zeros (i.e., have multiplicity 1).

    This means that each zero is a single root, not a multiple root, which would
    influence how certain related functions behave near these zeros. -/
def ZerosHypothesis : Prop :=
  ∀ s : ℂ, CriticalStrip s → riemannZeta s = 0 →
    deriv riemannZeta s ≠ 0

/-- # The Li criterion: an equivalent formulation of the Riemann Hypothesis in terms of the non-negativity of Li coefficients derived from the logarithmic derivative of the zeta function.

    This remarkable equivalence, proved by Li in 1997, states that the Riemann Hypothesis
    is true if and only if all Li coefficients λn are non-negative for n > 0. -/
noncomputable def LiCriterion : Prop :=
  ∀ n : ℕ, n > 0 → LiCoefficients n ≥ 0

end Millennium
