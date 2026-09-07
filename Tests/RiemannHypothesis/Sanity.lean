import Problems.RiemannHypothesis.Millennium

/-!
# Riemann Hypothesis: sanity checks

The Clay statement is literally Mathlib's `RiemannHypothesis`; the `ξ(t)` wording is equivalent
without extra hypotheses; Lean's junk values at `s = 0`, `s = 1` and the trivial zeros do not
create spurious "nontrivial zeros".  Only the prize placeholder may use `sorryAx`.
-/

open Millennium Complex

namespace Tests.RiemannHypothesis

/-! ## The statement is Mathlib's `RiemannHypothesis` -/

example : ClayRiemannHypothesis ↔ RiemannHypothesis :=
  ⟨ClayRiemannHypothesis.mathlib, ClayRiemannHypothesis.of_mathlib⟩

/-! ## Axiom audit -/

/-- info: 'Millennium.ClayRiemannHypothesis.Formulations.RealPart.iff_mathlib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayRiemannHypothesis.Formulations.RealPart.iff_mathlib

/-- info: 'Millennium.ClayRiemannHypothesis.Formulations.XiZeros.iff_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayRiemannHypothesis.Formulations.XiZeros.iff_zeta

/-- info: 'Millennium.ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds

/-- info: 'Millennium.expanded_xi_formula.eq_xi_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expanded_xi_formula.eq_xi_of_ne

/-- info: 'Millennium.xi.even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xi.even

/-- info: 'Millennium.clay_prize_riemann_hypothesis' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clay_prize_riemann_hypothesis

/-! ## Junk-value sanity: `s = 0` and `s = 1` are not nontrivial zeros -/

example : ¬ IsNontrivialZero 1 := fun h => h.2.2 rfl

example : riemannZeta 1 ≠ 0 := riemannZeta_one_ne_zero

example : ¬ IsNontrivialZero 0 := fun h => by
  have := h.1
  rw [riemannZeta_zero] at this
  norm_num at this

/-- The trivial zeros are zeros of `ζ` but are excluded from `IsNontrivialZero`. -/
example (n : ℕ) : ¬ IsNontrivialZero (-2 * ((n : ℂ) + 1)) := fun h => h.2.1 ⟨n, rfl⟩

/-! ## The pole-cancelled `xi` versus the expanded PDF formula -/

/-- `t₀` is the parameter with `s = 1/2 + i t₀ = -2`, a trivial zero of `ζ`. -/
noncomputable def t₀ : ℂ := zeta_zero_parameter (-2)

/-- Lean junk value: the expanded PDF formula vanishes at the non-real point `t₀`. -/
example : expanded_xi_formula t₀ = 0 := by
  unfold expanded_xi_formula
  simp only [t₀, xi_argument.comp_zeta_zero_parameter]
  have : riemannZeta (-2) = 0 := by simpa using riemannZeta_neg_two_mul_nat_add_one 0
  simp [this]

example : t₀.im ≠ 0 := by
  simp [t₀, zeta_zero_parameter]
  norm_num

/-- The statement's `xi` does not vanish there. -/
example : xi t₀ ≠ 0 := by
  intro h
  have hzero : IsNontrivialZero (xi_argument t₀) :=
    ClayRiemannHypothesis.Support.xi_zero_imp_nontrivial_zero t₀ h
  rw [t₀, xi_argument.comp_zeta_zero_parameter] at hzero
  exact hzero.2.1 ⟨0, by norm_num⟩

end Tests.RiemannHypothesis
