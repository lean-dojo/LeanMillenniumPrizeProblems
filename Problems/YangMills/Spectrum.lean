import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Order.Bounds.Basic

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# The spectral clause in Jaffe–Witten, §4

Here `σ` is intended to be the **full real spectrum** of the self-adjoint
Hamiltonian, including continuous spectrum, not just its eigenvalues.
`QFT/Operator.lean` defines this set from the resolvent of an actual operator;
`QFT/Wightman.lean` ties that operator to time translations.
-/

namespace YangMills

/-- Positive energy: there is no spectrum below zero. -/
def PositiveEnergy (σ : Set ℝ) : Prop :=
  ∀ E ∈ σ, 0 ≤ E

/-- A positive number Δ is a gap when the open interval (0, Δ) misses σ.
The endpoint Δ is allowed in σ; we do not demand a one-particle eigenstate. -/
def IsMassGap (σ : Set ℝ) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ E ∈ σ, ¬ (0 < E ∧ E < Δ)

/-- The admissible positive gaps, whose supremum is the physical mass. -/
def admissibleGaps (σ : Set ℝ) : Set ℝ := {Δ | IsMassGap σ Δ}

/-- This expression represents the mass only when `admissibleGaps σ` is
nonempty and bounded above. Lean's real supremum is total, so those hypotheses
must not be omitted; see `HasPositiveFiniteMass`. -/
noncomputable def mass (σ : Set ℝ) : ℝ := sSup (admissibleGaps σ)

/-- The two requirements in §4: a positive gap exists and its supremum is finite.
Boundedness is essential: σ = {0} has arbitrarily large gaps and is excluded. -/
def HasPositiveFiniteMass (σ : Set ℝ) : Prop :=
  (∃ Δ : ℝ, IsMassGap σ Δ) ∧ BddAbove (admissibleGaps σ)

/-- Under the stated hypotheses the supremum really is strictly positive. -/
theorem mass_pos (σ : Set ℝ) (h : HasPositiveFiniteMass σ) :
    0 < mass σ := by
  obtain ⟨⟨Δ, hΔ⟩, hbounded⟩ := h
  exact lt_of_lt_of_le hΔ.1 (le_csSup hbounded hΔ)

/-- The interval formulation also says every nonzero spectral energy is at
least Δ, provided the positive-energy condition holds. -/
theorem isMassGap_iff (σ : Set ℝ) (hpos : PositiveEnergy σ) (Δ : ℝ) :
    IsMassGap σ Δ ↔ 0 < Δ ∧ ∀ E ∈ σ, E = 0 ∨ Δ ≤ E := by
  constructor
  · rintro ⟨hΔ, hgap⟩
    refine ⟨hΔ, ?_⟩
    intro E hE
    by_cases hzero : E = 0
    · exact Or.inl hzero
    · exact Or.inr (le_of_not_gt (fun hlt =>
        hgap E hE ⟨lt_of_le_of_ne (hpos E hE) (Ne.symm hzero), hlt⟩))
  · rintro ⟨hΔ, hgap⟩
    refine ⟨hΔ, ?_⟩
    intro E hE hbetween
    rcases hgap E hE with hzero | hle
    · exact (ne_of_gt hbetween.1) hzero
    · exact (not_lt_of_ge hle) hbetween.2

/-- A positive spectral energy bounds every admissible gap from above.
This does not require that this energy be an eigenvalue. -/
theorem gaps_bounded_of_positive_spectral_value (σ : Set ℝ)
    {E : ℝ} (hE : E ∈ σ) (hpositive : 0 < E) :
    BddAbove (admissibleGaps σ) := by
  refine ⟨E, ?_⟩
  intro Δ hΔ
  exact le_of_not_gt (fun hlt => hΔ.2 E hE ⟨hpositive, hlt⟩)

/-- A vacuum-only (or empty) spectrum cannot pass the finite-mass clause.
More generally, without a positive spectral value every positive number
would be a gap, so there could be no finite upper bound. -/
theorem no_finite_mass_without_positive_energy (σ : Set ℝ)
    (hnonpos : ∀ E ∈ σ, E ≤ 0) : ¬ HasPositiveFiniteMass σ := by
  rintro ⟨_, M, hM⟩
  have hpositive : 0 < max M 0 + 1 :=
    lt_of_le_of_lt (le_max_right M 0) (lt_add_one (max M 0))
  have hgap : IsMassGap σ (max M 0 + 1) := by
    refine ⟨hpositive, ?_⟩
    intro E hE hbetween
    exact (not_lt_of_ge (hnonpos E hE)) hbetween.1
  have hbound : max M 0 + 1 ≤ M := hM hgap
  exact (not_le_of_gt
    (lt_of_le_of_lt (le_max_left M 0) (lt_add_one (max M 0)))) hbound

theorem vacuum_only_has_no_finite_mass :
    ¬ HasPositiveFiniteMass ({0} : Set ℝ) := by
  apply no_finite_mass_without_positive_energy
  intro E hE
  have hzero : E = 0 := Set.mem_singleton_iff.mp hE
  exact hzero.le

/-- Finite supremum mass is equivalent to the existence of some positive
spectral value, once a gap exists. No isolated particle/eigenvector is required. -/
theorem hasPositiveFiniteMass_iff (σ : Set ℝ) :
    HasPositiveFiniteMass σ ↔
      (∃ Δ : ℝ, IsMassGap σ Δ) ∧ ∃ E ∈ σ, 0 < E := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hnone
    have hnonpos : ∀ E ∈ σ, E ≤ 0 := by
      intro E hE
      exact le_of_not_gt (fun hpos => hnone ⟨E, hE, hpos⟩)
    exact no_finite_mass_without_positive_energy σ hnonpos h
  · rintro ⟨hgap, E, hE, hpos⟩
    exact ⟨hgap, gaps_bounded_of_positive_spectral_value σ hE hpos⟩

/-- Every positive spectral energy is at least the supremum mass. -/
theorem mass_le_positive_spectral_value (σ : Set ℝ)
    (h : HasPositiveFiniteMass σ) {E : ℝ} (hE : E ∈ σ) (hpos : 0 < E) :
    mass σ ≤ E := by
  apply csSup_le h.1
  intro Δ hΔ
  exact le_of_not_gt (fun hlt => hΔ.2 E hE ⟨hpos, hlt⟩)

/-- The supremum in the source is itself an admissible gap, so the
supremum-based formulation cannot hide spectrum strictly below its mass. -/
theorem mass_isMassGap (σ : Set ℝ) (h : HasPositiveFiniteMass σ) :
    IsMassGap σ (mass σ) := by
  refine ⟨mass_pos σ h, ?_⟩
  intro E hE hbetween
  exact (not_lt_of_ge (mass_le_positive_spectral_value σ h hE hbetween.1)) hbetween.2

end YangMills
