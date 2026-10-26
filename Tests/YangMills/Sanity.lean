import Problems.YangMills.Millennium

/-!
# Yang–Mills existence and mass gap: sanity checks

The entry point retains the universe-polymorphic, all-group specification. A candidate must
have nonzero stress, and the finite-mass clause excludes a vacuum-only spectrum even though
that spectrum admits positive gaps. These checks concern the proposed formalization; they
neither establish its equivalence to the Clay problem nor supply an existence proof.
-/

open MillenniumYangMills YangMills

universe u

namespace Tests.YangMills

/-! ## Axiom audit: no placeholder proofs or additional axioms -/

/-- info: 'MillenniumYangMills.ClayYangMills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MillenniumYangMills.ClayYangMills

/-- info: 'MillenniumYangMills.clayYangMills_iff_specification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MillenniumYangMills.clayYangMills_iff_specification

/-- info: 'YangMills.FilteredGeneratedCandidate.stress_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms YangMills.FilteredGeneratedCandidate.stress_nonzero

/-- info: 'YangMills.vacuum_only_has_no_finite_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms YangMills.vacuum_only_has_no_finite_mass

/-- info: 'YangMills.hasPositiveFiniteMass_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms YangMills.hasPositiveFiniteMass_iff

/-! ## The entry point preserves the specification and its universe parameter -/

example : ClayYangMills.{u} = YangMillsExistenceAndMassGap.{u} := rfl

example : ClayYangMills.{u} ↔
    ∀ G : CompactSimpleGaugeGroup.{u}, Nonempty (FilteredGeneratedCandidate G) := Iff.rfl

/-! ## Every gauge group must have a candidate with nonzero stress -/

example (h : ClayYangMills.{u}) (G : CompactSimpleGaugeGroup.{u}) :
    Nonempty (FilteredGeneratedCandidate G) := h G

example {G : CompactSimpleGaugeGroup.{u}} (candidate : FilteredGeneratedCandidate G) :
    ¬ (∀ μ ν f v, candidate.stress.field μ ν f v = 0) :=
  candidate.stress_nonzero

/-! ## A positive gap alone does not imply positive finite mass -/

example (Δ : ℝ) (hΔ : 0 < Δ) : IsMassGap ({0} : Set ℝ) Δ := by
  refine ⟨hΔ, ?_⟩
  intro E hE hbetween
  have hzero : E = 0 := Set.mem_singleton_iff.mp hE
  exact (ne_of_gt hbetween.1) hzero

example : ¬ HasPositiveFiniteMass ({0} : Set ℝ) :=
  vacuum_only_has_no_finite_mass

example (σ : Set ℝ) (h : HasPositiveFiniteMass σ) : ∃ E ∈ σ, 0 < E :=
  ((hasPositiveFiniteMass_iff σ).mp h).2

example (σ : Set ℝ) (h : HasPositiveFiniteMass σ) : 0 < mass σ :=
  mass_pos σ h

end Tests.YangMills
