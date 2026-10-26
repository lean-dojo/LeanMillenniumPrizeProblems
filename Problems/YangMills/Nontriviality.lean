import Problems.YangMills.QFT.Wightman
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Non-vacuum states in the existing QFT

These definitions concern the same Hilbert space, vacuum, field words and
Hamiltonian as `WightmanData`. They exclude a vacuum-only theory. They do not
identify the theory as Yang--Mills or impose a non-Gaussianity criterion.
Their adequacy as the full meaning of Section 4's nontriviality requirement
remains subject to review alongside the missing Yang--Mills identification.
-/

noncomputable section
namespace YangMills

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace WightmanData

/-- There is a state outside the complex linear span of the vacuum. -/
def HasNonVacuumState (Q : WightmanData H) : Prop :=
  ∃ v : H, v ∉ Submodule.span ℂ {(Q.vacuum : H)}

/-- A finite product of the actual smeared fields creates a state outside
the vacuum line. No unrelated observable or auxiliary Hilbert space is used. -/
def HasFieldExcitation (Q : WightmanData H) : Prop :=
  ∃ w : List (Q.FieldIndex × TestFunction),
    (Q.word w : H) ∉ Submodule.span ℂ {(Q.vacuum : H)}

theorem HasFieldExcitation.hasNonVacuumState {Q : WightmanData H}
    (h : Q.HasFieldExcitation) : Q.HasNonVacuumState := by
  obtain ⟨w, hw⟩ := h
  exact ⟨Q.word w, hw⟩

end WightmanData

namespace DenselyDefinedOperator

/-- A zero operator on the whole space has a bounded inverse after every
nonzero scalar shift. This checks the actual resolvent, not a chosen spectrum. -/
theorem zero_inResolvent (A : DenselyDefinedOperator H)
    (hdom : ∀ v : H, v ∈ A.domain)
    (hzero : ∀ v : A.domain, A.toLinearMap v = 0)
    (z : ℂ) (hz : z ≠ 0) : A.InResolvent z := by
  refine ⟨(-z⁻¹) • ContinuousLinearMap.id ℂ H, fun v => hdom _, ?_, ?_⟩
  · intro v
    simp [hzero, smul_smul, hz]
  · intro v
    simp [hzero, smul_smul, hz]

end DenselyDefinedOperator

namespace WightmanAxioms

/-- Cyclicity makes non-vacuum states equivalent to field-generated
excitations: the vacuum line is closed, so taking a dense span cannot escape it. -/
theorem hasFieldExcitation_iff {Q : WightmanData H}
    (h : WightmanAxioms H Q) :
    Q.HasFieldExcitation ↔ Q.HasNonVacuumState := by
  constructor
  · exact WightmanData.HasFieldExcitation.hasNonVacuumState
  · intro hstate
    by_contra hfields
    have hall : ∀ w, (Q.word w : H) ∈ Submodule.span ℂ {(Q.vacuum : H)} := by
      simpa [WightmanData.HasFieldExcitation] using hfields
    have hspan : Submodule.span ℂ (Set.range (fun w => (Q.word w : H))) ≤
        Submodule.span ℂ {(Q.vacuum : H)} :=
      Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact hall w)
    have hclosed : IsClosed (Submodule.span ℂ {(Q.vacuum : H)} : Set H) :=
      (Submodule.span ℂ {(Q.vacuum : H)}).closed_of_finiteDimensional
    obtain ⟨v, hv⟩ := hstate
    exact hv (hclosed.closure_subset_iff.mpr hspan (h.cyclic v))

/-- If all states lie on the vacuum line, every positive real energy is in
the resolvent. This is a statement about the theory's own Hamiltonian. -/
theorem no_positive_spectrum_of_no_nonVacuumState {Q : WightmanData H}
    (h : WightmanAxioms H Q) (htrivial : ¬ Q.HasNonVacuumState)
    (E : ℝ) (hE : 0 < E) : E ∉ Q.hamiltonian.realSpectrum := by
  have hall : ∀ v : H, ∃ c : ℂ, c • (Q.vacuum : H) = v := by
    intro v
    apply Submodule.mem_span_singleton.mp
    by_contra hv
    exact htrivial ⟨v, hv⟩
  have hdom : ∀ v : H, v ∈ Q.hamiltonian.domain := by
    intro v
    obtain ⟨c, rfl⟩ := hall v
    exact Q.hamiltonian.domain.smul_mem c h.vacuum_mem
  have hzero : ∀ v : Q.hamiltonian.domain, Q.hamiltonian.toLinearMap v = 0 := by
    intro v
    obtain ⟨c, hc⟩ := hall v
    have heq : v = c • (⟨(Q.vacuum : H), h.vacuum_mem⟩ : Q.hamiltonian.domain) :=
      Subtype.ext hc.symm
    rw [heq, map_smul, h.vacuum_zero, smul_zero]
  exact fun hspec => hspec (Q.hamiltonian.zero_inResolvent hdom hzero (E : ℂ)
    (by exact_mod_cast ne_of_gt hE))

end WightmanAxioms

namespace GappedWightmanTheory

/-- Finite mass already rules out a vacuum-only Hilbert space. Thus this
minimal nontriviality condition adds no hypothesis to the existing target. -/
theorem hasNonVacuumState {Q : WightmanData H}
    (h : GappedWightmanTheory H Q) : Q.HasNonVacuumState := by
  by_contra htrivial
  apply no_finite_mass_without_positive_energy Q.hamiltonian.realSpectrum _ h.massGap
  intro E hE
  exact le_of_not_gt (fun hpos =>
    h.axioms.no_positive_spectrum_of_no_nonVacuumState htrivial E hpos hE)

theorem hasFieldExcitation {Q : WightmanData H}
    (h : GappedWightmanTheory H Q) : Q.HasFieldExcitation :=
  h.axioms.hasFieldExcitation_iff.mpr h.hasNonVacuumState

end GappedWightmanTheory
end YangMills
