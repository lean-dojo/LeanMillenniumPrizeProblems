import Problems.YangMills.Statement
import Problems.YangMills.Spectrum

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Jaffe--Witten Section 4: directly translatable mathematics

These definitions transcribe the **explicit mathematical shape** of the
written statement. They do not fill in its undefined physical phrases,
and they cannot by themselves serve as a Clay proof target.

Each declaration below has a PDF_EXPLICIT tag in its docstring. When a
term such as "Yang--Mills theory" requires additional interpretation,
that obligation belongs in SourceClassification/requirements.json, not
in a silently inserted assumption or an invented predicate.
-/

noncomputable section

namespace YangMills.PDFLiteral

universe u

/-- PDF_EXPLICIT (Section 4, printed p.6): space-time is R^4.
The coordinate-model equivalence with the existing four-dimensional
spacetime abbreviation is definitional; this proves no field exists. -/
abbrev FourDimensionalSpace : Type := Fin 4 → ℝ

theorem fourDimensionalSpace_eq_spacetime :
    FourDimensionalSpace = YangMills.Spacetime := rfl

/-- PDF_EXPLICIT (Section 4, printed p.6): H Ω = 0.
For an unbounded Hamiltonian, the equation includes vacuum-domain
membership. The H and Ω here belong to the *chosen* QuantumTheory model;
the formula is direct, but the model's fidelity still needs review. -/
def HamiltonianKillsVacuum (Q : QuantumTheory) : Prop :=
  ∃ hmem : (Q.fields.vacuum : Q.State) ∈ Q.fields.hamiltonian.domain,
    Q.fields.hamiltonian.toLinearMap
      ⟨(Q.fields.vacuum : Q.State), hmem⟩ = 0

/-- A concrete Wightman-axiom witness proves the written H Ω = 0 clause.
This is a logical implication, not an existence proof of such a QFT. -/
theorem hamiltonianKillsVacuum_of_wightman
    (Q : QuantumTheory) (h : WightmanAxioms Q.State Q.fields) :
    HamiltonianKillsVacuum Q :=
  ⟨h.vacuum_mem, h.vacuum_zero⟩

/-- PDF_EXPLICIT (Section 4, printed p.6): the energy spectrum lies in
[0, infinity), and the vacuum has energy zero. The latter is recorded
here as membership of zero in the spectrum, not as a replacement for
the separate required equation HΩ = 0. -/
def HamiltonianSpectralFacts (σ : Set ℝ) : Prop :=
  PositiveEnergy σ ∧ 0 ∈ σ

/-- PDF_EXPLICIT (Section 4, printed p.6): some positive interval
(0, Δ) contains no Hamiltonian spectral point. -/
def PositiveGap (σ : Set ℝ) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∀ E ∈ σ, ¬ (0 < E ∧ E < Δ)

/-- PDF_EXPLICIT: the mass is the supremum of admissible positive gaps
and must be finite, so the set must be nonempty and bounded above.
The existing HasPositiveFiniteMass makes that precise. -/
def PositiveFiniteMass (σ : Set ℝ) : Prop :=
  HasPositiveFiniteMass σ

theorem positiveGap_iff (σ : Set ℝ) :
    PositiveGap σ ↔ ∃ Δ, IsMassGap σ Δ := Iff.rfl

theorem positiveFiniteMass_iff (σ : Set ℝ) :
    PositiveFiniteMass σ ↔
      PositiveGap σ ∧ BddAbove (admissibleGaps σ) := Iff.rfl

/-- PDF_EXPLICIT (Section 4 theorem, printed p.6): the quantifier is
"for any compact simple gauge group G".
This takes a property P only to transcribe the LOGICAL BINDER.
P is **not** an accepted definition of quantum Yang--Mills and can
never be selected by a proof submitter for Clay certification. -/
def ForEveryCompactSimpleGroup
    (P : CompactSimpleGaugeGroup.{u} → Prop) : Prop :=
  ∀ G : CompactSimpleGaugeGroup.{u}, P G

theorem forEveryCompactSimpleGroup_iff
    (P : CompactSimpleGaugeGroup.{u} → Prop) :
    ForEveryCompactSimpleGroup P ↔
      ∀ G : CompactSimpleGaugeGroup.{u}, P G := Iff.rfl

/-- An explicit *spectral sub-clause*, NOT a theory-existence target.
The written statement also demands a genuine nontrivial Yang--Mills
quantum field theory with its own Hamiltonian and local operators. -/
def DirectSpectralClauses (σ : Set ℝ) : Prop :=
  HamiltonianSpectralFacts σ ∧ PositiveFiniteMass σ

end YangMills.PDFLiteral
