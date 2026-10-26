import Problems.YangMills.Statement
import Problems.YangMills.PeriodicLattice4

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Group quantifier alone is NOT Yang–Mills identification

The Clay statement is universally quantified over compact simple gauge
groups. The formula below makes that quantifier explicit but does not couple
G to any gauge-invariant quantum operator. The theorem proves that exactly
this construction is too weak: a *single* unrelated gapped QFT may be reused
for every group. No full-Clay certification must accept this statement.
-/

noncomputable section

namespace YangMills

universe u

/-- Necessary QFT-only shadow of the PDF's groupwise existence theorem.
This is intentionally **not** called Yang–Mills existence. -/
def GroupwiseQFTExistenceAndMassGap : Prop :=
  ∀ _G : CompactSimpleGaugeGroup.{u},
    ∃ Q : QuantumTheory, GappedWightmanTheory Q.State Q.fields

/-- Demonstrates the dangerous weakening: quantifying a group that the
quantum theory never uses gives nothing beyond one gapped QFT, even before
Yang–Mills identification, nontriviality or UV/OPE conditions are imposed. -/
theorem qft_exists_implies_groupwise_qft
    (h : QFTExistenceAndMassGap) :
    GroupwiseQFTExistenceAndMassGap := by
  intro _G
  exact h


/-- Adding a genuine G-dependent lattice *check* to a theorem, without
requiring that Q's quantum fields represent that lattice theory, is still
insufficient. This is an intentionally inadequate necessary shadow. -/
def GroupwiseQFTWithUnlinkedLatticeChecks : Prop :=
  ∀ G : CompactSimpleGaugeGroup.{u},
    ∃ Q : QuantumTheory,
      GappedWightmanTheory Q.State Q.fields ∧
      (∀ (n : ℕ) (χ : ConjClasses G.Carrier → ℝ)
          (h : PeriodicFourVertex n → G.Carrier)
          (links : GaugeLinks (PeriodicFourVertex n) G),
        periodicFourClassAction n G χ (gaugeTransform G h links) =
          periodicFourClassAction n G χ links)

/-- Kernel-checkable negative control: QFT existence alone also implies
every group-dependent *but unlinked* finite-gauge consistency test.
Therefore proving those two ingredients side-by-side never identifies
the quantum theory with Yang--Mills for G. -/
theorem qft_exists_implies_unlinked_group_checks
    (h : QFTExistenceAndMassGap) :
    GroupwiseQFTWithUnlinkedLatticeChecks := by
  obtain ⟨Q, hQ⟩ := h
  intro G
  refine ⟨Q, hQ, ?_⟩
  intro n χ gauges links
  exact periodicFourClassAction_gauge_invariant n G χ gauges links

end YangMills
