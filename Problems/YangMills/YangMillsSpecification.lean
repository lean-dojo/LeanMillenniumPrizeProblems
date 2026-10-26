import Problems.YangMills.FilteredGeneratedCandidate

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed Yang–Mills existence and mass-gap specification

The proposition below fixes the complete simultaneous properties. It does
not provide their witnesses or an existence proof. Its gauge group, master
action, renormalization flow, corrected observables, OPE and UV predictions,
physical fields, vacuum, stress tensor and Hamiltonian are tied together by
the concrete relations of FilteredGeneratedCandidate.

The source interpretation and presentation choices are reviewed separately;
Lean kernel validity does not establish external mathematical acceptance.
-/
noncomputable section
namespace YangMills
universe u

/-- For EVERY compact connected simple Lie gauge group, a four-dimensional
pure Yang–Mills QFT with the fixed same-theory renormalized local-observable,
Ward/CS, all-order UV/OPE and stress properties, and a positive finite gap of
its actual physical time-translation Hamiltonian. No existence proof is
assumed or supplied by this definition. -/
def YangMillsExistenceAndMassGap : Prop :=
  ∀ G : CompactSimpleGaugeGroup.{u}, Nonempty (FilteredGeneratedCandidate G)

end YangMills
