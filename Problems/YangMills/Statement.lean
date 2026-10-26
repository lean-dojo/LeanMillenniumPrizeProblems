import Problems.YangMills.GaugeGroup
import Problems.YangMills.QFT.Wightman

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Precisely checked QFT-and-gap target — not yet the full Yang–Mills target

Jaffe–Witten §§3–4:
https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf

The target below checks the QFT-and-gap portion against fixed definitions.
It is only a necessary portion of the Millennium problem: it does not identify
a QFT with Yang–Mills for a given gauge group. An unrelated massive free field is not excluded by
this necessary target; no such model is constructed here. The
gauge-observable correspondence, renormalized Yang–Mills identification, and
prescribed ultraviolet/OPE asymptotics still need a precise specification and
implementation. They are NOT represented by free predicates, axioms, or hidden
proof holes here.
-/

noncomputable section
namespace YangMills

/-- A candidate supplies a state space and concrete field/translation data.
Completeness, separability, and the field axioms are obligations below. -/
structure QuantumTheory where
  State : Type
  [normed : NormedAddCommGroup State]
  [innerProduct : InnerProductSpace ℂ State]
  fields : WightmanData State

attribute [instance] QuantumTheory.normed QuantumTheory.innerProduct

/-- A closed target for the QFT-and-gap portion ONLY. There are no predicate
parameters and no hypotheses under which the conclusion is assumed.

Read `∃` as “there exists”. A proof must supply the concrete candidate and
proofs of every fixed Wightman and spectral obligation.

This proposition is deliberately not called Yang–Mills existence. No theorem
of this type, even when fully kernel-checked, certifies the Millennium problem.
-/
def QFTExistenceAndMassGap : Prop :=
  ∃ Q : QuantumTheory, GappedWightmanTheory Q.State Q.fields

end YangMills
