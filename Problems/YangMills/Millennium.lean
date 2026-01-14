import Problems.YangMills.Quantum

namespace MillenniumYangMills

open LieGroup MillenniumYangMillsDefs

/-!
# Yang-Mills Existence and Mass Gap Problem

This file states the Clay Millennium problem “Yang–Mills existence and mass gap” in Lean, following
the official Clay problem description:
`Problems/YangMills/references/clay/yangmills.pdf`.

The problem asks to prove that for any compact simple gauge group `G`, a non-trivial quantum
Yang–Mills theory exists on `ℝ⁴` and has a mass gap `Δ > 0`.

In the Clay writeup, the Hamiltonian `H` has a **mass gap** `Δ` if it has no spectrum in the
interval `(0, Δ)`.

## References
- Jaffe, A., & Witten, E. "Quantum Yang-Mills Theory"
- Streater & Wightman (1964): "PCT, Spin and Statistics, and All That"
- Osterwalder & Schrader (1973, 1975): "Axioms for Euclidean Green's functions"
-/

/-!
We do not formalize the spectral theory of the Hamiltonian operator here, so we use a standard
“quadratic form” inequality that implies a spectral gap above the vacuum when combined with
self-adjointness/positivity (already part of `WightmanAxioms` in `Problems/YangMills/Quantum.lean`).
-/

/-- A non-trivial theory: the Hilbert space has at least two distinct states. -/
def NontrivialTheory {G : Type} [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) : Prop :=
  Nontrivial qft.hilbertSpace

/--
Mass gap (Lean-level stand-in for “no spectrum in (0,Δ)”).

This is phrased in terms of the Hamiltonian from the Wightman axioms:
`H := qft.wightman.hamiltonian` and vacuum `Ω := qft.wightman.vacuum`.
-/
def HasMassGap (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  Δ > 0 ∧
    ∀ ψ : qft.hilbertSpace,
      inner ℝ ψ qft.wightman.vacuum = 0 →
        Δ * inner ℝ ψ ψ ≤ inner ℝ (qft.wightman.hamiltonian ψ) ψ

/--
Mass gap in the form used in the Clay statement: the Hamiltonian has no spectrum in `(0, Δ)`.

Here `spectrum ℝ qft.wightman.hamiltonian` is Mathlib's spectrum of a bounded operator.
-/
def HasMassGapSpectrum (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ Disjoint (spectrum ℝ qft.wightman.hamiltonian) (Set.Ioo 0 Δ)

/--
The “mass” `m` as described in the Clay writeup: the supremum of the admissible spectral gaps.

This is a definition only (no properties are proved here).
-/
noncomputable def Mass (G : Type) [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) : ℝ :=
  sSup {Δ : ℝ | HasMassGapSpectrum G qft Δ}

/--
“Existence” requirements highlighted in the Clay statement.

In this development, these are carried as *data + laws* inside `QuantumYangMillsTheory`:
- Wightman axioms (`qft.wightman`)
- Local-operator correspondence (`qft.localOperators`)
- Short-distance agreement (`qft.shortDistance`)
- Stress tensor (`qft.stressTensor`)
- Operator product expansion (`qft.operatorProductExpansion`)

So the remaining non-vacuity condition we explicitly require is that the theory is non-trivial.
-/
def ClayExistence {G : Type} [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) : Prop :=
  NontrivialTheory qft

/--
The Clay writeup defines the “mass” `m` as the supremum of possible mass gaps and requires `m < ∞`.

We model “finite mass” as a (non-sharp) global upper bound on the gaps witnessed by `HasMassGap`.
-/
def FiniteMass (G : Type) [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, HasMassGap G qft Δ → Δ ≤ m

/--
Finite mass condition corresponding to the Clay definition of “mass” as the supremum of gaps.

We record this as the existence of an upper bound on all spectral gaps.
-/
def FiniteMassSpectrum (G : Type) [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) : Prop :=
  ∃ m : ℝ, m > 0 ∧ ∀ Δ : ℝ, HasMassGapSpectrum G qft Δ → Δ ≤ m

/--
Clustering estimate from the Clay writeup (equation (2), stated as a `Prop`).

We model `O(⃗x) = U(⃗x) O U(⃗x)⁻¹` using the spatial translation representation
`U := qft.wightman.spaceTranslation`.
-/
def ClusteringProperty (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → C < Δ →
    ∀ O : LinearOperator qft.hilbertSpace,
      IsCentered qft.wightman.vacuum O →
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ x y : Space,
            R ≤ dist x y →
              |vacuumExpectation qft.wightman.vacuum
                    ((localOperatorAt qft.wightman.spaceTranslation x O).comp
                      (localOperatorAt qft.wightman.spaceTranslation y O))| ≤
                Real.exp (-C * dist x y)

/--
The Clay writeup notes that a mass gap implies clustering; we record this as a statement.
-/
def MassGapImpliesClustering (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) : Prop :=
  ∀ Δ : ℝ, HasMassGapSpectrum G qft Δ → ClusteringProperty G qft Δ

/-- # The Yang–Mills existence and mass gap problem statement. -/
def YangMillsExistenceAndMassGap (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (qft : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence qft ∧ HasMassGapSpectrum G qft Δ ∧ FiniteMassSpectrum G qft

end MillenniumYangMills
