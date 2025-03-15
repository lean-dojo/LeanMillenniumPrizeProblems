import Problems.YangMills.Quantum

namespace MillenniumYangMills

open LieGroup MillenniumYangMillsDefs

/-!
# Yang-Mills Existence and Mass Gap Problem

This file formalizes the Millennium Prize problem on the Yang-Mills existence and mass gap. This was the hardest conjecture to formalize for me as I didnt know basically any concepts and had to learn and debug a lot with Claude and LeanSearch and the Mathlib library + watch videos.

The problem asks to prove that:
1. For any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on R⁴
2. This theory has a mass gap Δ > 0 (difference in energy between vacuum and lowest energy state)

In a more simpler term basically 1 is the Existence: For any compact simple gauge group G, there exists a quantum field theory on 4D spacetime that satisfies the axioms of quantum field theory.

In a more simpler term 2 is the Mass Gap: This theory has a "mass gap" - meaning there's a positive minimum energy difference between the vacuum state (lowest energy state) and the first excited state.

The conjecture is significant because Yang-Mills theories form the foundation of the Standard Model in particle physics, but a rigorous mathematical construction has remained elusive.

### The Quantum.lean file contains essential mathematical structures needed to formalize quantum field theory:

1. Spacetime: Defined as Fin 4 → ℝ, representing 4D Minkowski spacetime with points as functions from indices to coordinates.
2. MinkowskiMetric: The metric tensor with signature (+,-,-,-) defining spacetime geometry.
3. CompactSimpleGaugeGroup: Represents gauge groups like SU(2) or SU(3), with properties:
  3.1 Has a Lie group structure
  3.2 Is compact (bounded and closed)
  3.3 Is simple (no non-trivial normal subgroups)
  3.4 Has an associated Lie algebra
4. GaugeField: The connection/gauge potential representing the fundamental field in Yang-Mills theory.
5. FieldStrength: The curvature of the gauge field, analogous to electromagnetic field tensor.
6. SchwartzSpace: Test functions for quantum field theory, representing smooth functions that decay rapidly.
7. OperatorValuedDistribution: Quantum fields as operator-valued distributions on test functions.
8. WightmanAxioms: The fundamental axioms for rigorous quantum field theory:
  8.1 Relativistic invariance: Fields transform correctly under spacetime symmetries
  8.2 Spectral condition: Energy is positive and momentum is in forward light cone
  8.3 Existence of vacuum: Lowest energy state exists and is invariant
  8.4 Cyclicity: Fields acting on vacuum generate the whole state space
  8.5 Locality/causality: Fields at spacelike separation commute
  8.6 OsterwalderSchraderAxioms: Alternative axiomatization connecting to statistical mechanics.
9. QuantumYangMillsTheory: The complete structure bringing together:
  9.1 A Hilbert space of quantum states
  9.2 Field operators satisfying the axioms
  9.3 Hamiltonian (energy operator)
  9.4 Vacuum state
  9.5 Connection to classical Yang-Mills theory
  9.6 TwoPointFunction: The correlation function used to probe particle content and mass gap.

## References
- Jaffe, A., & Witten, E. "Quantum Yang-Mills Theory"
- Streater & Wightman (1964): "PCT, Spin and Statistics, and All That"
- Osterwalder & Schrader (1973, 1975): "Axioms for Euclidean Green's functions"
-/

/-- Mass gap in terms of two-point function decay
The two-point function should decay exponentially with distance, with rate controlled by Δ--/
def HasMassGapViaTwoPoint (G : Type) [CompactSimpleGaugeGroup G]
  (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ -- The mass gap must be positive
  ∃ (C : ℝ), C > 0 ∧ -- There exists some positive constant C
  ∀ (t : ℝ), t > 0 → -- For all positive time separations
    let x : Spacetime := λ i => if i = 0 then t else 0 -- Point at time t, space origin
    let y : Spacetime := λ i => if i = 0 then 0 else 0 -- Point at time 0, space origin
    TwoPointFunction G qft x y ≤ C * Real.exp (-Δ * t) -- Exponential decay with rate Δ

/-- Mass gap in terms of Hamiltonian spectrum
There should be a minimum energy gap between vacuum and excited states--/
def HasMassGapViaSpectrum (G : Type) [CompactSimpleGaugeGroup G]
  (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ -- The mass gap must be positive
  ∀ (state : qft.hilbertSpace), -- For all quantum states
    state ≠ qft.vacuum → -- Except the vacuum state
    sorry -- TODO Inner.inner (qft.hamiltonian state) state -
    --Inner.inner (qft.hamiltonian qft.vacuum) qft.vacuum ≥
    --Δ * Inner.inner state state

/-- The Yang-Mills existence and mass gap theorem statement --/
theorem yang_mills_existence_and_mass_gap (G : Type) [CompactSimpleGaugeGroup G] :
  ∃ (qft : QuantumYangMillsTheory G) (Δ : ℝ), -- There exists a quantum YM theory and positive mass gap
    HasMassGapViaSpectrum G qft Δ ∧ HasMassGapViaTwoPoint G qft Δ := sorry

end MillenniumYangMills
