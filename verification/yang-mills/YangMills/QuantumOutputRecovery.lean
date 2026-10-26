import YangMills.QuantumObservableLift

/-!
# Output recovery through the same quantum observable dictionary

After pairing the actual generated monomial OPE coefficients with a relative
configuration test, their output vector acts on the same W insertion fields.
Its physical projection uses corrected cocycle lifts on BOTH sides; classical
invariant polynomials are not their own duals. A permitted remainder is the
actual unregulated generated quantum ST image of finite ghost-number -1
primitives. This is a conditional relation, not a construction or uniqueness
proof of that projection, and does not supply missing contact Ward identities.
-/
noncomputable section
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

abbrev BigradedMonomialVector (G : CompactSimpleGaugeGroup) :=
  ℕ → ℕ → LocalMonomial G → ℂ

/-- Full generated raw output vector evaluated on same-engine physical
insertion distributions, with exact coupling/loop Cauchy convolution. -/
def rawOutputDistribution (W : WardContinuumData G) (D : ℕ)
    (vector : BigradedMonomialVector G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) : JointMomentumDistribution 1 legs :=
  ∑ m ∈ monomialsBelow G D, ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
    vector a.val b.val m • W.physical .single (order - a.val) (loop - b.val)
      (fun _ : Fin 1 => m) legs

/-- Physical outgoing insertions use the corrected dictionary; the same
finiteInsertion operation must be used to form incoming regulated products. -/
def liftedOutputDistribution {n : ℕ} (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (labels : Fin n → InvariantInsertionLabel G)
    (coefficients : ℕ → ℕ → Fin n → ℂ) (order loop : ℕ)
    (legs : List (ExternalLeg G)) : JointMomentumDistribution 1 legs :=
  ∑ i : Fin n, ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
    coefficients a.val b.val i •
      lift.physicalInsertion W (labels i) (order - a.val) (loop - b.val) legs

/-- Primitives are finite and one engineering degree lower than the OPE
output cutoff, with actual ghost-number -1 and odd parity. -/
def outputPrimitiveMonomials (G : CompactSimpleGaugeGroup) (D : ℕ) :
    Finset (LocalMonomial G) := by
  classical
  exact (monomialsBelow G D).filter
    (fun m => m.dimension + 1 < D ∧ m.ghostNumber = -1 ∧ m.parity = true)

/-- Actual Taylor coefficient of the generated physical quantum ST map.
Use only with the coupling-smoothness guard below. -/
def quantumWardCouplingCoefficient (Q : QuantumWardLimit G)
    (order loop : ℕ) (input output : LocalMonomial G) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => Q.coefficient g loop input output) 0

def QuantumWardLimit.CouplingSmooth (Q : QuantumWardLimit G) : Prop :=
  ∀ loop input output, ContDiff ℝ ∞ (fun g : ℝ => Q.coefficient g loop input output)

/-- Q acts on a genuine finite local primitive; it is not a freely chosen
null-output vector or a second, disconnected Ward operator. -/
def quantumExactOutputVector (Q : QuantumWardLimit G) (D : ℕ)
    (primitive : BigradedMonomialVector G) : BigradedMonomialVector G :=
  fun order loop output => ∑ input ∈ outputPrimitiveMonomials G D,
    ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
      primitive a.val b.val input *
        quantumWardCouplingCoefficient Q (order - a.val) (loop - b.val) input output

/-- Witness data for the fixed regulated-BV anomaly boundary problem of
these very L insertions and their own empty-list background. The proof field
is the explicit source equation bundle, not an unspecified physical predicate. -/
structure SameTheoryWardTransportData {B : InvariantForm G} (e : ColorFrame B)
    (L : ℝ → InsertedFlowFamily G) where
  actionAnomaly : ℝ → FlowFamily G
  insertionAnomaly : ℝ → LocalMonomial G → Spacetime → FlowFamily G
  coefficient : ℝ → LocalAnomalyCoefficients G
  points : AnomalyNormalizationPoints G
  coefficient_graph_grading : ∀ g loop UV input output,
    coefficient g loop UV input output =
      if input.legs.length ≤ output.legs.length + 2 * loop then
        (g : ℂ) ^ (output.legs.length + 2 * loop - input.legs.length) *
          coefficient 1 loop UV input output
      else 0
  conditions : ∀ g, SameTheoryAnomalyTransport e (L g []) (L g) g
    (actionAnomaly g) (insertionAnomaly g) (coefficient g) points

/-- The generated coefficient-limit differential must agree with the SAME
physical amplitudes on all nonexceptional compact tests, beyond finite
normalization probes. This is the actual single Ward equation to establish. -/
def GeneratedPhysicalSingleWardIdentity (W : WardContinuumData G)
    (Q : QuantumWardLimit G) : Prop :=
  Q.Filtered ∧ Q.CouplingSmooth ∧ ∀ A order loop legs
      (test : JointMomentumTest 1 legs), A.Admissible → HasCompactSupport test →
      NonexceptionalSupport .single test →
    W.physical .wardSingle order loop (fun _ : Fin 1 => A) legs test =
      (∑ output ∈ monomialsBelow G (A.dimension + 2),
        ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
          quantumWardCouplingCoefficient Q a.val b.val A output *
            W.physical .single (order - a.val) (loop - b.val)
              (fun _ : Fin 1 => output) legs test)

/-- Concrete cohomological output equation on every source-admissible
compact external test. The input `generated` must be fixed separately by the
actual regulated OPE extraction/weak limit; this relation cannot choose it.
No claim that the Q-image vanishes in a reconstructed Hilbert space is made.
That conclusion needs the full quantum Ward and physical quotient theorem. -/
def QuantumPhysicalOutputRecovery {n : ℕ} {B : InvariantForm G}
    (e : ColorFrame B) (L : ℝ → InsertedFlowFamily G)
    (transport : SameTheoryWardTransportData e L)
    (lift : QuantumObservableLift G) (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (D : ℕ) (labels : Fin n → InvariantInsertionLabel G)
    (generated : BigradedMonomialVector G) (coefficients : ℕ → ℕ → Fin n → ℂ) : Prop :=
  lift.Compatible e transport.coefficient Q ∧ lift.LimitCompatible L W ∧
  GeneratedPhysicalSingleWardIdentity W Q ∧ RestoredActionWardIdentity W ∧
  Q.Filtered ∧ Q.Nilpotent ∧ Q.CouplingSmooth ∧
  (∀ i, intrinsicEngineeringDimension (labels i) < D) ∧
  (∀ order loop i, order < 2 * loop → coefficients order loop i = 0) ∧
  ∃ primitive : BigradedMonomialVector G,
    (∀ order loop m, primitive order loop m ≠ 0 → m ∈ outputPrimitiveMonomials G D) ∧
    ∀ order loop legs (test : JointMomentumTest 1 legs),
      HasCompactSupport test → NonexceptionalSupport .single test →
      rawOutputDistribution W D generated order loop legs test -
        liftedOutputDistribution lift W labels coefficients order loop legs test =
          rawOutputDistribution W D (quantumExactOutputVector Q D primitive)
            order loop legs test

end YangMills.PerturbativeFlow
