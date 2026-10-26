import YangMills.CompositeFields
import YangMills.InsertionWardTransport

/-!
# Same-prescription quantum cocycle lifts of classical invariant labels

The raw insertion of a classical invariant polynomial need not be a cocycle
of the generated quantum ST differential. This dictionary allows its actual
finite local hbar corrections, with fixed tree normalization, intrinsic
engineering filtration, and closure under s+A1 from the SAME anomaly flow.
It does not assert that such a dictionary exists. Contact Ward restoration
and the physical null-state/cohomology theorem remain to be established.
-/
noncomputable section
open scoped ContDiff
open Filter MeasureTheory
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

abbrev InvariantInsertionLabel (G : CompactSimpleGaugeGroup) :=
  CurvatureJetPolynomial.invariantAlgebra G

/-- Finite-cutoff quantum local representatives, at fixed real coupling g.
The finite support is actual monomial support, not a list of unrelated fields. -/
structure QuantumObservableLift (G : CompactSimpleGaugeGroup) where
  coefficient : ℝ → InvariantInsertionLabel G → ℕ → ℝ → LocalMonomial G →₀ ℂ
  physicalCoefficient : ℝ → InvariantInsertionLabel G → ℕ → LocalMonomial G →₀ ℂ

/-- Insert the corrected local representative through these very L fields.
At each loop order the exact finite hbar Cauchy sum is used. -/
def QuantumObservableLift.finiteInsertion (lift : QuantumObservableLift G)
    (L : InsertedFlowFamily G) (g : ℝ) (p : InvariantInsertionLabel G) (x : Spacetime) : FlowFamily G :=
  fun loop Λ UV legs q => ∑ l : Fin (loop + 1),
    (lift.coefficient g p l.val UV).sum (fun m c =>
      c * L [⟨m, x⟩] (loop - l.val) Λ UV legs q)

/-- Continuum insertion of the SAME corrected representative, using the
actual UV limits of its coefficients and the single-insertion distributions.
Its identification with the weak limit of finiteInsertion is a required
limit-interchange/continuity theorem, not supplied by this definition. -/
def QuantumObservableLift.physicalInsertion (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (p : InvariantInsertionLabel G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) : JointMomentumDistribution 1 legs :=
  ∑ m ∈ monomialsBelow G (intrinsicEngineeringDimension p + 1),
    ∑ a : Fin (order + 1), ∑ l : Fin (loop + 1),
      (((Nat.factorial a.val : ℂ)⁻¹) * iteratedDeriv a.val
        (fun g : ℝ => lift.physicalCoefficient g p l.val m) 0) •
          W.physical .single (order - a.val) (loop - l.val) (fun _ : Fin 1 => m) legs

/-- Two labels which agree on smooth connections represent the SAME
quantum class, while allowing legitimate exact changes of local lift. The
primitive degree is fixed intrinsically by the labels. At degree zero no
primitive exists, so a classically zero label cannot acquire a fake unit.
The primitive's own coupling grading prevents an infinite loop ambiguity at
fixed coupling order. No injectivity of classical labels is asserted. -/
def SameQuantumLabelClass (Q : QuantumWardLimit G) (lift : QuantumObservableLift G)
    (p q : InvariantInsertionLabel G) : Prop :=
  ∃ primitive : ℝ → ℕ → LocalMonomial G →₀ ℂ,
    (∀ g loop m, primitive g loop m ≠ 0 →
      m.Admissible ∧ m.dimension + 1 ≤
        max (intrinsicEngineeringDimension p) (intrinsicEngineeringDimension q) ∧
        m.ghostNumber = -1 ∧ m.parity = true) ∧
    (∀ loop m, ContDiff ℝ ∞ (fun g : ℝ => primitive g loop m)) ∧
    (∀ g loop m, primitive g loop m =
      (g : ℂ) ^ (m.legs.length + 2 * loop) * primitive 1 loop m) ∧
    ∀ g loop output, output.Admissible → output.dimension ≤
        max (intrinsicEngineeringDimension p) (intrinsicEngineeringDimension q) →
      lift.physicalCoefficient g p loop output - lift.physicalCoefficient g q loop output =
        ∑ l : Fin (loop + 1), (primitive g l.val).sum (fun input c =>
          c * Q.coefficient g (loop - l.val) input output)

/-- In dimension zero there is no lower-degree primitive. Thus identity
respecting quantum lifts cannot turn a classically zero label into a unit
counterterm at higher loop order. -/
theorem SameQuantumLabelClass.dimensionZero_eq {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} {p q : InvariantInsertionLabel G}
    (h : SameQuantumLabelClass Q lift p q)
    (hp : intrinsicEngineeringDimension p = 0) (hq : intrinsicEngineeringDimension q = 0)
    (g : ℝ) (loop : ℕ) (output : LocalMonomial G) (ha : output.Admissible)
    (hd : output.dimension = 0) :
    lift.physicalCoefficient g p loop output = lift.physicalCoefficient g q loop output := by
  rcases h with ⟨primitive, support, _smooth, _grading, equation⟩
  have primitive_zero : ∀ g l, primitive g l = 0 := by
    intro g l
    ext m
    by_contra hn
    have bound := (support g l m hn).2.1
    simp only [hp, hq, max_self] at bound
    omega
  have equality := equation g loop output ha (by simp [hp, hq, hd])
  apply sub_eq_zero.mp
  simpa [primitive_zero] using equality

/-- Every entry is constrained by actual same-action equations. In
particular the quantum correction cannot substitute another classical label,
and a chosen overly large engineering cutoff cannot weaken the closure test.
The equations hold for the full real coupling family, with smoothness
guards before any actual coupling derivative is taken. -/
structure QuantumObservableLift.Compatible {B : InvariantForm G} (e : ColorFrame B)
    (anomalyCoeff : ℝ → LocalAnomalyCoefficients G) (Q : QuantumWardLimit G)
    (lift : QuantumObservableLift G) : Prop where
  same_ward_limit : Q.Compatible e anomalyCoeff
  ward_filtered : Q.Filtered
  relations : ∀ (p q : InvariantInsertionLabel G), CurvatureJetPolynomial.sameOnConnections
      (p : CurvatureJetPolynomial G) (q : CurvatureJetPolynomial G) →
    SameQuantumLabelClass Q lift p q
  ward_graph_grading : ∀ g loop input output,
    Q.coefficient g loop input output =
      if input.legs.length ≤ output.legs.length + 2 * loop then
        (g : ℂ) ^ (output.legs.length + 2 * loop - input.legs.length) *
          Q.coefficient 1 loop input output
      else 0
  finite_graph_grading : ∀ g p loop UV m,
    lift.coefficient g p loop UV m =
      (g : ℂ) ^ (m.legs.length + 2 * loop) * lift.coefficient 1 p loop UV m
  physical_graph_grading : ∀ g p loop m,
    lift.physicalCoefficient g p loop m =
      (g : ℂ) ^ (m.legs.length + 2 * loop) * lift.physicalCoefficient 1 p loop m
  linear_add : ∀ g p q loop UV,
    lift.coefficient g (p + q) loop UV =
      lift.coefficient g p loop UV + lift.coefficient g q loop UV
  linear_smul : ∀ g (c : ℝ) p loop UV,
    lift.coefficient g (c • p) loop UV = (c : ℂ) • lift.coefficient g p loop UV
  unit_corrections : ∀ g loop UV, 0 < loop → lift.coefficient g 1 loop UV = 0
  tree : ∀ g p UV, 0 < UV →
    lift.coefficient g p 0 UV = normalizedObservableExpansion e (p : CurvatureJetPolynomial G) g
  finite_support : ∀ g p loop UV m, 0 < UV → lift.coefficient g p loop UV m ≠ 0 →
    m.Admissible ∧ m.dimension ≤ intrinsicEngineeringDimension p ∧
      m.ghostNumber = 0 ∧ m.parity = false
  physical_support : ∀ g p loop m, lift.physicalCoefficient g p loop m ≠ 0 →
    m.Admissible ∧ m.dimension ≤ intrinsicEngineeringDimension p ∧
      m.ghostNumber = 0 ∧ m.parity = false
  coefficient_limit : ∀ g p loop m,
    Tendsto (fun UV : ℝ => lift.coefficient g p loop UV m) atTop
      (nhds (lift.physicalCoefficient g p loop m))
  finite_coupling_smooth : ∀ p loop UV m, 0 < UV →
    ContDiff ℝ ∞ (fun g : ℝ => lift.coefficient g p loop UV m)
  physical_coupling_smooth : ∀ p loop m,
    ContDiff ℝ ∞ (fun g : ℝ => lift.physicalCoefficient g p loop m)
  cocycle : ∀ g p loop output, output.Admissible →
    output.dimension ≤ intrinsicEngineeringDimension p + 1 →
    (∑ l : Fin (loop + 1), (lift.physicalCoefficient g p l.val).sum (fun input c =>
      c * Q.coefficient g (loop - l.val) input output)) = 0

/-- Positive-IR UV limit of the corrected insertion, using the SAME
coefficient limits and the SAME ultraviolet single-insertion distributions. -/
def QuantumObservableLift.ultravioletInsertion (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (p : InvariantInsertionLabel G) (order loop : ℕ)
    (Λ : ℝ) (legs : List (ExternalLeg G)) : JointMomentumDistribution 1 legs :=
  ∑ m ∈ monomialsBelow G (intrinsicEngineeringDimension p + 1),
    ∑ a : Fin (order + 1), ∑ l : Fin (loop + 1),
      (((Nat.factorial a.val : ℂ)⁻¹) * iteratedDeriv a.val
        (fun g : ℝ => lift.physicalCoefficient g p l.val m) 0) •
          W.ultraviolet .single (order - a.val) (loop - l.val) Λ
            (fun _ : Fin 1 => m) legs

def QuantumObservableLift.finiteIntegrand (lift : QuantumObservableLift G)
    (L : ℝ → InsertedFlowFamily G) (p : InvariantInsertionLabel G) (order loop : ℕ)
    (Λ UV : ℝ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (xq : (Fin 1 → Spacetime) × (Fin legs.length → Spacetime)) : ℂ :=
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    lift.finiteInsertion (L g) g p (xq.1 0) loop Λ UV legs xq.2) 0) * test xq

/-- Exact weak UV-then-IR transport of the corrected dictionary. Coefficient
convergence alone cannot justify interchanging g derivatives and limits;
these equations impose the needed identification on actual compact tests.
They preserve the source nonexceptional restriction at the IR endpoint. -/
structure QuantumObservableLift.LimitCompatible (lift : QuantumObservableLift G)
    (L : ℝ → InsertedFlowFamily G) (W : WardContinuumData G) : Prop where
  coupling_momentum_smooth : ∀ p x loop Λ UV, 0 < Λ → Λ ≤ UV → ∀ legs,
    ContDiff ℝ ∞ (fun z : ℝ × (Fin legs.length → Spacetime) =>
      lift.finiteInsertion (L z.1) z.1 p x loop Λ UV legs z.2)
  finite_integrable : ∀ p order loop Λ UV legs (test : JointMomentumTest 1 legs),
    0 < Λ → Λ ≤ UV → HasCompactSupport test →
      MeasureTheory.Integrable (lift.finiteIntegrand L p order loop Λ UV legs test)
  ultraviolet_limit : ∀ p order loop Λ legs (test : JointMomentumTest 1 legs),
    0 < Λ → HasCompactSupport test →
    Tendsto (fun UV : ℝ => ∫ xq, lift.finiteIntegrand L p order loop Λ UV legs test xq)
      atTop (nhds (lift.ultravioletInsertion W p order loop Λ legs test))
  infrared_limit : ∀ p order loop legs (test : JointMomentumTest 1 legs),
    HasCompactSupport test → NonexceptionalSupport .single test →
    Tendsto (fun Λ : ℝ => lift.ultravioletInsertion W p order loop Λ legs test)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (lift.physicalInsertion W p order loop legs test))

/-- Quantum-exact changes use actual ghost-number -1 local primitives
of degree one below the physical label, with the SAME generated differential.
This is a local coefficient equation and not an assertion that exact operators
are null in a separately reconstructed physical Hilbert space. -/
def SameQuantumCohomologyClass (g : ℝ) (Q : QuantumWardLimit G)
    (left right : QuantumObservableLift G) (p : InvariantInsertionLabel G) : Prop :=
  ∃ primitive : ℕ → LocalMonomial G →₀ ℂ,
    (∀ loop m, primitive loop m ≠ 0 →
      m.Admissible ∧ m.dimension + 1 ≤ intrinsicEngineeringDimension p ∧
        m.ghostNumber = -1 ∧ m.parity = true) ∧
    ∀ loop output, output.Admissible →
      output.dimension ≤ intrinsicEngineeringDimension p →
      left.physicalCoefficient g p loop output - right.physicalCoefficient g p loop output =
        ∑ l : Fin (loop + 1), (primitive l.val).sum (fun input c =>
          c * Q.coefficient g (loop - l.val) input output)

end YangMills.PerturbativeFlow
