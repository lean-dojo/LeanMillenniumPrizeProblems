import Problems.YangMills.QuantumOutputRecovery
import Problems.YangMills.RegulatedWardInsertion
import Problems.YangMills.StressSymbols

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Same-dictionary quantum stress normalization

Canonical fields cancel the source 1/g^2 before differentiation at g=0.
The tree symbol is fixed; quantum corrections are same-Q local cocycles.
Physical source-label mixing may have a pole of order two: its REGULAR
numerator is used throughout, and the equation is multiplied by g^2.
There is no all-order trace-zero condition and no existence assertion.
-/
noncomputable section
open scoped ContDiff
set_option maxHeartbeats 1200000
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Convert an actual potential polynomial into the same fixed BV density.
Each coefficient, coupling power and potential jet comes from P itself. -/
def potentialDensity (P : PotentialPolynomial G) (g : ℝ) : FullBV.JetAlgebra G :=
  FullBV.densityOfVertices g (P.support.toList.map fun m =>
    { coefficient := ((P.coeff m : ℝ) : ℂ), couplingOrder := m (.inl ()),
      legs := (potentialMonomialLegs m).map fun k => ⟨.inl k.field, k.derivatives⟩ })

/-- Contravariant Minkowski LABEL symbol. Euclidean amplitudes are continued
with the existing label Wick rotation; this does not assert Euclidean
conservation of the unrotated (+---) component array. -/
def canonicalStressDensity {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (mu nu : Fin 4) : FullBV.JetAlgebra G :=
  potentialDensity (canonicalStressPolynomial e mu nu) g

/-- Finite normalized local coefficients of an actual BV polynomial. -/
def normalizedDensityVector (P : FullBV.JetAlgebra G) (D : ℕ) :
    LocalMonomial G →₀ ℂ := by
  classical
  exact Finsupp.onFinset (monomialsBelow G D)
    (fun m => if m ∈ monomialsBelow G D then densityMonomialCoefficient P m else 0)
    (by intro m hm; by_contra hn; exact hm (by simp [hn]))

/-- Only dimension <=4 can occur in the fixed stress tree symbol. The
weighted-degree reconstruction of this fact is supporting proof work. -/
def canonicalStressVector {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (mu nu : Fin 4) : LocalMonomial G →₀ ℂ :=
  normalizedDensityVector (canonicalStressDensity e g mu nu) 5

structure QuantumStressRepresentative (G : CompactSimpleGaugeGroup) where
  coefficient : ℝ → Fin 4 → Fin 4 → ℕ → ℝ → LocalMonomial G →₀ ℂ
  physicalCoefficient : ℝ → Fin 4 → Fin 4 → ℕ → LocalMonomial G →₀ ℂ

/-- Insert the genuine local representative through the same L family. -/
def QuantumStressRepresentative.finiteInsertion (stress : QuantumStressRepresentative G)
    (L : InsertedFlowFamily G) (g : ℝ) (mu nu : Fin 4) (x : Spacetime) : FlowFamily G :=
  fun loop Λ UV legs q => ∑ l : Fin (loop + 1),
    (stress.coefficient g mu nu l.val UV).sum fun m c =>
      c * L [⟨m, x⟩] (loop - l.val) Λ UV legs q

/-- Corrected stress coefficients act on the same physical single-insertion
fields, with the exact coupling/loop Cauchy products. -/
def QuantumStressRepresentative.continuumInsertion (stress : QuantumStressRepresentative G)
    (W : WardContinuumData G) (mu nu : Fin 4) (order loop : ℕ)
    (Λ : Option ℝ) (legs : List (ExternalLeg G)) : JointMomentumDistribution 1 legs :=
  ∑ m ∈ monomialsBelow G 5, ∑ a : Fin (order + 1), ∑ l : Fin (loop + 1),
    (((Nat.factorial a.val : ℂ)⁻¹) * iteratedDeriv a.val
      (fun g : ℝ => stress.physicalCoefficient g mu nu l.val m) 0) •
      (match Λ with
      | none => W.physical .single (order - a.val) (loop - l.val) (fun _ : Fin 1 => m) legs
      | some scale => W.ultraviolet .single (order - a.val) (loop - l.val) scale
          (fun _ : Fin 1 => m) legs)

def QuantumStressRepresentative.finiteIntegrand (stress : QuantumStressRepresentative G)
    (L : ℝ → InsertedFlowFamily G) (mu nu : Fin 4) (order loop : ℕ)
    (Λ UV : ℝ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (xq : (Fin 1 → Spacetime) × (Fin legs.length → Spacetime)) : ℂ :=
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    stress.finiteInsertion (L g) g mu nu (xq.1 0) loop Λ UV legs xq.2) 0) * test xq

/-- Weak stress transport must be proved on actual tests. Convergence of the
local coefficients alone cannot exchange g derivatives with UV/IR limits. -/
structure QuantumStressRepresentative.LimitCompatible (stress : QuantumStressRepresentative G)
    (L : ℝ → InsertedFlowFamily G) (W : WardContinuumData G) : Prop where
  smooth : ∀ mu nu x loop Λ UV legs, 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (fun z : ℝ × (Fin legs.length → Spacetime) =>
      stress.finiteInsertion (L z.1) z.1 mu nu x loop Λ UV legs z.2)
  integrable : ∀ mu nu order loop Λ UV legs (test : JointMomentumTest 1 legs),
    0 < Λ → Λ ≤ UV → HasCompactSupport test →
    MeasureTheory.Integrable (stress.finiteIntegrand L mu nu order loop Λ UV legs test)
  ultraviolet_limit : ∀ mu nu order loop Λ legs (test : JointMomentumTest 1 legs),
    0 < Λ → HasCompactSupport test →
    Filter.Tendsto (fun UV : ℝ => ∫ xq,
      stress.finiteIntegrand L mu nu order loop Λ UV legs test xq)
      Filter.atTop (nhds (stress.continuumInsertion W mu nu order loop (some Λ) legs test))
  infrared_limit : ∀ mu nu order loop legs (test : JointMomentumTest 1 legs),
    HasCompactSupport test → NonexceptionalSupport .single test →
    Filter.Tendsto (fun Λ : ℝ => stress.continuumInsertion W mu nu order loop (some Λ) legs test)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (stress.continuumInsertion W mu nu order loop none legs test))

/-- Fixed normalized polynomial represented by a finite coefficient vector. -/
def densityOfMonomialVector (v : LocalMonomial G →₀ ℂ) : FullBV.JetAlgebra G :=
  v.sum fun m c => c • normalizedMonomialDensity m

/-- The graph exponent is n_m+2l-2, with a guard BEFORE natural subtraction.
In particular the canonical tree kinetic stress has g^0, not g^2. -/
def StressGraphGrading (c : ℝ → Fin 4 → Fin 4 → ℕ → LocalMonomial G → ℂ) : Prop :=
  ∀ g mu nu loop m, c g mu nu loop m =
    if 2 ≤ m.legs.length + 2 * loop then
      (g : ℂ) ^ (m.legs.length + 2 * loop - 2) * c 1 mu nu loop m
    else 0

structure QuantumStressRepresentative.Compatible {B : InvariantForm G}
    (e : ColorFrame B) (Q : QuantumWardLimit G)
    (stress : QuantumStressRepresentative G) : Prop where
  ward_filtered : Q.Filtered
  tree_reconstruction : ∀ g mu nu,
    densityOfMonomialVector (canonicalStressVector e g mu nu) = canonicalStressDensity e g mu nu
  finite_symmetry : ∀ g mu nu loop UV,
    stress.coefficient g mu nu loop UV = stress.coefficient g nu mu loop UV
  physical_symmetry : ∀ g mu nu loop,
    stress.physicalCoefficient g mu nu loop = stress.physicalCoefficient g nu mu loop
  tree : ∀ g mu nu UV, 0 < UV →
    stress.coefficient g mu nu 0 UV = canonicalStressVector e g mu nu
  finite_support : ∀ g mu nu loop UV m, 0 < UV →
    stress.coefficient g mu nu loop UV m ≠ 0 →
    m.Admissible ∧ m.dimension ≤ 4 ∧ m.ghostNumber = 0 ∧ m.parity = false
  physical_support : ∀ g mu nu loop m,
    stress.physicalCoefficient g mu nu loop m ≠ 0 →
    m.Admissible ∧ m.dimension ≤ 4 ∧ m.ghostNumber = 0 ∧ m.parity = false
  finite_graph : ∀ UV, 0 < UV → StressGraphGrading
    (fun g mu nu loop m => stress.coefficient g mu nu loop UV m)
  physical_graph : StressGraphGrading
    (fun g mu nu loop m => stress.physicalCoefficient g mu nu loop m)
  finite_smooth : ∀ mu nu loop UV m, 0 < UV →
    ContDiff ℝ ∞ (fun g : ℝ => stress.coefficient g mu nu loop UV m)
  physical_smooth : ∀ mu nu loop m,
    ContDiff ℝ ∞ (fun g : ℝ => stress.physicalCoefficient g mu nu loop m)
  coefficient_limit : ∀ g mu nu loop m,
    Filter.Tendsto (fun UV : ℝ => stress.coefficient g mu nu loop UV m) Filter.atTop
      (nhds (stress.physicalCoefficient g mu nu loop m))
  cocycle : ∀ g mu nu loop output, output.Admissible → output.dimension ≤ 5 →
    (∑ l : Fin (loop + 1), (stress.physicalCoefficient g mu nu l.val).sum
      (fun input c => c * Q.coefficient g (loop - l.val) input output)) = 0

/-- A finite source-invariant dictionary. `regular` is the regular numerator
of the formal Laurent mixing; the physical stress has at most a g^-2 pole
in SOURCE labels, canceled by their canonical-field powers. -/
structure StressSourceDictionary (G : CompactSimpleGaugeGroup) where
  count : ℕ
  label : Fin count → InvariantInsertionLabel G
  regular : ℝ → Fin 4 → Fin 4 → ℕ → Fin count → ℝ
  exactRegular : ℝ → Fin 4 → Fin 4 → Fin count → ℝ

/-- Loopwise finite regularized dictionary. Multiplying by g^2 avoids any
use of the totalized inverse at the perturbative expansion point. This
permits quantum scalar mixing, including a trace anomaly. -/
structure StressSourceDictionary.Compatible
    (dict : StressSourceDictionary G) (lift : QuantumObservableLift G)
    (stress : QuantumStressRepresentative G) : Prop where
  degree : ∀ i, intrinsicEngineeringDimension (dict.label i) ≤ 4
  graph : ∀ g mu nu loop i,
    dict.regular g mu nu loop i = g ^ (2 * loop) * dict.regular 1 mu nu loop i
  smooth : ∀ mu nu loop i,
    ContDiff ℝ ∞ (fun g : ℝ => dict.regular g mu nu loop i)
  exact_smooth : ∀ mu nu i,
    ContDiff ℝ ∞ (fun g : ℝ => dict.exactRegular g mu nu i)
  exact_jet : ∀ order mu nu i,
    (Nat.factorial order : ℝ)⁻¹ * iteratedDeriv order
      (fun g : ℝ => dict.exactRegular g mu nu i) 0 =
      if order % 2 = 0 then dict.regular 1 mu nu (order / 2) i else 0
  finite_binding : ∀ (g : ℝ) mu nu loop UV m, 0 < UV →
    (g : ℂ) ^ 2 * stress.coefficient g mu nu loop UV m =
      ∑ i : Fin dict.count, ∑ l : Fin (loop + 1),
        (dict.regular g mu nu l.val i : ℂ) *
          lift.coefficient g (dict.label i) (loop - l.val) UV m
  physical_binding : ∀ (g : ℝ) mu nu loop m,
    (g : ℂ) ^ 2 * stress.physicalCoefficient g mu nu loop m =
      ∑ i : Fin dict.count, ∑ l : Fin (loop + 1),
        (dict.regular g mu nu l.val i : ℂ) *
          lift.physicalCoefficient g (dict.label i) (loop - l.val) m

/-- The actual physical stress uses the same C dictionary at its actual
positive coupling. This is not equality with a fixed traceless classical
label: the coefficients have their quantum jets and may mix F^2. -/
def StressSourceDictionary.PhysicalBinding
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {QFT : WightmanData H} {C : RenormalizedCompositeMap QFT G}
    (dict : StressSourceDictionary G) (T : StressTensorData QFT G C) : Prop :=
  ∀ mu nu,
    (T.coupling.val ^ 2) • T.label mu nu =
      ∑ i : Fin dict.count, dict.exactRegular T.coupling.val mu nu i • dict.label i

/-- A genuine same-Q local exact change, plus divergence of a local
antisymmetric improvement current. Neither term is declared physically null
here: Q-exact nullness needs the physical cohomology map; improvements change
the stress field and must be carried into its physical dictionary. -/
def StressRepresentativeEquivalent (Q : QuantumWardLimit G) (g : ℝ)
    (left right : QuantumStressRepresentative G) : Prop :=
  ∃ primitive : Fin 4 → Fin 4 → ℕ → LocalMonomial G →₀ ℂ,
  ∃ improvement : Fin 4 → Fin 4 → Fin 4 → ℕ → LocalMonomial G →₀ ℂ,
    (∀ mu nu loop m, primitive mu nu loop m ≠ 0 →
      m.Admissible ∧ m.dimension ≤ 3 ∧ m.ghostNumber = -1 ∧ m.parity = true) ∧
    (∀ rho mu nu loop m, improvement rho mu nu loop m ≠ 0 →
      m.Admissible ∧ m.dimension ≤ 3 ∧ m.ghostNumber = 0 ∧ m.parity = false) ∧
    (∀ rho mu nu loop, improvement rho mu nu loop = -improvement mu rho nu loop) ∧
    ∀ mu nu loop output, output.Admissible → output.dimension ≤ 4 →
      left.physicalCoefficient g mu nu loop output -
        right.physicalCoefficient g mu nu loop output =
      (∑ l : Fin (loop + 1), (primitive mu nu l.val).sum fun input c =>
        c * Q.coefficient g (loop - l.val) input output) +
      ∑ rho : Fin 4, densityMonomialCoefficient
        (FullBV.totalDerivative rho
          (densityOfMonomialVector (improvement rho mu nu loop))) output


/-- All stress links needed at admission, on these same L/F/W/Q data.
Physical BRST null-state identification and the existing translation/trace
conditions remain separate obligations of the encompassing YM sector. -/
def GeneratedStressNormalization {B : InvariantForm G} (e : ColorFrame B)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G)
    (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (transport : SameTheoryWardTransportData e L)
    (lift : QuantumObservableLift G) (stress : QuantumStressRepresentative G)
    (dict : StressSourceDictionary G)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {QFT : WightmanData H} {C : RenormalizedCompositeMap QFT G}
    (T : StressTensorData QFT G C) : Prop :=
  W.BulkCompatible L F ∧
  lift.Compatible e transport.coefficient Q ∧ lift.LimitCompatible L W ∧
  GeneratedPhysicalSingleWardIdentity W Q ∧ Q.Nilpotent ∧
  stress.Compatible e Q ∧ stress.LimitCompatible L W ∧
  dict.Compatible lift stress ∧ dict.PhysicalBinding T ∧
  T.traceForm = B ∧ T.Compatible

theorem StressGraphGrading.no_low_tree
    {c : ℝ → Fin 4 → Fin 4 → ℕ → LocalMonomial G → ℂ}
    (h : StressGraphGrading c) (g : ℝ) (mu nu : Fin 4) (m : LocalMonomial G)
    (hm : m.legs.length < 2) : c g mu nu 0 m = 0 := by
  rw [h]
  simp only [mul_zero, add_zero]
  rw [if_neg (by omega)]

end YangMills.PerturbativeFlow
