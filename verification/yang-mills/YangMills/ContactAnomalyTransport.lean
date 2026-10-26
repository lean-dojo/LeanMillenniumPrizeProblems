import YangMills.ContactTaylorProjection
import YangMills.ClassicalPointContact
import YangMills.WardContinuum

/-!
# Same-flow local pair anomaly and its UV boundary transport

FHH (335), (340), (346). Every ordinary delta-derivative channel comes from
an explicit finite Taylor projection of the same regulated BV pair kernel,
minus the same-L insertion of the computed classical point bracket. The
right external translation phase is converted to first-centered normalform
BEFORE summing partitions. A2 evolves by homogeneous insertion flow with
these full UV boundary values. Unlike A1, it is not assigned zero irrelevant
UV data. Existence of its UV/IR limit still needs the full Ward decomposition
and estimates; no such theorem is assumed by these definitions.
-/
noncomputable section
open scoped ContDiff
open Filter
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Actual bare local A2 channel, in the first-centered convention. -/
def bareContactAnomalyChannel (L : InsertedFlowFamily G)
    (A B : LocalMonomial G) (w : ContactDerivativeIndex) (loop : ℕ) (UV : ℝ) :
    OrderedAmplitude G :=
  fun legs q => if w.order + 3 ≤ A.dimension + B.dimension then
    (∑ l : Fin (loop + 1), ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
      centeredContactTaylorCoefficient (barePairBVFourierSplit L A B loop l.val UV legs q s)
        (A.dimension + B.dimension - 3)
        (selectedMomentum legs (complementIndices legs s) q) w) -
      classicalPointContactFlow L A B w 0 loop UV UV legs q
  else 0

abbrev ContactAnomalyCoefficients (G : CompactSimpleGaugeGroup) :=
  ℕ → ℝ → LocalMonomial G → LocalMonomial G → ContactDerivativeIndex → LocalMonomial G → ℂ

/-- Local A2 channels are finite combinations of these SAME insertion fields.
Delta-derivative order consumes engineering degree of the output field. -/
def transportedContactAnomaly (L : InsertedFlowFamily G)
    (coeff : ContactAnomalyCoefficients G) (A B : LocalMonomial G)
    (w : ContactDerivativeIndex) (x : Spacetime) : FlowFamily G :=
  fun loop Λ UV legs q => ∑ C ∈ monomialsBelow G (contactOutputBound A B w + 1),
    ∑ l : Fin (loop + 1), coeff l.val UV A B w C *
      L [⟨C, x⟩] (loop - l.val) Λ UV legs q

/-- The FULL A2 flow retains regulator-suppressed irrelevant UV tails.
Only its continuum local representative has the finite engineering bound. -/
abbrev FullContactAnomaly (G : CompactSimpleGaugeGroup) :=
  LocalMonomial G → LocalMonomial G → ContactDerivativeIndex → Spacetime → FlowFamily G

/-- Source (346) fixes the entire ultraviolet amplitude of this independent
flow. The finite same-L combination matches only its normalization jets;
it is NOT identified with the full finite-cutoff UV amplitude. -/
structure ContactAnomalyTransportConditions (L : InsertedFlowFamily G)
    (coeff : ContactAnomalyCoefficients G) (full : FullContactAnomaly G)
    (mu : RenormalizationScale) : Prop where
  support : ∀ loop UV A B w C, 0 < UV → coeff loop UV A B w C ≠ 0 →
    A.Admissible ∧ B.Admissible ∧ C.Admissible ∧
      C.dimension + w.order + 3 ≤ A.dimension + B.dimension ∧
      C.ghostNumber = A.ghostNumber + B.ghostNumber + 1 ∧
      C.parity = decide ((A.oddMultiplicity + B.oddMultiplicity + 1) % 2 = 1)
  kernel_smooth : ∀ A B loop leftLoop UV legs s, A.Admissible → B.Admissible →
    leftLoop ≤ loop → 0 < UV →
    ContDiff ℝ ∞ (fun qp : (Fin legs.length → Spacetime) × Spacetime =>
      barePairBVFourierSplit L A B loop leftLoop UV legs qp.1 s qp.2)
  ultraviolet_boundary : ∀ A B w loop UV, A.Admissible → B.Admissible →
    0 < UV → full A B w 0 loop UV UV = bareContactAnomalyChannel L A B w loop UV
  translation : ∀ A B w x loop Λ UV legs q,
    full A B w x loop Λ UV legs q =
      Complex.exp (-Complex.I * (euclideanPair x (∑ i : Fin legs.length, q i) : ℂ)) *
        full A B w 0 loop Λ UV legs q
  outside_channels : ∀ A B w x loop Λ UV,
    A.dimension + B.dimension < w.order + 3 → full A B w x loop Λ UV = 0
  momentum_smooth : ∀ A B w x loop Λ UV legs, A.Admissible → B.Admissible →
    0 < Λ → Λ ≤ UV → ContDiff ℝ ∞ (full A B w x loop Λ UV legs)
  scale_jet_continuous : ∀ A B w x loop UV legs
      (directions : List (Fin legs.length × Fin 4)) q,
    A.Admissible → B.Admissible →
    ContinuousOn (fun Λ : ℝ => momentumJet directions
      (full A B w x loop Λ UV legs) q) (Set.Ioc 0 UV)
  loop_integrable : ∀ A B w x loop Λ UV legs q, A.Admissible → B.Admissible →
    0 < Λ → Λ < UV → MeasureTheory.Integrable
      (linearFlowIntegrand (full A B w x) loop Λ UV legs q)
  flow : ∀ A B w x loop Λ UV legs q, A.Admissible → B.Admissible → 0 < Λ → Λ < UV →
    HasDerivAt (fun scale : ℝ => full A B w x loop scale UV legs q)
      (insertionHomogeneousRHS (L []) (full A B w x) loop Λ UV legs q) Λ
  normalization_jets : ∀ A B w loop UV C, A.Admissible → B.Admissible →
    mu.val < UV → C ∈ monomialsBelow G (contactOutputBound A B w + 1) →
    extractCoefficient C (full A B w 0 loop mu.val UV) 0 =
      extractCoefficient C (transportedContactAnomaly L coeff A B w 0 loop mu.val UV) 0

/-- Actual coupling coefficient of the nonlocal finite-cutoff remainder.
Its weak UV vanishing is a separate, explicit local-representation condition. -/
def contactTransportRemainderIntegrand (L : ℝ → InsertedFlowFamily G)
    (coeff : ℝ → ContactAnomalyCoefficients G) (full : ℝ → FullContactAnomaly G)
    (A B : LocalMonomial G) (w : ContactDerivativeIndex) (order loop : ℕ)
    (Λ UV : ℝ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (xq : (Fin 1 → Spacetime) × (Fin legs.length → Spacetime)) : ℂ :=
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    full g A B w (xq.1 0) loop Λ UV legs xq.2 -
      transportedContactAnomaly (L g) (coeff g) A B w (xq.1 0) loop Λ UV legs xq.2) 0) * test xq

/-- Same coupling family and common normalization scale. Unlike a finite
local-field ansatz at UV, the full flow can contain irrelevant regulator
tails; only their actual compact-test remainder tends to zero. -/
structure FullContactAnomalyFlowConditions (L : ℝ → InsertedFlowFamily G)
    (coeff : ℝ → ContactAnomalyCoefficients G) (full : ℝ → FullContactAnomaly G)
    (normalizationScale : RenormalizationScale) : Prop where
  per_coupling : ∀ g, ContactAnomalyTransportConditions (L g) (coeff g) (full g) normalizationScale
  coupling_smooth : ∀ loop UV A B w C, 0 < UV →
    ContDiff ℝ ∞ (fun g : ℝ => coeff g loop UV A B w C)
  full_coupling_smooth : ∀ A B w x loop Λ UV legs, A.Admissible → B.Admissible →
    0 < Λ → Λ ≤ UV → ContDiff ℝ ∞
      (fun gq : ℝ × (Fin legs.length → Spacetime) => full gq.1 A B w x loop Λ UV legs gq.2)
  graph_grading : ∀ g loop UV A B w C,
    coeff g loop UV A B w C =
      if A.legs.length + B.legs.length ≤ C.legs.length + 2 + 2 * loop then
        (g : ℂ) ^ (C.legs.length + 2 + 2 * loop - (A.legs.length + B.legs.length)) *
          coeff 1 loop UV A B w C
      else 0
  full_graph_grading : ∀ g A B w x loop Λ UV legs q,
    full g A B w x loop Λ UV legs q =
      if A.legs.length + B.legs.length ≤ legs.length + 2 + 2 * loop then
        (g : ℂ) ^ (legs.length + 2 + 2 * loop - (A.legs.length + B.legs.length)) *
          full 1 A B w x loop Λ UV legs q
      else 0
  remainder_integrable : ∀ A B w order loop Λ UV legs (test : JointMomentumTest 1 legs),
    A.Admissible → B.Admissible → 0 < Λ → Λ ≤ UV → HasCompactSupport test →
    MeasureTheory.Integrable (contactTransportRemainderIntegrand L coeff full
      A B w order loop Λ UV legs test)
  remainder_uv_limit : ∀ A B w order loop Λ legs (test : JointMomentumTest 1 legs),
    A.Admissible → B.Admissible → 0 < Λ → HasCompactSupport test →
    Tendsto (fun UV : ℝ => ∫ xq,
      contactTransportRemainderIntegrand L coeff full A B w order loop Λ UV legs test xq)
      atTop (nhds 0)

/-- Full flow witnesses are auxiliary data fixed by the actual boundary
problem and remainder limit; they are not unconstrained physical predictions. -/
def CoupledContactAnomalyTransportConditions (L : ℝ → InsertedFlowFamily G)
    (coeff : ℝ → ContactAnomalyCoefficients G) : Prop :=
  ∃ mu : RenormalizationScale, ∃ full : ℝ → FullContactAnomaly G,
    FullContactAnomalyFlowConditions L coeff full mu

/-- Actual regulator-removal candidate for the computed local contact map.
It is not an independent choice of contact anomaly coefficients. -/
structure ContactAnomalyLimit (G : CompactSimpleGaugeGroup) where
  coefficient : ℕ → LocalMonomial G → LocalMonomial G → ContactDerivativeIndex → LocalMonomial G → ℂ

def ContactAnomalyLimit.Compatible (Q2 : ContactAnomalyLimit G)
    (coeff : ContactAnomalyCoefficients G) : Prop :=
  ∀ loop A B w C, A.Admissible → B.Admissible → C.Admissible →
    Tendsto (fun UV : ℝ => coeff loop UV A B w C) atTop (nhds (Q2.coefficient loop A B w C))

end YangMills.PerturbativeFlow
