import Problems.YangMills.ConnectedWardContinuum
import Problems.YangMills.QuantumOutputRecovery
import Problems.YangMills.ContactAnomalyTransport
import Problems.YangMills.PartialDiagonalContact

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Full connected multi-insertion quantum Ward/contact restoration

FHH (288)–(289), (330)–(348). The equation is imposed for EVERY insertion
number, not inferred from its one- and two-insertion restrictions. Its
single term uses the same generated physical s+A1; its contact term is the
computed classical point bracket plus the same-flow A2 limit. All contacts
act through actual partial-diagonal Schwartz maps, with ordinary position
derivatives. For odd inputs the BV binary coderivation is (-1)^p(A)(A,B),
which fixes the signs absent from the source's bosonic shorthand.

This is an explicit restoration condition, not an existence theorem for
admissible global contact extensions. The connected bulk and same G_0 flow
are linked separately; complete local extension classification/normalization
and the regulator-removal proof remain mathematical obligations.
-/
noncomputable section
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The classical point bracket has no g dependence. A2 is its actual
computed quantum correction, rather than a freely selected contact map. -/
def fullQuantumContactCoefficient (Q2 : ℝ → ContactAnomalyLimit G)
    (g : ℝ) (loop : ℕ) (A B : LocalMonomial G) (w : ContactDerivativeIndex)
    (output : LocalMonomial G) : ℂ :=
  (if loop = 0 then densityMonomialCoefficient
    (classicalPointContactDensity (normalizedMonomialDensity A)
      (normalizedMonomialDensity B) w) output else 0) +
    (Q2 g).coefficient loop A B w output

def quantumContactCouplingCoefficient (Q2 : ℝ → ContactAnomalyLimit G)
    (order loop : ℕ) (A B : LocalMonomial G) (w : ContactDerivativeIndex)
    (output : LocalMonomial G) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => fullQuantumContactCoefficient Q2 g loop A B w output) 0

/-- Fixed same-flow anomaly seed, UV transport, physical limit, degree,
parity/ghost support, and coupling guards for the quantum contact map. -/
structure FullQuantumContactCompatible (L : ℝ → InsertedFlowFamily G)
    (coeff : ℝ → ContactAnomalyCoefficients G) (Q2 : ℝ → ContactAnomalyLimit G) : Prop where
  transport : CoupledContactAnomalyTransportConditions L coeff
  same_limit : ∀ g, (Q2 g).Compatible (coeff g)
  higher_loop : ∀ g A B w output, (Q2 g).coefficient 0 A B w output = 0
  coupling_smooth : ∀ loop A B w output,
    ContDiff ℝ ∞ (fun g : ℝ => fullQuantumContactCoefficient Q2 g loop A B w output)
  support : ∀ g loop A B w output, A.Admissible → B.Admissible →
    fullQuantumContactCoefficient Q2 g loop A B w output ≠ 0 →
    output.Admissible ∧ output.dimension + w.order + 3 ≤ A.dimension + B.dimension ∧
      output.ghostNumber = A.ghostNumber + B.ghostNumber + 1 ∧
      output.parity = decide ((A.oddMultiplicity + B.oddMultiplicity + 1) % 2 = 1)
  graph_grading : ∀ g loop A B w output,
    fullQuantumContactCoefficient Q2 g loop A B w output =
      if A.legs.length + B.legs.length ≤ output.legs.length + 2 + 2 * loop then
        (g : ℂ) ^ (output.legs.length + 2 + 2 * loop - (A.legs.length + B.legs.length)) *
          fullQuantumContactCoefficient Q2 1 loop A B w output
      else 0

def wardPrefixOdd {n : ℕ} (labels : Fin n → LocalMonomial G) (i : Fin n) : ℕ :=
  ∑ k : Fin n, if k < i then (labels k).oddMultiplicity else 0

def singleWardSign {n : ℕ} (labels : Fin n → LocalMonomial G) (i : Fin n) : ℂ :=
  (-1 : ℂ) ^ wardPrefixOdd labels i

/-- Output stays at i and j is removed. The p_i term converts the odd
antibracket into its graded-symmetric binary coderivation. -/
def pairWardSign {n : ℕ} (labels : Fin n → LocalMonomial G) (i j : Fin n) : ℂ :=
  (-1 : ℂ) ^ (wardPrefixOdd labels i + (labels i).oddMultiplicity +
    (labels j).oddMultiplicity *
      ∑ k : Fin n, if i < k ∧ k < j then (labels k).oddMultiplicity else 0)

/-- Every q-image is inserted into the same connected hierarchy at its
original position; coupling and hbar orders are convolved independently. -/
def multiWardSingleTerm (C : ConnectedWardData G) (Q1 : QuantumWardLimit G)
    {n : ℕ} (labels : Fin n → LocalMonomial G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest n legs) : ℂ :=
  ∑ i : Fin n, singleWardSign labels i *
    ∑ output ∈ monomialsBelow G ((labels i).dimension + 2),
      ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
        quantumWardCouplingCoefficient Q1 a.val b.val (labels i) output *
          C.physical false (order - a.val) (loop - b.val)
            (Function.update labels i output) legs test

/-- Actual first-centered contact action on an arbitrary joint test,
including tests crossing ANY partial insertion diagonal. Spectators retain
their order and coordinates; every derivative acts on the removed j slot. -/
def multiWardPairTerm (C : ConnectedWardData G) (Q2 : ℝ → ContactAnomalyLimit G)
    {n : ℕ} (labels : Fin (n + 2) → LocalMonomial G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest (n + 2) legs) : ℂ :=
  ∑ i : Fin (n + 2), ∑ j : Fin (n + 2), if h : i < j then
    pairWardSign labels i j *
      ∑ w ∈ contactDerivativeIndices (labels i) (labels j),
        ∑ output ∈ monomialsBelow G (contactOutputBound (labels i) (labels j) w + 1),
          ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
            quantumContactCouplingCoefficient Q2 a.val b.val (labels i) (labels j) w output *
              C.physical false (order - a.val) (loop - b.val)
                (pairMergedLabels labels i j h output) legs
                (firstPairContactTest i j h w legs test)
  else 0

/-- The remainder of (333)/(347), defined as an actual distributional
Ward defect, not supplied as an unconstrained anomaly family. -/
def connectedMultiWardRemainder (C : ConnectedWardData G) (Q1 : QuantumWardLimit G)
    (Q2 : ℝ → ContactAnomalyLimit G) {n : ℕ}
    (labels : Fin (n + 2) → LocalMonomial G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest (n + 2) legs) : ℂ :=
  C.physical true order loop labels legs test -
    multiWardSingleTerm C Q1 labels order loop legs test -
      multiWardPairTerm C Q2 labels order loop legs test

/-- Source (288) for ALL arities≥2 and every nonexceptional compact joint
test. No off-insertion-diagonal restriction is allowed here: otherwise the
entire contact sum would be invisible. -/
def FullConnectedWardIdentity (C : ConnectedWardData G) (Q1 : QuantumWardLimit G)
    (Q2 : ℝ → ContactAnomalyLimit G) : Prop :=
  ∀ n (labels : Fin (n + 2) → LocalMonomial G) order loop legs
      (test : JointMomentumTest (n + 2) legs),
    (∀ i, (labels i).Admissible) → HasCompactSupport test →
    NonexceptionalSupport .single test →
    connectedMultiWardRemainder C Q1 Q2 labels order loop legs test = 0

/-- One coherent restoration bundle: the background, connected/disconnected
flow, both quantum anomaly maps, and corrected observable dictionary all
belong to the same L/F/W system. Actual Yang--Mills action boundary data and
complete admissible extension constraints must be conjoined by assembly. -/
structure FullMultiWardRestoration {B : InvariantForm G} (e : ColorFrame B)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G)
    (W : WardContinuumData G) (C : ConnectedWardData G)
    (singleTransport : SameTheoryWardTransportData e L)
    (pairCoeff : ℝ → ContactAnomalyCoefficients G)
    (Q1 : QuantumWardLimit G) (Q2 : ℝ → ContactAnomalyLimit G)
    (lift : QuantumObservableLift G) : Prop where
  same_bulk : W.BulkCompatible L F
  same_connected : C.Compatible W L F
  same_contact : FullQuantumContactCompatible L pairCoeff Q2
  same_dictionary : lift.Compatible e singleTransport.coefficient Q1
  same_dictionary_limit : lift.LimitCompatible L W
  action : RestoredActionWardIdentity W
  single : GeneratedPhysicalSingleWardIdentity W Q1
  nilpotent : Q1.Nilpotent
  multiple : FullConnectedWardIdentity C Q1 Q2

end YangMills.PerturbativeFlow
