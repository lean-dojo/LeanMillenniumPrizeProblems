import Problems.YangMills.WardContinuum
import Problems.YangMills.RegulatedWardInsertion

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Insertion-anomaly flow and local anomaly transport

Source 1511.09425 (321)–(326). A local insertion and the INTEGRATED action
anomaly have different momentum constraints. Their connecting momentum is
fixed by the action branch, rather than integrated independently. These are
operator definitions and a generic boundary-value interface; the bare seeds
must be specialized to the same regulated BV defects. They do not assert
existence, anomaly cancellation, or a contact-extension theorem.
-/
noncomputable section
open scoped ContDiff
open Filter
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Ordered contraction with the momentum-conserving action anomaly on
its RIGHT. This keeps the source's insertion order and intrinsic odd sign.
The action branch fixes p+sum(q_right)=0. -/
def rightActionAnomalySource (A : LocalMonomial G)
    (insertion actionAnomaly : FlowFamily G) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ l : Fin (loop + 1), ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
    let t := complementIndices legs s
    let p := -selectedMomentum legs t q
    splitSign legs s * ∑ M : BasicField G, ∑ N : BasicField G,
      intrinsicContractionSign A.parity M * (basicDerivativeCovariance Λ M N p : ℂ) *
        insertion l.val Λ Λ0 (.inl N :: selectedLegs legs s)
          (prependMomenta (.inl N) (-p) (selectedMomenta legs s q)) *
        actionAnomaly (loop - l.val) Λ Λ0 (.inl M :: selectedLegs legs t)
          (prependMomenta (.inl M) p (selectedMomenta legs t q))

/-- The source (323) has the same inhomogeneous flow as two insertions.
There is no extra half factor or loop shift in its quadratic source. -/
def insertionAnomalyRHS (background : FlowFamily G) (L : InsertedFlowFamily G)
    (actionAnomaly : FlowFamily G) (anomaly : LocalMonomial G → Spacetime → FlowFamily G)
    (A : LocalMonomial G) (x : Spacetime) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  insertionHomogeneousRHS background (anomaly A x) loop Λ Λ0 legs q -
    rightActionAnomalySource A (L [⟨A, x⟩]) actionAnomaly loop Λ Λ0 legs q

/-- Finite local coefficients of A1: the output degree is at most [A]+1,
and its ghost number/parity shift by one. The coefficients are mathematical
unknowns to be determined by the SAME anomaly boundary problem below. -/
abbrev LocalAnomalyCoefficients (G : CompactSimpleGaugeGroup) :=
  ℕ → ℝ → LocalMonomial G → LocalMonomial G → ℂ

def transportedLocalAnomaly (L : InsertedFlowFamily G)
    (coeff : LocalAnomalyCoefficients G) (A : LocalMonomial G) (x : Spacetime) :
    FlowFamily G :=
  fun loop Λ Λ0 legs q =>
    ∑ B ∈ monomialsBelow G (A.dimension + 2), ∑ l : Fin (loop + 1),
      coeff l.val Λ0 A B * L [⟨B, x⟩] (loop - l.val) Λ Λ0 legs q

/-- Renormalization probes are actual nonexceptional momentum points for
all admissible output monomials, not arbitrary desired amplitude values. -/
structure AnomalyNormalizationPoints (G : CompactSimpleGaugeGroup) where
  point : (B : LocalMonomial G) → Fin B.legs.length → Spacetime
  nonexceptional : ∀ B, B.Admissible → NonexceptionalMomenta false (point B)

/-- Generic source-exact boundary problem. `bareAction` and `bareInsertion`
are explicit ordered-amplitude seeds; a final YM condition must substitute
the regulated BV functions, never existentially choose these seeds.

The positive-scale jet continuity reaches the UV endpoint. Relevant jets
are matched after IR transport at NONEXCEPTIONAL external momenta. This
avoids identifying the μ-normalized insertion matrix with the physical one.
-/
structure AnomalyTransportConditions
    (background : FlowFamily G) (L : InsertedFlowFamily G)
    (bareAction : ℕ → ℝ → OrderedAmplitude G)
    (bareInsertion : LocalMonomial G → Spacetime → ℕ → ℝ → OrderedAmplitude G)
    (actionAnomaly : FlowFamily G)
    (anomaly : LocalMonomial G → Spacetime → FlowFamily G)
    (coeff : LocalAnomalyCoefficients G) (points : AnomalyNormalizationPoints G) : Prop where
  coefficient_support : ∀ loop UV A B, coeff loop UV A B ≠ 0 →
    B.Admissible ∧ B.dimension ≤ A.dimension + 1 ∧
      B.ghostNumber = A.ghostNumber + 1 ∧ B.parity = !A.parity
  action_uv : ∀ loop UV, 0 < UV → actionAnomaly loop UV UV = bareAction loop UV
  insertion_uv : ∀ A x loop UV, A.Admissible → 0 < UV →
    anomaly A x loop UV UV = bareInsertion A x loop UV
  action_smooth : ∀ loop Λ UV legs, 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (actionAnomaly loop Λ UV legs)
  insertion_smooth : ∀ A x loop Λ UV legs, A.Admissible → 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (anomaly A x loop Λ UV legs)
  action_jet_continuous : ∀ loop UV legs (directions : List (Fin legs.length × Fin 4)) q,
    ContinuousOn (fun Λ : ℝ => momentumJet directions (actionAnomaly loop Λ UV legs) q)
      (Set.Ioc 0 UV)
  insertion_jet_continuous : ∀ A x loop UV legs
      (directions : List (Fin legs.length × Fin 4)) q, A.Admissible →
    ContinuousOn (fun Λ : ℝ => momentumJet directions (anomaly A x loop Λ UV legs) q)
      (Set.Ioc 0 UV)
  action_loop_integrable : ∀ loop Λ UV legs q, 0 < Λ → Λ < UV →
    MeasureTheory.Integrable (linearFlowIntegrand actionAnomaly loop Λ UV legs q)
  insertion_loop_integrable : ∀ A x loop Λ UV legs q,
    A.Admissible → 0 < Λ → Λ < UV →
    MeasureTheory.Integrable (linearFlowIntegrand (anomaly A x) loop Λ UV legs q)
  action_flow : ∀ loop Λ UV legs q, 0 < Λ → Λ < UV →
    HasDerivAt (fun scale : ℝ => actionAnomaly loop scale UV legs q)
      (insertionHomogeneousRHS background actionAnomaly loop Λ UV legs q) Λ
  insertion_flow : ∀ A x loop Λ UV legs q, A.Admissible → 0 < Λ → Λ < UV →
    HasDerivAt (fun scale : ℝ => anomaly A x loop scale UV legs q)
      (insertionAnomalyRHS background L actionAnomaly anomaly A x loop Λ UV legs q) Λ
  transported_flow : ∀ A x loop Λ UV legs q, A.Admissible → 0 < Λ → Λ < UV →
    HasDerivAt (fun scale : ℝ => transportedLocalAnomaly L coeff A x loop scale UV legs q)
      (insertionHomogeneousRHS background (transportedLocalAnomaly L coeff A x)
        loop Λ UV legs q) Λ
  irrelevant_uv : ∀ A B loop UV, A.Admissible → B.Admissible →
    A.dimension + 1 < B.dimension → 0 < UV →
    ∀ q : Fin B.legs.length → Spacetime,
      extractCoefficient B (transportedLocalAnomaly L coeff A 0 loop UV UV) q = 0
  relevant_ir : ∀ A B loop UV, A.Admissible → B.Admissible →
    B.dimension ≤ A.dimension + 1 → 0 < UV →
      Tendsto (fun Λ : ℝ =>
        extractCoefficient B (anomaly A 0 loop Λ UV) (points.point B) -
        extractCoefficient B (transportedLocalAnomaly L coeff A 0 loop Λ UV) (points.point B))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- Final same-YM specialization: both UV seeds are fixed regulated BV
expressions of this background and these insertion counterterms. No new
bare anomaly polynomial or independent Ward action is chosen. -/
def SameTheoryAnomalyTransport {B : InvariantForm G} (e : ColorFrame B)
    (background : FlowFamily G) (L : InsertedFlowFamily G) (g : ℝ)
    (actionAnomaly : FlowFamily G)
    (anomaly : LocalMonomial G → Spacetime → FlowFamily G)
    (coeff : LocalAnomalyCoefficients G) (points : AnomalyNormalizationPoints G) : Prop :=
  BVContractionIntegrability background ∧ InsertionBVContractionIntegrability L ∧
  AnomalyTransportConditions background L (bareActionWardDefect background)
    (bareInsertionWardDefect e background L g) actionAnomaly anomaly coeff points

/-- The generated quantum local ST coefficients are classical s plus A1.
The classical part uses the full same-action evolutionary BV differential,
so derivative descendants are retained. -/
def generatedQuantumWardCoefficient {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (coeff : LocalAnomalyCoefficients G) (loop : ℕ) (UV : ℝ)
    (A B : LocalMonomial G) : ℂ :=
  (if loop = 0 then densityMonomialCoefficient
    (FullBV.classicalLocalSTDensity e g (normalizedMonomialDensity A)) B else 0) +
    coeff loop UV A B

/-- Generic FINITE-cutoff algebraic test, NOT a mandatory YM condition:
regulated breaking can persist at finite UV. The physical consistency
condition belongs to QuantumWardLimit.Nilpotent below. This helper tests the
full outgoing degree [A]+2 instead of a falsely closed square truncation. -/
def GeneratedQuantumWardNilpotent {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (coeff : LocalAnomalyCoefficients G) : Prop :=
  ∀ A C loop UV, A.Admissible → C.Admissible → C.dimension ≤ A.dimension + 2 →
    0 < UV →
    (∑ middle ∈ monomialsBelow G (A.dimension + 2), ∑ l : Fin (loop + 1),
      generatedQuantumWardCoefficient e g coeff l.val UV A middle *
      generatedQuantumWardCoefficient e g coeff (loop - l.val) UV middle C) = 0

/-- Candidate unregulated quantum ST coefficients, uniquely identified by
coefficientwise limits when Compatible holds. -/
structure QuantumWardLimit (G : CompactSimpleGaugeGroup) where
  coefficient : ℝ → ℕ → LocalMonomial G → LocalMonomial G → ℂ

def QuantumWardLimit.Compatible {B : InvariantForm G} (e : ColorFrame B)
    (anomalyCoeff : ℝ → LocalAnomalyCoefficients G) (Q : QuantumWardLimit G) : Prop :=
  ∀ g loop A output, A.Admissible → output.Admissible →
    output.dimension ≤ A.dimension + 1 →
    Tendsto (fun UV : ℝ => generatedQuantumWardCoefficient e g (anomalyCoeff g)
      loop UV A output) atTop (nhds (Q.coefficient g loop A output))

/-- The physical differential raises engineering degree and ghost number
by one and reverses parity. This full-output support condition prevents a
bounded coordinate test from hiding higher-degree outgoing coefficients. -/
def QuantumWardLimit.Filtered (Q : QuantumWardLimit G) : Prop :=
  ∀ g loop A output, A.Admissible → Q.coefficient g loop A output ≠ 0 →
    output.Admissible ∧ output.dimension ≤ A.dimension + 1 ∧
      output.ghostNumber = A.ghostNumber + 1 ∧ output.parity = !A.parity

/-- Physical nilpotence after regulator removal and action-Ward restoration.
Composition retains every degree-allowed intermediate/output monomial. -/
def QuantumWardLimit.Nilpotent (Q : QuantumWardLimit G) : Prop :=
  ∀ g A output loop, A.Admissible → output.Admissible →
    output.dimension ≤ A.dimension + 2 →
    (∑ middle ∈ monomialsBelow G (A.dimension + 2), ∑ l : Fin (loop + 1),
      Q.coefficient g l.val A middle * Q.coefficient g (loop - l.val) middle output) = 0

end YangMills.PerturbativeFlow
