import Problems.YangMills.CompositeFields
import Problems.YangMills.FreeWardExtraction
import Problems.YangMills.OversubtractedFlow

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Physical output recovery from the generated full monomial expansion

An invariant output polynomial is NOT its own dual coefficient projector.
This module uses the same renormalized insertion amplitudes and the actual
G-dependent polynomial expansion. Equality is a full coefficient-functional
identity modulo the fixed free BV Ward image, not arbitrary selected OPE
numbers or agreement of a few jets.

The full restored quantum Ward/BRST cohomology theorem and physical UV/IR
limit construction are needed to justify interpreting the Ward image as
null on physical observables. No such theorem is assumed here. In particular,
this conditional recovery relation alone is not a complete physical projector.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- A continuum insertion coefficient family must elsewhere be fixed by
actual limits of the same flow family. It is a mathematical argument to the
relations below, not permission to choose independent physical predictions. -/
abbrev ContinuumInsertionFamily (G : CompactSimpleGaugeGroup) :=
  List (PositionedInsertion G) → ℕ → OrderedAmplitude G

/-- The polynomial is inserted through the fixed normalized monomial map.
For stress, this operation applies to its classical/tree symbol only: the
full anomalous stress insertion cannot be defined to be the all-order linear
image of a classically traceless polynomial. -/
def continuumPolynomialInsertion (physical : ContinuumInsertionFamily G)
    (g : ℝ) (P : PotentialPolynomial G) (loop : ℕ) : OrderedAmplitude G :=
  fun legs q => polynomialInsertionValue
    (fun labels => physical labels loop legs q) g [(P, 0)] []

def continuumInvariantInsertion {B : InvariantForm G} (e : ColorFrame B)
    (physical : ContinuumInsertionFamily G) (g : ℝ)
    (p : CurvatureJetPolynomial.invariantAlgebra G) (loop : ℕ) : OrderedAmplitude G :=
  continuumPolynomialInsertion physical g
    (classicalInsertionPolynomial e (p : CurvatureJetPolynomial G)) loop

/-- Actual renormalized insertion matrix, with monomial rows and invariant
operator columns. It is not the array of coefficients of p used as a dual. -/
def renormalizedPhysicalInsertionMatrix {n rows : ℕ} {B : InvariantForm G}
    (e : ColorFrame B) (L : InsertedFlowFamily G) (g scale ultraviolet : ℝ)
    (outputs : Fin rows → LocalMonomial G)
    (physicalLabels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (loop : ℕ) : Matrix (Fin rows) (Fin n) ℂ :=
  fun row col => extractCoefficient (outputs row)
    (polynomialInsertionFlow L g
      [(classicalInsertionPolynomial e (physicalLabels col : CurvatureJetPolynomial G), 0)]
      loop scale ultraviolet) 0

/-- Only actual local ghost-number -1 primitives can provide a Ward-exact
ambiguity. Their engineering degree is lowered by one because s0 raises it. -/
def primitiveMonomialsBelow (G : CompactSimpleGaugeGroup) (D : ℕ) :
    Finset (LocalMonomial G) := by
  classical
  exact (monomialsBelow G D).filter
    (fun m => m.ghostNumber = -1 ∧ m.dimension + 1 < D)

/-- Complete monomial-output functional, after a relative-configuration test
has paired its generated coefficient distributions. The loop orders combine
by the exact formal Cauchy product. -/
def generatedOutputFunctional (physical : ContinuumInsertionFamily G)
    (generated : ℕ → LocalMonomial G → ℂ) (D loop : ℕ) : OrderedAmplitude G :=
  fun legs q => ∑ m ∈ monomialsBelow G D, ∑ r : Fin (loop + 1),
    generated r.val m * physical [⟨m, 0⟩] (loop - r.val) legs q

def invariantOutputFunctional {n : ℕ} {B : InvariantForm G} (e : ColorFrame B)
    (physical : ContinuumInsertionFamily G) (g : ℝ)
    (physicalLabels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (coefficients : ℕ → Fin n → ℂ) (loop : ℕ) : OrderedAmplitude G :=
  fun legs q => ∑ i : Fin n, ∑ r : Fin (loop + 1), coefficients r.val i *
    continuumInvariantInsertion e physical g (physicalLabels i) (loop - r.val) legs q

def primitiveOutputFunctional (physical : ContinuumInsertionFamily G)
    (primitive : ℕ → LocalMonomial G → ℂ) (D loop : ℕ) : OrderedAmplitude G :=
  fun legs q => ∑ m ∈ primitiveMonomialsBelow G D, ∑ r : Fin (loop + 1),
    primitive r.val m * physical [⟨m, 0⟩] (loop - r.val) legs q

/-- Concrete physical recovery: the same generated full expansion differs
from the same G-invariant operator expansion by a fixed S0 Ward image.
This is imposed on the full ordered amplitude hierarchy, not only a square
finite jet block. It therefore does not discard outgoing higher-degree
components of the BRST transformation.

No independence/bijection of the actual quantum fields is required. To select
coefficient representatives and prove the relation's sufficiency, the full
BRST cohomology and normalized finite scheme transport must still be supplied.
Contact extensions on coincidence diagonals are a separate local prescription;
use this relation with configuration tests away from those diagonals. -/
def PhysicalCohomologicalRecovery {n : ℕ} {B : InvariantForm G} (e : ColorFrame B)
    (physical : ContinuumInsertionFamily G) (g : ℝ) (D : ℕ)
    (physicalLabels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (generated : ℕ → LocalMonomial G → ℂ)
    (coefficients : ℕ → Fin n → ℂ) : Prop :=
  (∀ i, intrinsicEngineeringDimension (physicalLabels i) < D) ∧
  ∃ primitive : ℕ → LocalMonomial G → ℂ, ∀ loop legs q,
    generatedOutputFunctional physical generated D loop legs q -
      invariantOutputFunctional e physical g physicalLabels coefficients loop legs q =
        freeWardAmplitude (primitiveOutputFunctional physical primitive D loop) legs q

end YangMills.PerturbativeFlow
