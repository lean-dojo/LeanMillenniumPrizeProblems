import Problems.YangMills.CompositeExtraction
import Problems.YangMills.PerturbativeFlow

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed multiple-insertion oversubtraction flow

Fröb--Holland (1603.08012), eq.(4.3), with the boundary projectors (4.4)
from CompositeExtraction. The background and each inserted coefficient are
families for the same actual elementary fields, covariance, and graded signs.
The independent pair momentum is integrated rather than incorrectly fixed
by overall conservation at a local insertion.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def LocalMonomial.oddMultiplicity (m : LocalMonomial G) : ℕ :=
  m.sum (fun v n => if ExternalLeg.parity v.1 then n else 0)

def LocalMonomial.parity (m : LocalMonomial G) : Bool :=
  decide (m.oddMultiplicity % 2 = 1)

def LocalMonomial.ghostNumber (m : LocalMonomial G) : ℤ :=
  m.sum (fun v n => (n : ℤ) * ExternalLeg.ghostNumber v.1)

def inputOddMultiplicity (input : List (PositionedInsertion G)) : ℕ :=
  (input.map (fun a => a.monomial.oddMultiplicity)).sum

def inputGhostNumber (input : List (PositionedInsertion G)) : ℤ :=
  (input.map (fun a => a.monomial.ghostNumber)).sum

/-- The source term places the selected ordered pair before its spectators.
The sign is the Koszul sign of precisely this insertion-block permutation. -/
def insertionPairSign (input : List (PositionedInsertion G))
    (k l : Fin input.length) : ℂ :=
  let pair : Finset (Fin input.length) := {k, l}
  (-1 : ℂ) ^ (∑ i ∈ pair, ∑ j ∈ Finset.univ \ pair,
    if j < i then (input.get i).monomial.oddMultiplicity *
      (input.get j).monomial.oddMultiplicity else 0)

def insertionSpectators (input : List (PositionedInsertion G))
    (k l : Fin input.length) : List (PositionedInsertion G) :=
  ((Finset.univ \ ({k, l} : Finset (Fin input.length))).sort (· ≤ ·)).map input.get

/-- One chosen pair, with the exact independent-momentum contraction,
multiplied by all the remaining single-insertion functionals. -/
def insertionPairSource (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) (k l : Fin input.length) : FlowFamily G :=
  fun loop Λ Λ0 legs q => insertionPairSign input k l *
    flowProduct
      (fun r scale uv external momenta => independentContractionRHS
        (input.get k).monomial.parity (L [input.get k]) (L [input.get l])
        r scale uv external momenta)
      (singleInsertionProduct L (insertionSpectators input k l)) loop Λ Λ0 legs q

/-- The sum k<k' in (4.3), with no extra 1/2 and no hbar shift. -/
def oversubtractionSource (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) : FlowFamily G :=
  fun loop Λ Λ0 legs q => ∑ k : Fin input.length, ∑ l : Fin input.length,
    if k < l then insertionPairSource L input k l loop Λ Λ0 legs q else 0

/-- The complete right-hand side of (4.3). F is linear in its own family;
the inhomogeneous source is fixed by the same single-insertion L. -/
def oversubtractionFlowRHS (background : FlowFamily G) (L : InsertedFlowFamily G)
    (F : OversubtractedFamily G) (D : ℕ) (input : List (PositionedInsertion G))
    (loop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : ℂ :=
  insertionHomogeneousRHS background (F D input) loop Λ Λ0 legs q -
    oversubtractionSource L input loop Λ Λ0 legs q

/-- All missing analytic and algebraic conditions are explicit fixed
relations, not a predicate supplied by an existence proof. Combined with a
background CoefficientFlowConditions for the same action/frame, these fix
the insertion flow and its single and multiple insertion boundary normalizations.
Existence, uniqueness and renormalized UV limits remain supporting theorems.
-/
structure InsertionFlowConditions (background : FlowFamily G)
    (L : InsertedFlowFamily G) (F : OversubtractedFamily G) (μ : ℝ) : Prop where
  single_boundary : SingleInsertionBoundaryConditions L μ
  oversubtraction_boundary : OversubtractionBoundaryConditions F μ
  /-- Noninserted amplitudes are literally the same background family. -/
  background_identity : L [] = background
  single_statistics : ∀ input loop Λ Λ0 legs q,
    (oddCount legs % 2 ≠ inputOddMultiplicity input % 2 ∨
      totalGhostNumber legs ≠ inputGhostNumber input) →
      L input loop Λ Λ0 legs q = 0
  oversubtraction_statistics : ∀ D input loop Λ Λ0 legs q,
    (oddCount legs % 2 ≠ inputOddMultiplicity input % 2 ∨
      totalGhostNumber legs ≠ inputGhostNumber input) →
      F D input loop Λ Λ0 legs q = 0
  single_graded_symmetry : ∀ A x loop Λ Λ0 legs q (π : Equiv.Perm (Fin legs.length)),
    L [⟨A, x⟩] loop Λ Λ0 (permutedLegs legs π) (permutedMomenta legs π q) =
      permutationSign legs π * L [⟨A, x⟩] loop Λ Λ0 legs q
  oversubtraction_graded_symmetry : ∀ D input loop Λ Λ0 legs q
      (π : Equiv.Perm (Fin legs.length)),
    F D input loop Λ Λ0 (permutedLegs legs π) (permutedMomenta legs π q) =
      permutationSign legs π * F D input loop Λ Λ0 legs q
  single_translation : ∀ A x y loop Λ Λ0 legs q,
    L [⟨A, x⟩] loop Λ Λ0 legs q =
      Complex.exp (-Complex.I * (euclideanPair y (∑ i : Fin legs.length, q i) : ℂ)) *
        L [⟨A, x - y⟩] loop Λ Λ0 legs q
  single_loop_integrable : ∀ A x loop Λ Λ0 legs q,
    0 < Λ → Λ < Λ0 →
      Integrable (linearFlowIntegrand (L [⟨A, x⟩]) loop Λ Λ0 legs q)
  oversubtraction_loop_integrable : ∀ D input loop Λ Λ0 legs q,
    0 < Λ → Λ < Λ0 →
      Integrable (linearFlowIntegrand (F D input) loop Λ Λ0 legs q)
  /-- Every independently integrated pair source is genuinely integrable;
  Lean's totalized zero integral cannot supply a false coefficient. -/
  independent_pair_integrable : ∀ (input : List (PositionedInsertion G)) (k l : Fin input.length)
      loop Λ Λ0 legs q, k < l → 0 < Λ → Λ < Λ0 →
    Integrable (independentContractionIntegrand (input.get k).monomial.parity
      (L [input.get k]) (L [input.get l]) loop Λ Λ0 legs q)
  single_flow : ∀ A x loop Λ Λ0 legs q,
    0 < Λ → Λ < Λ0 →
      HasDerivAt (fun scale : ℝ => L [⟨A, x⟩] loop scale Λ0 legs q)
        (insertionHomogeneousRHS background (L [⟨A, x⟩]) loop Λ Λ0 legs q) Λ
  oversubtraction_flow : ∀ D (input : InsertionCluster G) loop Λ Λ0 legs q,
    0 < Λ → Λ < Λ0 →
      HasDerivAt (fun scale : ℝ => F D input.insertions loop scale Λ0 legs q)
        (oversubtractionFlowRHS background L F D input.insertions loop Λ Λ0 legs q) Λ

/-- The coupled family used when extracting actual g-Taylor coefficients.
Joint momentum/coupling smoothness is explicit; separate per-g smoothness
would not justify interchanging g derivatives and momentum projectors. -/
structure CoupledInsertionFlowConditions (background : ℝ → FlowFamily G)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G)
    (μ : ℝ) : Prop where
  per_coupling : ∀ g, InsertionFlowConditions (background g) (L g) (F g) μ
  single_joint_smooth : ∀ input loop Λ Λ0 legs,
    0 < Λ → Λ ≤ Λ0 → ContDiff ℝ ∞
      (fun gq : ℝ × (Fin legs.length → Spacetime) =>
        L gq.1 input loop Λ Λ0 legs gq.2)
  oversubtraction_joint_smooth : ∀ D input loop Λ Λ0 legs,
    0 < Λ → Λ ≤ Λ0 → ContDiff ℝ ∞
      (fun gq : ℝ × (Fin legs.length → Spacetime) =>
        F gq.1 D input loop Λ Λ0 legs gq.2)

end YangMills.PerturbativeFlow
