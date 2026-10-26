import Problems.YangMills.OversubtractedFlow
import Problems.YangMills.FullBV
import Problems.YangMills.RegulatedBVFlow

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed bare single-insertion Ward defects

FHH (324) subtracts the classical LOCAL ST variation, not its class modulo
total divergences. The latter would incorrectly kill derivative insertions.
The actual same-action evolutionary differential includes antifields and
all jet prolongations. Its density is inserted through exact normalized jet
coefficient extraction; no independently selected classical variation appears.
The weighted-degree reconstruction and amplitude equivalence are supporting
lemmas required before source-fidelity admission.
-/
noncomputable section
open MeasureTheory
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The jet labels in the monomial extractor and the full BV algebra agree
literally in field/antifield species and ordinary derivative multiindex. -/
def fullBVJet (v : JetVariable G) : FullBV.Jet G := ⟨v.1, v.2⟩

/-- Normalized local monomials, with canonical order and exterior ghosts.
Even multiplicities are divided by their actual factorials. -/
def normalizedMonomialDensity (m : LocalMonomial G) : FullBV.JetAlgebra G :=
  ((m.multiplicityFactorial : ℂ)⁻¹) •
    (m.orderedJets.map (fun v => FullBV.jet (fullBVJet v))).prod

/-- The scalar coefficient in the normalized monomial basis comes from
actual ordered jet partials and augmentation, not a polynomial used as a dual. -/
def densityMonomialCoefficient (P : FullBV.JetAlgebra G) (m : LocalMonomial G) : ℂ :=
  FullBV.augmentation (FullBV.externalJetDerivative (m.orderedJets.map fullBVJet) P)

/-- Explicit finite normalized density insertion. The bound in the classical
ST use below is fixed by [s O_A]=[A]+1, not selected by a proof author. -/
def boundedDensityInsertion (L : InsertedFlowFamily G) (bound : ℕ)
    (P : FullBV.JetAlgebra G) (x : Spacetime) : FlowFamily G :=
  fun loop Λ Λ0 legs q => ∑ m ∈ monomialsBelow G bound,
    densityMonomialCoefficient P m * L [⟨m, x⟩] loop Λ Λ0 legs q

/-- s O_A computed from the same full master-action density, with ordinary
jet prolongation. Derivative descendants remain genuine local insertions. -/
def classicalVariationInsertion {B : InvariantForm G} (e : ColorFrame B)
    (L : InsertedFlowFamily G) (g : ℝ) (A : LocalMonomial G) (x : Spacetime) : FlowFamily G :=
  boundedDensityInsertion L (A.dimension + 2)
    (FullBV.classicalLocalSTDensity e g (normalizedMonomialDensity A)) x

/-- The exact bare defect formula (324), expanded at loop order l. Its seed
is therefore determined by the SAME action and insertion counterterms.
The loop-zero Delta contribution is absent rather than using l-1 at l=0. -/
def bareInsertionWardDefect {B : InvariantForm G} (e : ColorFrame B)
    (background : FlowFamily G) (L : InsertedFlowFamily G) (g : ℝ)
    (A : LocalMonomial G) (x : Spacetime) (loop : ℕ) (ultraviolet : ℝ) : OrderedAmplitude G :=
  fun legs q =>
    regulatedFreeWardAmplitude ultraviolet (L [⟨A, x⟩] loop ultraviolet ultraviolet) legs q +
      regulatedBVBracket false background (L [⟨A, x⟩]) loop ultraviolet ultraviolet legs q +
      (if loop = 0 then 0 else regulatedBVLaplacian A.parity ultraviolet
        (L [⟨A, x⟩] (loop - 1) ultraviolet ultraviolet) legs q) -
      classicalVariationInsertion e L g A x loop ultraviolet ultraviolet legs q

/-- Source (338) at both local insertion points zero. The Fourier measure
is NOT included; its polynomial Taylor coefficients become local deltas. -/
def barePairBVFourierKernel (L : InsertedFlowFamily G)
    (A B : LocalMonomial G) (loop : ℕ) (ultraviolet : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (p : Spacetime) : ℂ :=
  pairBVFourierKernel A.parity (L [⟨A, 0⟩]) (L [⟨B, 0⟩])
    loop ultraviolet ultraviolet legs q p

/-- Individual unshuffle/loop split is exposed because converting the
second insertion's translation phase to first-centered delta normal form
uses the RIGHT external momentum of this very partition. -/
def barePairBVFourierSplit (L : InsertedFlowFamily G)
    (A B : LocalMonomial G) (loop leftLoop : ℕ) (ultraviolet : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (s : Finset (Fin legs.length)) (p : Spacetime) : ℂ :=
  pairBVFourierSplit A.parity (L [⟨A, 0⟩]) (L [⟨B, 0⟩])
    loop leftLoop ultraviolet ultraviolet legs q s p

/-- Legitimacy of the BV contractions in all local insertion-defect seeds. -/
structure InsertionBVContractionIntegrability (L : InsertedFlowFamily G) : Prop where
  laplacian : ∀ A x loop Λ0 legs q, 0 < Λ0 →
    Integrable (regulatedBVLaplacianIntegrand A.parity Λ0
      (L [⟨A, x⟩] loop Λ0 Λ0) legs q)

end YangMills.PerturbativeFlow
