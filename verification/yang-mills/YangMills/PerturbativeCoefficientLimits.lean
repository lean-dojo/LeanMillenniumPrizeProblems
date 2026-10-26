import YangMills.OversubtractedFlow
import YangMills.MultiOperatorProductExpansion

/-!
# Fixed group-specific Euclidean coefficient limits

The integrand below is computed from the same normalized insertion flow,
actual G curvature-polynomial inputs, and the fixed triangular OPE extractor.
Only compact tests away from partial coincidence are used for the initial UV
limit. Requiring its unsubtracted weak limit across coincidence would already
fail for free composite Wick powers. Contact extensions require local
power-counting and Ward-compatible counterterms, not a totalized integral.
Physical invariant-output projection and RG loop assembly remain separate.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Concrete fixed action and insertion equations, with common reference
scale and actual gauge Lie algebra. This is the flow part of a prescription;
quantum Ward restoration and physical cohomology must still be added. -/
structure FixedFlowSystem {B : InvariantForm G} (e : ColorFrame B) where
  referenceScale : RenormalizationScale
  localScheme : LocalMarginalData G
  background : ScaleCouplingFamily G
  insertions : ℝ → ℝ → InsertedFlowFamily G
  oversubtractions : ℝ → ℝ → OversubtractedFamily G
  background_equations : CoefficientFlowConditions e localScheme background
  insertion_equations : ∀ μ, 0 < μ →
    CoupledInsertionFlowConditions (background μ) (insertions μ) (oversubtractions μ) μ

/-- All input labels are expanded by the fixed actual-G polynomial map.
The final insertion is at zero; the other n relative points are r_i. -/
def FixedFlowSystem.regulatedInvariantCoefficient {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) {n : ℕ}
    (labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (last : CurvatureJetPolynomial.invariantAlgebra G)
    (output : LocalMonomial G) (loop : ℕ) (g Λ0 : ℝ)
    (r : OPE.RelativeSpace n) : ℂ :=
  regulatedPolynomialOPECoefficient (S.insertions S.referenceScale.val g) (S.oversubtractions S.referenceScale.val g)
    g S.referenceScale.val Λ0
    (List.ofFn (fun i => (classicalInsertionPolynomial e (labels i), r i)))
    (classicalInsertionPolynomial e last, 0) loop output

/-- Actual g-Taylor coefficient of that same regulated coefficient. -/
def FixedFlowSystem.regulatedCouplingCoefficient {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) {n : ℕ}
    (labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (last : CurvatureJetPolynomial.invariantAlgebra G)
    (output : LocalMonomial G) (loop order : ℕ) (Λ0 : ℝ)
    (r : OPE.RelativeSpace n) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => S.regulatedInvariantCoefficient labels last output loop g Λ0 r) 0

/-- These hypotheses ensure every derivative and compact-test integral used
in the prescribed limit is legitimate. They are explicit mathematical
conditions on S, not arbitrary coefficient or "renormalized" predicates. -/
structure FixedFlowSystem.CoefficientRegularity {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) : Prop where
  coupling_smooth : ∀ n labels last (output : LocalMonomial G) loop Λ0
      (r : OPE.RelativeSpace n), S.referenceScale.val < Λ0 →
    (∀ i, r i ≠ 0) → (∀ i j, i ≠ j → r i ≠ r j) →
      ContDiff ℝ ∞ (fun g : ℝ => S.regulatedInvariantCoefficient labels last output loop g Λ0 r)
  test_integrable : ∀ n labels last (output : LocalMonomial G) loop order Λ0
      (f : OPE.RelativeTest n), S.referenceScale.val < Λ0 → OPE.MultiOffDiagonal f →
    Integrable (fun r => S.regulatedCouplingCoefficient labels last output loop order Λ0 r * f r)

/-- The UV limit is fixed on every noncoincident compact test. It is not an
existential choice of "predictions" unrelated to the same group/action flow.
Local contact extensions may differ only within the separately prescribed
Ward-compatible finite local renormalization freedom. -/
def FixedFlowSystem.IsCoefficientLimit {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) {n : ℕ}
    (labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (last : CurvatureJetPolynomial.invariantAlgebra G) (output : LocalMonomial G)
    (loop order : ℕ) (E : OPE.MultiDistribution n) : Prop :=
  S.CoefficientRegularity ∧ OPE.IsLocalMultiDistribution E ∧
  ∀ f : OPE.RelativeTest n, OPE.MultiOffDiagonal f →
    Tendsto (fun Λ0 => ∫ r, S.regulatedCouplingCoefficient labels last output loop order Λ0 r * f r)
      atTop (nhds (E f))

/-- The generated limit is unique where the perturbative OPE is defined;
contact extensions are deliberately not declared unique by this lemma. -/
theorem FixedFlowSystem.IsCoefficientLimit.agree_offDiagonal
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    {last : CurvatureJetPolynomial.invariantAlgebra G} {output : LocalMonomial G}
    {loop order : ℕ} {E E' : OPE.MultiDistribution n}
    (hE : S.IsCoefficientLimit labels last output loop order E)
    (hE' : S.IsCoefficientLimit labels last output loop order E')
    (f : OPE.RelativeTest n) (hf : OPE.MultiOffDiagonal f) : E f = E' f :=
  tendsto_nhds_unique (hE.2.2 f hf) (hE'.2.2 f hf)

end YangMills.PerturbativeFlow
