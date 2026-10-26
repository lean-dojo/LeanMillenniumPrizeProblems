import Problems.YangMills.CohomologicalScaleInsertion
import Problems.YangMills.LocalWardFlowFamily
import Problems.YangMills.InvariantBasisCoordinates
import Problems.YangMills.RenormalizationGroup

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Same-engine CS normalization and finite physical RG series

Beta and operator mixing are bound by the full computed scale-insertion
residuals of the SAME action, corrected insertions and generated quantum Q.
Their coupling/loop grading makes setting hbar=1 coefficientwise finite.
Mixing outputs use unique actual classical basis coordinates; quantum
injectivity is neither required nor inferred. Wick rotation conjugates the
Euclidean column-label matrix before comparison with physical RG frames.
The scale-insertion/Legendre/cohomology fidelity theorems remain obligations.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Outside positive scales the reference value is merely a total extension;
all CS derivatives and endpoint conditions use the positive domain. -/
def positiveScaleExtension {alpha : Type*} (reference : RenormalizationScale)
    (f : RenormalizationScale → alpha) (mu : ℝ) : alpha :=
  if h : 0 < mu then f ⟨mu, h⟩ else f reference

/-- Full same-prescription scale-insertion normalization. No raw projected
bare-coupling formula is promoted to a physical beta function here. -/
structure GeneratedScaleNormalization {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S) where
  beta : ScaleInsertion.ScalarCoefficients
  fields : ScaleInsertion.FieldCoefficients
  actionPrimitive : ScaleInsertion.LocalScalePrimitive G 4 2
  mixing : ScaleInsertion.CompositeMixing G
  primitive : (p : InvariantInsertionLabel G) →
    ScaleInsertion.LocalScalePrimitive G (intrinsicEngineeringDimension p) 0
  beta_graph_order : ∀ order loop, order < 2 * loop + 1 → beta order loop = 0
  fields_graph_order : ∀ order loop, order < 2 * loop → fields order loop = ⟨0,0,0,0⟩
  mixing_graph_order : ∀ mu order loop p, 0 < mu → order < 2 * loop →
    mixing.coefficient mu order loop p = 0
  same_scale_insertion : ScaleInsertion.CompositeCSConditions e
    (positiveScaleExtension S.referenceScale (fun scale => (family.singleTransport scale).coefficient))
    S.background S.insertions
    (positiveScaleExtension S.referenceScale family.ward)
    (positiveScaleExtension S.referenceScale family.lift)
    beta fields actionPrimitive mixing primitive

/-- Every loop above the finite range is zero by the actual g-adic guard. -/
def GeneratedScaleNormalization.betaSeries {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (order : ℕ) : ℝ :=
  ∑ loop ∈ Finset.range (order + 1), N.beta order loop

/-- Euclidean mixing matrix: column=input, row=output. Finite raw polynomial
labels are resolved in the SAME actual coherent classical basis, including
identities on connections but not a physical cohomology isomorphism. -/
def GeneratedScaleNormalization.euclideanGammaLoop {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (basis : OPE.FilteredBasis G)
    (mu : RenormalizationScale) (order loop : ℕ) (output input : basis.Index) : ℝ :=
  (N.mixing.coefficient mu.val order loop (basis.label input)).sum fun p c =>
    c * basis.classicalCoordinates p output

def GeneratedScaleNormalization.euclideanGammaSeries {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (basis : OPE.FilteredBasis G)
    (mu : RenormalizationScale) (order : ℕ) (output input : basis.Index) : ℂ :=
  ((∑ loop ∈ Finset.range (order / 2 + 1),
    N.euclideanGammaLoop basis mu order loop output input : ℝ) : ℂ)

theorem GeneratedScaleNormalization.beta_excluded_loop
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (order loop : ℕ) (h : order < loop) : N.beta order loop = 0 := by
  apply N.beta_graph_order
  omega

theorem GeneratedScaleNormalization.gamma_excluded_loop
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale) (order loop : ℕ)
    (output input : basis.Index) (h : order / 2 < loop) :
    N.euclideanGammaLoop basis mu order loop output input = 0 := by
  unfold euclideanGammaLoop
  rw [N.mixing_graph_order mu.val order loop (basis.label input) mu.property (by omega)]
  simp

/-- Physical column-label mixing is W gamma_E W^-1, with the same actual
label Wick substitution used for all incoming/outgoing OPE coefficients. -/
def rotateGammaSeries {n : ℕ} {labels : Fin n → InvariantInsertionLabel G}
    (W : Wick.LabelRotation labels) (gamma : ℕ → Fin n → Fin n → ℂ)
    (order : ℕ) (output input : Fin n) : ℂ :=
  ∑ a : Fin n, ∑ b : Fin n,
    W.map (Pi.single a 1) output * gamma order a b * W.map.symm (Pi.single input 1) b

end YangMills.PerturbativeFlow
