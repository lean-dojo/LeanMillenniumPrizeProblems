import Problems.YangMills.LocalWardFlowFamily
import Problems.YangMills.GeneratedMultiMatching
import Problems.YangMills.StressRenormalizationGroup

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# All-arity same-field OPE and stress binding for the local Ward family

The coefficient generator is fixed by the actual local Ward/flow family at
all normalization scales. The physical OPE and stress tensor use one common
exhaustive RG system. Stress normalization uses precisely its dimension-four
sector, not a second gamma matrix or an unrelated stress dictionary.
Beta/gamma still need the same-engine scale-insertion authorization; this is
an assembly fragment, not an admitted full Yang--Mills existence target.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {QFT : WightmanData H} {C : RenormalizedCompositeMap QFT G}

/-- The source stress dictionary uses exactly all labels below degree five
in the common physical matching family. Its numerator coefficients have
quantum jets; no equality to an all-order traceless classical label appears. -/
def stressDictionaryFromSector {basis : OPE.FilteredBasis G} {mu : RenormalizationScale}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → basis.Index → basis.Index → ℂ}
    {coeff : OPE.MultiCoefficients basis} {physical : ℕ → OPE.MultiCoefficients basis}
    (X : RG.ExhaustiveMatching basis C mu betaSeries gammaSeries
      (RG.pairFromMulti coeff) (fun k => RG.pairFromMulti (physical k)))
    (regular : ℝ → Fin 4 → Fin 4 → ℕ → Fin (X.count 4) → ℝ)
    (exactRegular : ℝ → Fin 4 → Fin 4 → Fin (X.count 4) → ℝ) : StressSourceDictionary G :=
  ⟨X.count 4, fun i => basis.label (X.index 4 i), regular, exactRegular⟩

def LocalWardOPEStressConditions {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S) (basis : OPE.FilteredBasis G)
    (generated : LocalWardCoefficientFamily family basis) (kernels : OPE.MultiKernels C)
    (betaSeries : ℕ → ℝ) (gammaSeries : ℕ → basis.Index → basis.Index → ℂ)
    (coeff : OPE.MultiCoefficients basis) (physical : ℕ → OPE.MultiCoefficients basis)
    (T : StressTensorData QFT G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  C.Compatible ∧ OPE.WeakMultiExpansion kernels basis S.referenceScale coeff ∧
  ∃ X : RG.ExhaustiveMatching basis C S.referenceScale betaSeries gammaSeries
      (RG.pairFromMulti coeff) (fun k => RG.pairFromMulti (physical k)),
    RG.FamilyStressMatched X form T curvatureSquare ∧
    RG.MultiFamilyContinuation X (generated.data S.referenceScale).assembled ∧
    (∀ D, RG.AllOrderMultiMatch (X.frame D)
      (fun n inputs last output => coeff n (fun r => X.index D (inputs r))
        (X.index D last) (X.index D output))
      (fun k n inputs last output => physical k n (fun r => X.index D (inputs r))
        (X.index D last) (X.index D output))) ∧
    ∃ stress : QuantumStressRepresentative G,
    ∃ regular : ℝ → Fin 4 → Fin 4 → ℕ → Fin (X.count 4) → ℝ,
    ∃ exactRegular : ℝ → Fin 4 → Fin 4 → Fin (X.count 4) → ℝ,
      let dict := stressDictionaryFromSector X regular exactRegular
      GeneratedStressNormalization e (S.insertions S.referenceScale.val)
        (S.oversubtractions S.referenceScale.val) (family.continuum S.referenceScale)
        (family.ward S.referenceScale) (family.singleTransport S.referenceScale)
        (family.lift S.referenceScale) stress dict T ∧
      dict.SameStressRG (X.frame 4) T

/-- The concrete local-Ward assembly retains the earlier same-field
matching relation with exactly the generated Euclidean series. -/
theorem localWardOPEStress_implies_generatedMulti
    {form : InvariantForm G} {e : ColorFrame form} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} {basis : OPE.FilteredBasis G}
    {generated : LocalWardCoefficientFamily family basis} {kernels : OPE.MultiKernels C}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → basis.Index → basis.Index → ℂ}
    {coeff : OPE.MultiCoefficients basis} {physical : ℕ → OPE.MultiCoefficients basis}
    {T : StressTensorData QFT G C} {curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G}
    (h : LocalWardOPEStressConditions family basis generated kernels betaSeries gammaSeries
      coeff physical T curvatureSquare) :
    GeneratedMultiSectorConditions S (family.lift S.referenceScale)
      (family.continuum S.referenceScale) (family.ward S.referenceScale)
      (family.singleTransport S.referenceScale) kernels basis (generated.data S.referenceScale)
      betaSeries gammaSeries coeff physical T curvatureSquare := by
  refine ⟨?_, h.1, h.2.1, ?_⟩
  · exact generated.compatible S.referenceScale
  · obtain ⟨X, hstress, hwick, hmatch, _⟩ := h.2.2
    exact ⟨X, hstress, hwick, hmatch⟩

end YangMills.PerturbativeFlow
