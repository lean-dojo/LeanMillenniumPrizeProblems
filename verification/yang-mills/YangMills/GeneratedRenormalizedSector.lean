import YangMills.LocalWardOPEStressBinding
import YangMills.GeneratedScaleNormalization
import YangMills.GeneratedVacuumWordMatching

/-!
# One generated renormalized Yang--Mills sector: assembly fragment

This fixes the remaining prediction arguments to the same computed CS/flow
system. Beta is its finite loop assembly; physical gamma is its actual
classical-basis mixing conjugated by the SAME Wick maps as the OPE and
vacuum-word continuation. The gamma equation is required at ALL subtraction
scales: a comparison only at the reference scale cannot justify homogeneous
RG evolution in the presence of dimensionful lower-degree mixing.

The compatible homogeneous/vacuum-subtracted reference presentation is an
auxiliary scheme choice whose adequacy needs a source-equivalence theorem.
This declaration is not full-problem admission or an existence proof. The
classical BV, Legendre, scale-insertion and cited-standard fidelity work is
not discharged merely by writing this concrete simultaneous relation.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {QFT : WightmanData H} {C : RenormalizedCompositeMap QFT G}

/-- Same Wick substitutions for the generated OPE coefficients, physical
mixing matrices and actual vacuum-word UV matching. -/
def MultiContinuationWithRotations {basis : OPE.FilteredBasis G}
    {mu : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : ℕ → basis.Index → basis.Index → ℂ}
    {coeff : OPE.MultiCoefficients basis} {physical : ℕ → OPE.MultiCoefficients basis}
    (X : RG.ExhaustiveMatching basis C mu betaSeries gammaSeries
      (RG.pairFromMulti coeff) (fun k => RG.pairFromMulti (physical k)))
    (euclidean : ℕ → OPE.MultiCoefficients basis)
    (rotation : (D : ℕ) → Wick.LabelRotation (fun i => basis.label (X.index D i))) : Prop :=
  ∃ raw : ℕ → OPE.MultiCoefficients basis,
    (∀ order n inputs last output, Nonempty (Wick.MultiAnalyticContinuation
      (euclidean order n inputs last output) (raw order n inputs last output))) ∧
    ∀ D order n inputs last output (test : OPE.RelativeTest n), HasCompactSupport test →
      physical order n (fun r => X.index D (inputs r)) (X.index D last) (X.index D output) test =
        Wick.rotateMultiPairing (rotation D)
          (fun is j k => raw order n (fun r => X.index D (is r)) (X.index D j) (X.index D k))
          inputs last output test

/-- All central objects now belong to one actual group, action prescription,
local Ward family, physical composite map, stress tensor and RG system.
There are no independently supplied Euclidean or beta predictions. Gamma's
witness entries are fixed on every finite sector by the computed all-scale
CS mixing and the prescribed tensor Wick substitution. -/
structure GeneratedRenormalizedSector {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S)
    (basis : OPE.FilteredBasis G) (generated : LocalWardCoefficientFamily family basis)
    (normalization : GeneratedScaleNormalization family) (kernels : OPE.MultiKernels C)
    (coeff : OPE.MultiCoefficients basis) (physical : ℕ → OPE.MultiCoefficients basis)
    (T : StressTensorData QFT G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) where
  gammaSeries : ℕ → basis.Index → basis.Index → ℂ
  correspondence : C.Compatible
  physical_ope : OPE.WeakMultiExpansion kernels basis S.referenceScale coeff
  matching : RG.ExhaustiveMatching basis C S.referenceScale normalization.betaSeries gammaSeries
    (RG.pairFromMulti coeff) (fun k => RG.pairFromMulti (physical k))
  rotation : (D : ℕ) → Wick.LabelRotation (fun i => basis.label (matching.index D i))
  generated_gamma_all_scales : ∀ mu : RenormalizationScale, ∀ D order output input,
    gammaSeries order (matching.index D output) (matching.index D input) =
      rotateGammaSeries (rotation D)
        (fun k i j => normalization.euclideanGammaSeries basis mu k
          (matching.index D i) (matching.index D j)) order output input
  coefficient_continuation : MultiContinuationWithRotations matching
    (generated.data S.referenceScale).assembled rotation
  coefficient_matching : ∀ D, RG.AllOrderMultiMatch (matching.frame D)
    (fun n inputs last output => coeff n (fun r => matching.index D (inputs r))
      (matching.index D last) (matching.index D output))
    (fun k n inputs last output => physical k n (fun r => matching.index D (inputs r))
      (matching.index D last) (matching.index D output))
  vacuumContinuation : PhysicalWords.VacuumWordContinuation kernels
  actual_word_matching : PhysicalWords.GeneratedVacuumWordBridge family basis kernels
    vacuumContinuation matching rotation
  same_stress : RG.FamilyStressMatched matching form T curvatureSquare
  stressRepresentative : QuantumStressRepresentative G
  stressRegular : ℝ → Fin 4 → Fin 4 → ℕ → Fin (matching.count 4) → ℝ
  stressExactRegular : ℝ → Fin 4 → Fin 4 → Fin (matching.count 4) → ℝ
  generated_stress : GeneratedStressNormalization e (S.insertions S.referenceScale.val)
    (S.oversubtractions S.referenceScale.val) (family.continuum S.referenceScale)
    (family.ward S.referenceScale) (family.singleTransport S.referenceScale)
    (family.lift S.referenceScale) stressRepresentative
    (stressDictionaryFromSector matching stressRegular stressExactRegular) T
  same_stress_rg : (stressDictionaryFromSector matching stressRegular stressExactRegular).SameStressRG
    (matching.frame 4) T

/-- Forgetting the added CS/word/rotation constraints recovers the previous
same-field OPE/stress fragment with exactly the same objects and coefficients. -/
theorem GeneratedRenormalizedSector.localWardOPEStress
    {form : InvariantForm G} {e : ColorFrame form} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} {basis : OPE.FilteredBasis G}
    {generated : LocalWardCoefficientFamily family basis}
    {normalization : GeneratedScaleNormalization family} {kernels : OPE.MultiKernels C}
    {coeff : OPE.MultiCoefficients basis} {physical : ℕ → OPE.MultiCoefficients basis}
    {T : StressTensorData QFT G C} {curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G}
    (sector : GeneratedRenormalizedSector family basis generated normalization kernels
      coeff physical T curvatureSquare) :
    LocalWardOPEStressConditions family basis generated kernels normalization.betaSeries
      sector.gammaSeries coeff physical T curvatureSquare := by
  refine ⟨sector.correspondence, sector.physical_ope, sector.matching, sector.same_stress, ?_,
    sector.coefficient_matching, sector.stressRepresentative, sector.stressRegular,
    sector.stressExactRegular, sector.generated_stress, sector.same_stress_rg⟩
  obtain ⟨raw, hraw, hrotate⟩ := sector.coefficient_continuation
  refine ⟨raw, hraw, ?_⟩
  intro D
  exact ⟨sector.rotation D, hrotate D⟩

end YangMills.PerturbativeFlow
