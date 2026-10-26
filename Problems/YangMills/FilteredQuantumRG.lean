import Problems.YangMills.GeneratedRenormalizedSector
import Problems.YangMills.ClassicalDilation
import Problems.YangMills.CenteredTraceAnomaly

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Filtered quantum RG with fixed generated scale-dependent mixing

Classical labels may be chosen homogeneous, as proved separately. Quantum
transport need only preserve the engineering filtration: lower-degree mixing
carries its actual subtraction-scale dependence. Canonical dilation is applied
AFTER transporting to the high scale; its factors therefore do not commute
past the triangular label transport. Formal gamma coefficients below are
computed from the same GeneratedScaleNormalization, never supplied anew.
-/
noncomputable section
open Filter
open scoped ContDiff BigOperators
namespace YangMills.FilteredRG
open Perturbative PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The running subtraction scale, fixed by the same reference scale. -/
def runningScale (reference : RenormalizationScale) (t : ℝ) : RenormalizationScale :=
  ⟨reference.val * Real.exp t, mul_pos reference.property (Real.exp_pos t)⟩

structure Frame {n : ℕ} (labels : Fin n → InvariantInsertionLabel G)
    (reference : RenormalizationScale) (betaSeries : ℕ → ℝ)
    (gammaSeries : RenormalizationScale → ℕ → Fin n → Fin n → ℂ) where
  running : RG.RunningCoupling betaSeries
  gamma : ℝ → ℝ → Fin n → Fin n → ℂ
  gamma_smooth : ∀ i j, ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => gamma z.1 z.2 i j) (Set.Ioi 0 ×ˢ Set.univ)
  gamma_jet : ∀ mu : RenormalizationScale, ∀ i j,
    RG.HasPerturbativeJet (fun g => gamma mu.val g i j) (fun k => gammaSeries mu k i j)
  transport : ℝ → (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)
  initial : ∀ v, transport 0 v = v
  filtered : ∀ t i j, OPE.dimension (labels j) < OPE.dimension (labels i) →
    transport t (Pi.single j 1) i = 0
  equation : ∀ t i j, 0 ≤ t →
    HasDerivAt (fun s => transport s (Pi.single j 1) i)
      (∑ k : Fin n, gamma (runningScale reference t).val (running.coupling t) i k *
        transport t (Pi.single j 1) k) t

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {C : RenormalizedCompositeMap Q G}

def Realizes {m : ℕ} {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    (F : Frame labels reference betaSeries gammaSeries) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ i f v,
    C.field reference (labels i) f v = ∑ j : Fin m,
      (F.transport t (Pi.single i 1) j) •
        C.field (runningScale reference t) (labels j) f v

/-- D^-1 R C(R^-1 D)^tensor. The scaling exponent uses the EXTERNAL
incoming/output labels: R transports before canonical normalization. -/
def strippedMultiPairing {m : ℕ} {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    (F : Frame labels reference betaSeries gammaSeries)
    (coeff : (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (scale : ℝ) (n : ℕ) (inputs : Fin n → Fin m) (last output : Fin m)
    (test : OPE.RelativeTest n) : ℂ :=
  ∑ is : Fin n → Fin m, ∑ j : Fin m, ∑ k : Fin m,
    (((scale ^ ((∑ r : Fin n, (OPE.dimension (labels (inputs r)) : ℤ)) +
      OPE.dimension (labels last) - OPE.dimension (labels output)) : ℝ)) : ℂ) *
      F.transport (RG.time scale) (Pi.single k 1) output *
      (∏ r : Fin n, (F.transport (RG.time scale)).symm (Pi.single (inputs r) 1) (is r)) *
      (F.transport (RG.time scale)).symm (Pi.single last 1) j *
      coeff n is j k (OPE.dilateRelative scale test)

def AllOrderMultiMatch {m : ℕ} {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    (F : Frame labels reference betaSeries gammaSeries)
    (coeff : (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (physical : ℕ → (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n) : Prop :=
  (∀ n inputs last output, OPE.IsLocalMultiDistribution (coeff n inputs last output)) ∧
  (∀ order n inputs last output, OPE.IsLocalMultiDistribution (physical order n inputs last output)) ∧
  ∀ n, 0 < n → ∀ inputs last output (test : OPE.RelativeTest n), OPE.MultiOffDiagonal test →
    ∀ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ scale : ℝ, 0 < scale → scale < delta →
      ‖strippedMultiPairing F coeff scale n inputs last output test -
        ∑ k ∈ Finset.range (N+1), ((F.running.coupling (RG.time scale) : ℂ)^k) *
          physical k n inputs last output test‖ ≤ epsilon * F.running.coupling (RG.time scale)^N

/-- The SAME actual vacuum word, first transported to the running scale,
then canonically normalized in the external Euclidean label degrees. -/
def strippedVacuumWord {m : ℕ} {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} (V : PhysicalWords.VacuumWordContinuation K)
    (F : Frame labels reference betaSeries gammaSeries) (rotation : Wick.LabelRotation labels)
    (scale : ℝ) (n : ℕ) (inputs : Fin (n+1) → Fin m)
    (test : PhysicalWords.WordTest (n+1)) : ℂ :=
  ∑ indices : Fin (n+1) → Fin m,
    ((scale ^ (∑ r : Fin (n+1), OPE.dimension (labels (inputs r))) : ℝ) : ℂ) *
      (∏ r : Fin (n+1),
        ((F.transport (RG.time scale)).symm (rotation.map (Pi.single (inputs r) 1))) (indices r)) *
      V.scaledEuclideanObservation n reference (fun r => labels (indices r)) scale test

def AllOrderVacuumWordMatch {m : ℕ} {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} (V : PhysicalWords.VacuumWordContinuation K)
    (F : Frame labels reference betaSeries gammaSeries) (rotation : Wick.LabelRotation labels)
    (series : ℕ → (n : ℕ) → (Fin (n+1) → Fin m) → PhysicalWords.WordDistribution (n+1)) : Prop :=
  ∀ n, 0 < n → ∀ inputs (test : PhysicalWords.WordTest (n+1)),
    PhysicalWords.OrderedEuclideanTest test → ∀ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ scale : ℝ, 0 < scale → scale < delta →
      ‖strippedVacuumWord V F rotation scale n inputs test -
        ∑ k ∈ Finset.range (N+1), ((F.running.coupling (RG.time scale) : ℂ)^k) *
          series k n inputs test‖ ≤ epsilon * F.running.coupling (RG.time scale)^N

/-- No free beta/gamma prediction inputs: every finite sector's gamma jet is
computed from the SAME actual generated CS mixing at the running scale. -/
structure GeneratedMatching {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S)
    (basis : OPE.FilteredBasis G) (normalization : GeneratedScaleNormalization family)
    (coeff : OPE.MultiCoefficients basis) (physical : ℕ → OPE.MultiCoefficients basis) where
  classical_homogeneous : ∀ i, (basis.label i).val.EngineeringHomogeneous
    (OPE.dimension (basis.label i))
  running : RG.RunningCoupling normalization.betaSeries
  count : ℕ → ℕ
  index : (D : ℕ) → Fin (count D) → basis.Index
  index_active : ∀ D i, index D i ∈ basis.active D
  index_injective : ∀ D, Function.Injective (index D)
  index_surjective : ∀ D i, i ∈ basis.active D → ∃ j, index D j = i
  rotation : (D : ℕ) → Wick.LabelRotation (fun i => basis.label (index D i))
  frame : (D : ℕ) → Frame (fun i => basis.label (index D i)) S.referenceScale
    normalization.betaSeries (fun mu order => rotateGammaSeries (rotation D)
      (fun k i j => normalization.euclideanGammaSeries basis mu k (index D i) (index D j)) order)
  common_running : ∀ D, (frame D).running = running
  common_gamma : ∀ D E i j a b, index D i = index E a → index D j = index E b →
    ∀ mu g, (frame D).gamma mu g i j = (frame E).gamma mu g a b
  actual_transport : ∀ D, Realizes (C := C) (frame D)
  coherent_transport : ∀ D E i j a b, index D i = index E a → index D j = index E b →
    ∀ t, (frame D).transport t (Pi.single j 1) i = (frame E).transport t (Pi.single b 1) a
  coefficient_matching : ∀ D, AllOrderMultiMatch (frame D)
    (fun n inputs last output => coeff n (fun r => index D (inputs r)) (index D last) (index D output))
    (fun k n inputs last output => physical k n (fun r => index D (inputs r))
      (index D last) (index D output))

/-- Coordinate continuation uses the same fixed rotations as gamma and
actual word transport. The raw Minkowski boundary family is globally shared. -/
def GeneratedContinuation {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S} {basis : OPE.FilteredBasis G}
    {normalization : GeneratedScaleNormalization family} {coeff : OPE.MultiCoefficients basis}
    {physical : ℕ → OPE.MultiCoefficients basis}
    (X : GeneratedMatching (C := C) family basis normalization coeff physical)
    (generated : LocalWardCoefficientFamily family basis) : Prop :=
  ∃ raw : ℕ → OPE.MultiCoefficients basis,
    (∀ order n inputs last output, Nonempty (Wick.MultiAnalyticContinuation
      ((generated.data S.referenceScale).assembled order n inputs last output)
      (raw order n inputs last output))) ∧
    ∀ D order n inputs last output (test : OPE.RelativeTest n), HasCompactSupport test →
      physical order n (fun r => X.index D (inputs r)) (X.index D last) (X.index D output) test =
        Wick.rotateMultiPairing (X.rotation D)
          (fun is j k => raw order n (fun r => X.index D (is r)) (X.index D j) (X.index D k))
          inputs last output test

def GeneratedWordBridge {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S} {basis : OPE.FilteredBasis G}
    {normalization : GeneratedScaleNormalization family} {coeff : OPE.MultiCoefficients basis}
    {physical : ℕ → OPE.MultiCoefficients basis} {K : OPE.MultiKernels C}
    (X : GeneratedMatching (C := C) family basis normalization coeff physical)
    (V : PhysicalWords.VacuumWordContinuation K) : Prop :=
  ∀ D, AllOrderVacuumWordMatch V (X.frame D) (X.rotation D)
    (fun order n inputs => PhysicalWords.generatedInvariantWord family S.referenceScale order (n+1)
      (fun r => basis.label (X.index D (inputs r))))

/-- A scale-dependent stress dictionary is constrained by the SAME local
quantum representatives at each scale; no new stress predictions are data. -/
structure GeneratedStressFamily {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S) {m : ℕ}
    (labels : Fin m → InvariantInsertionLabel G) where
  representative : RenormalizationScale → QuantumStressRepresentative G
  regular : RenormalizationScale → ℝ → Fin 4 → Fin 4 → ℕ → Fin m → ℝ
  exactRegular : RenormalizationScale → ℝ → Fin 4 → Fin 4 → Fin m → ℝ
  joint_smooth : ∀ mu nu i, ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => positiveScaleExtension S.referenceScale
      (fun scale => exactRegular scale z.2 mu nu i) z.1) (Set.Ioi 0 ×ˢ Set.univ)
  same_generated : ∀ scale : RenormalizationScale,
    (representative scale).Compatible e (family.ward scale) ∧
    (representative scale).LimitCompatible (S.insertions scale.val) (family.continuum scale) ∧
    (StressSourceDictionary.mk m labels (regular scale) (exactRegular scale)).Compatible
      (family.lift scale) (representative scale)

def GeneratedStressFamily.dictionary {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S} {m : ℕ}
    {labels : Fin m → InvariantInsertionLabel G}
    (A : GeneratedStressFamily family labels) (mu : RenormalizationScale) : StressSourceDictionary G :=
  ⟨m,labels,A.regular mu,A.exactRegular mu⟩

/-- Both explicit subtraction-scale and coupling derivatives contribute to
scale independence. Multiplying by g clears the fixed source-label g^-2 pole. -/
structure GeneratedStressFamily.SameStressRG {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S} {m : ℕ}
    {labels : Fin m → InvariantInsertionLabel G}
    {betaSeries : ℕ → ℝ} {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    (A : GeneratedStressFamily family labels)
    (F : Frame labels S.referenceScale betaSeries gammaSeries)
    (T : StressTensorData Q G C) : Prop where
  reference_scale : T.scale = S.referenceScale
  coupling : T.coupling.val = F.running.coupling 0
  reference_binding : (A.dictionary S.referenceScale).PhysicalBinding T
  actual_transport : Realizes (C := C) F
  numerator_transport : ∀ mu nu t, 0 ≤ t →
    ((F.running.coupling 0 ^ 2 : ℝ) : ℂ) •
      (fun i => (A.exactRegular (runningScale S.referenceScale t) (F.running.coupling t) mu nu i : ℂ)) =
    ((F.running.coupling t ^ 2 : ℝ) : ℂ) •
      F.transport t (fun i => (A.exactRegular S.referenceScale (F.running.coupling 0) mu nu i : ℂ))
  differential : ∀ mu nu t, 0 ≤ t → ∀ i,
    let scale := runningScale S.referenceScale t
    let g := F.running.coupling t
    (((g * scale.val * deriv (fun s : ℝ => positiveScaleExtension S.referenceScale
        (fun scale => A.exactRegular scale g mu nu i) s) scale.val +
      g * F.running.beta g * deriv (fun h : ℝ => A.exactRegular scale h mu nu i) g -
      2 * F.running.beta g * A.exactRegular scale g mu nu i : ℝ)) : ℂ) =
        (g : ℂ) * ∑ j : Fin m, F.gamma scale.val g i j * (A.exactRegular scale g mu nu j : ℂ)
  same_field : ∀ t : ℝ, 0 ≤ t → ∀ mu nu f v,
    T.field mu nu f v =
      (((F.running.coupling t)⁻¹ ^ 2 : ℝ) : ℂ) •
        ∑ i : Fin m, (A.exactRegular (runningScale S.referenceScale t)
          (F.running.coupling t) mu nu i : ℂ) •
          C.field (runningScale S.referenceScale t) (labels i) f v

/-- Reviewable filtered replacement fragment. It retains the SAME actual
QFT/C, generated family, local OPE, Wick rotations, stress charges and trace
anomaly, while making no homogeneous-quantum-scheme availability demand. -/
structure GeneratedSector {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S)
    (basis : OPE.FilteredBasis G) (generated : LocalWardCoefficientFamily family basis)
    (normalization : GeneratedScaleNormalization family) (K : OPE.MultiKernels C)
    (coeff : OPE.MultiCoefficients basis) (physical : ℕ → OPE.MultiCoefficients basis)
    (T : StressTensorData Q G C) (curvatureSquare : InvariantInsertionLabel G) where
  correspondence : C.Compatible
  physical_ope : OPE.WeakMultiExpansion K basis S.referenceScale coeff
  matching : GeneratedMatching (C := C) family basis normalization coeff physical
  continuation : GeneratedContinuation matching generated
  vacuumContinuation : PhysicalWords.VacuumWordContinuation K
  actual_words : GeneratedWordBridge matching vacuumContinuation
  same_stress : T.Compatible ∧ T.traceForm = form ∧ T.scale = S.referenceScale ∧
    T.coupling.val = matching.running.coupling 0 ∧
    T.HasCenteredTraceAnomaly (matching.running.beta (matching.running.coupling 0)) curvatureSquare
  stressFamily : GeneratedStressFamily family (fun i => basis.label (matching.index 4 i))
  generated_stress_reference : GeneratedStressNormalization e (S.insertions S.referenceScale.val)
    (S.oversubtractions S.referenceScale.val) (family.continuum S.referenceScale)
    (family.ward S.referenceScale) (family.singleTransport S.referenceScale)
    (family.lift S.referenceScale) (stressFamily.representative S.referenceScale)
    (stressFamily.dictionary S.referenceScale) T
  same_stress_rg : stressFamily.SameStressRG (matching.frame 4) T

end YangMills.FilteredRG
