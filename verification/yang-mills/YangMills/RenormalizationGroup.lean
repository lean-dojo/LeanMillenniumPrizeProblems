import YangMills.OperatorProductExpansion
import YangMills.StressTensor
import YangMills.WickRotation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Running coupling, operator transport, and all-order weak UV matching

This file fixes the mathematical relation to a GIVEN perturbative series.
It does not make that series a proof-author-chosen definition of YM: the
renormalized graded YM generator, Ward identities and its coefficient
extraction must supply it. That generator is still incomplete in this library.

Exact coefficient distributions and smooth beta/gamma completions may be
witnesses. All their perturbative jets must agree to every finite order with
the fixed series; uniqueness of a nonperturbative resummation is not imposed.
The conventions below act on LABEL VECTORS, not arrays of field components.
-/
noncomputable section
open Filter
open scoped ContDiff
namespace YangMills.RG
abbrev Distribution := OPE.CoefficientDistribution

def time (scale : ℝ) : ℝ := Real.log scale⁻¹

/-- Explicit all-order expansion at g->0+, including the last retained order.
This relation is weaker than analyticity and permits flat corrections. -/
def HasPerturbativeJet (f : ℝ → ℂ) (series : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ,
    0 < g → g < δ →
      ‖f g - ∑ k ∈ Finset.range (N + 1), (g : ℂ) ^ k * series k‖ ≤ ε * g ^ N

/-- The series argument must come from the fixed perturbative calculation.
The actual running coupling is positive and tends to zero at high RG time. -/
structure RunningCoupling (betaSeries : ℕ → ℝ) where
  beta : ℝ → ℝ
  beta_smooth : ContDiff ℝ ∞ beta
  beta_jet : HasPerturbativeJet (fun g => (beta g : ℂ)) (fun k => (betaSeries k : ℂ))
  coupling : ℝ → ℝ
  initial_positive : 0 < coupling 0
  positive : ∀ t : ℝ, 0 ≤ t → 0 < coupling t
  equation : ∀ t : ℝ, 0 ≤ t → HasDerivAt coupling (beta (coupling t)) t
  ultraviolet : Tendsto coupling atTop (nhds 0)

/-- A finite homogeneous RG sector of ACTUAL classical observable labels.
The degree is derived from the quotient filtration, never assigned by witnesses. -/
structure Frame {G : CompactSimpleGaugeGroup} {n : ℕ}
    (labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (betaSeries : ℕ → ℝ) (gammaSeries : ℕ → Fin n → Fin n → ℂ) where
  running : RunningCoupling betaSeries
  gamma : ℝ → Fin n → Fin n → ℂ
  gamma_smooth : ∀ i j, ContDiff ℝ ∞ (fun g => gamma g i j)
  gamma_jet : ∀ i j, HasPerturbativeJet (fun g => gamma g i j) (fun k => gammaSeries k i j)
  transport : ℝ → (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)
  initial : ∀ v, transport 0 v = v
  /-- Equal-degree blocks are a homogeneous-scheme PRESENTATION.
  More general filtered changes need dimensionful scale factors. This condition
  is not silently claimed equivalent to all admissible schemes. -/
  homogeneous : ∀ t i j, OPE.dimension (labels i) ≠ OPE.dimension (labels j) →
    transport t (Pi.single j 1) i = 0
  /-- With Q_mu(v)=Q_(mu exp t)(R_t v), label transport obeys R'=gamma R. -/
  equation : ∀ t i j, 0 ≤ t →
    HasDerivAt (fun s => transport s (Pi.single j 1) i)
      (∑ k : Fin n, gamma (running.coupling t) i k * transport t (Pi.single j 1) k) t

/-- Component of R Cbar (R^-1 tensor R^-1), with
Cbar_(ij)^k = scale^(di+dj-dk) C_(ij)^k(scale r).
The explicit outgoing and incoming factors prevent a hidden transpose. -/
def strippedPairing {G : CompactSimpleGaugeGroup} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin n → Fin n → ℂ}
    (F : Frame labels betaSeries gammaSeries)
    (coeff : Fin n → Fin n → Fin n → Distribution)
    (scale : ℝ) (a b c : Fin n) (test : TestFunction) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    F.transport (time scale) (Pi.single k 1) c *
      (F.transport (time scale)).symm (Pi.single a 1) i *
      (F.transport (time scale)).symm (Pi.single b 1) j *
      (((scale ^ ((OPE.dimension (labels i) : ℤ) +
        OPE.dimension (labels j) - OPE.dimension (labels k)) : ℝ)) : ℂ) *
      coeff i j k (dilateTest scale test)

/-- Every finite-order remainder is small relative to the LAST retained
running-coupling power, weakly on compact tests away from collision. Fixed unit
configuration logarithms stay in `perturbative`; large-scale logarithms are in
the running system. A prescribed Laurent prefactor must be factored explicitly
before using this power-series normalization. -/
def AllOrderMatch {G : CompactSimpleGaugeGroup} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin n → Fin n → ℂ}
    (F : Frame labels betaSeries gammaSeries)
    (coeff : Fin n → Fin n → Fin n → Distribution)
    (perturbative : ℕ → Fin n → Fin n → Fin n → Distribution) : Prop :=
  (∀ a b c, OPE.IsLocalDistribution (coeff a b c)) ∧
  (∀ k a b c, OPE.IsLocalDistribution (perturbative k a b c)) ∧
  ∀ a b c (test : TestFunction), OPE.OffDiagonal test →
    ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ scale : ℝ,
    0 < scale → scale < δ →
      ‖strippedPairing F coeff scale a b c test -
        ∑ k ∈ Finset.range (N + 1),
          ((F.running.coupling (time scale) : ℂ) ^ k) * perturbative k a b c test‖ ≤
        ε * F.running.coupling (time scale) ^ N

/-- Finite scheme changes on LABELS: Q_new(v)=Q_old(Mv), hence
C_new=M^-1 C_old (M tensor M). All three slots refer to one basis change. -/
def schemeTransform {n : ℕ}
    (M : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
    (coeff : Fin n → Fin n → Fin n → Distribution)
    (a b c : Fin n) : Distribution :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    (M.symm (Pi.single k 1) c * M (Pi.single a 1) i * M (Pi.single b 1) j) • coeff i j k

/-- This is an ACTUAL operator identity for the same correspondence at both
scales, rather than a frame acting only on independent coefficient arrays. -/
def Realizes {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin n → Fin n → ℂ}
    (F : Frame labels betaSeries gammaSeries)
    (C : RenormalizedCompositeMap Q G) (μ : RenormalizationScale) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ i f v,
    C.field μ (labels i) f v = ∑ j : Fin n,
      (F.transport t (Pi.single i 1) j) •
        C.field ⟨μ.val * Real.exp t, mul_pos μ.property (Real.exp_pos t)⟩ (labels j) f v

/-- Coupled physical matching. The SAME coefficient distributions must also
enter `OPE.WeakExpansion` for these labels in an assembled specification.
One finite sector is insufficient: compatible exhaustive sectors and the
prescribed YM beta/gamma/OPE generator are still needed for a full target. -/
def PhysicalMatch {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin n → Fin n → ℂ}
    (F : Frame labels betaSeries gammaSeries) (C : RenormalizedCompositeMap Q G)
    (μ : RenormalizationScale) (coeff : Fin n → Fin n → Fin n → Distribution)
    (perturbative : ℕ → Fin n → Fin n → Fin n → Distribution) : Prop :=
  Realizes F C μ ∧ AllOrderMatch F coeff perturbative

/-- The trace/anomaly relation uses the SAME correspondence, reference scale,
action form, running coupling and beta completion, rather than independent
stress and RG data. The beta jets still need the fixed YM generator. -/
def StressMatched {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin n → Fin n → ℂ}
    (F : Frame labels betaSeries gammaSeries) {C : RenormalizedCompositeMap Q G}
    (B : InvariantForm G) (μ : RenormalizationScale)
    (T : StressTensorData Q G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  T.Compatible ∧ T.traceForm = B ∧ T.scale = μ ∧
  T.coupling.val = F.running.coupling 0 ∧ Realizes F C μ ∧
  T.HasTraceAnomaly (F.running.beta (F.running.coupling 0)) curvatureSquare

/-- Compatible exhaustive finite sectors of one classical filtered basis.
The exact coefficient family, formal series and actual C are shared by all
sectors. A trivial one-dimensional or empty frame cannot stand in for the
entire observable algebra. This still takes formal series as INPUTS; only a
completed fixed YM renormalization prescription can authorize those inputs. -/
structure ExhaustiveMatching {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
    (B : OPE.FilteredBasis G) (C : RenormalizedCompositeMap Q G)
    (μ : RenormalizationScale) (betaSeries : ℕ → ℝ)
    (gammaSeries : ℕ → B.Index → B.Index → ℂ)
    (coeff : B.Index → B.Index → B.Index → Distribution)
    (perturbative : ℕ → B.Index → B.Index → B.Index → Distribution) where
  running : RunningCoupling betaSeries
  count : ℕ → ℕ
  index : (D : ℕ) → Fin (count D) → B.Index
  index_active : ∀ D i, index D i ∈ B.active D
  index_injective : ∀ D, Function.Injective (index D)
  index_surjective : ∀ D i, i ∈ B.active D → ∃ j, index D j = i
  frame : ∀ D, Frame (fun i => B.label (index D i)) betaSeries
    (fun k i j => gammaSeries k (index D i) (index D j))
  common_running : ∀ D, (frame D).running = running
  common_gamma : ∀ D E i j a b, index D i = index E a → index D j = index E b →
    ∀ g, (frame D).gamma g i j = (frame E).gamma g a b
  actual_transport : ∀ D, Realizes (frame D) C μ
  coherent_transport : ∀ D E i j a b, index D i = index E a → index D j = index E b →
    ∀ t, (frame D).transport t (Pi.single j 1) i =
      (frame E).transport t (Pi.single b 1) a
  matching : ∀ D, AllOrderMatch (frame D)
    (fun a b c => coeff (index D a) (index D b) (index D c))
    (fun k a b c => perturbative k (index D a) (index D b) (index D c))

/-- A coordinate boundary family plus the fixed Wick map on every tensor
label sector produces the actual physical formal coefficient family. -/
def FamilyContinuation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
    {B : OPE.FilteredBasis G} {C : RenormalizedCompositeMap Q G}
    {μ : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : ℕ → B.Index → B.Index → ℂ}
    {coeff : B.Index → B.Index → B.Index → Distribution}
    {perturbative : ℕ → B.Index → B.Index → B.Index → Distribution}
    (X : ExhaustiveMatching B C μ betaSeries gammaSeries coeff perturbative)
    (euclidean : ℕ → B.Index → B.Index → B.Index → Distribution) : Prop :=
  ∃ raw : ℕ → B.Index → B.Index → B.Index → Distribution,
    (∀ k a b c, Nonempty (Wick.AnalyticContinuation (euclidean k a b c) (raw k a b c))) ∧
    ∀ D, ∃ W : Wick.LabelRotation (fun i => B.label (X.index D i)),
    ∀ k a b c (test : TestFunction), HasCompactSupport test →
      perturbative k (X.index D a) (X.index D b) (X.index D c) test =
        Wick.rotatePairing W
          (fun i j l => raw k (X.index D i) (X.index D j) (X.index D l)) a b c test

/-- Coupled relations, still taking the formal YM prediction series as inputs.
A completed fixed generator must authorize these inputs before admission. -/
def CoupledContinuumOPE {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
    {C : RenormalizedCompositeMap Q G} (K : OPE.PairKernels C)
    (B : OPE.FilteredBasis G) (μ : RenormalizationScale)
    (betaSeries : ℕ → ℝ) (gammaSeries : ℕ → B.Index → B.Index → ℂ)
    (coeff : B.Index → B.Index → B.Index → Distribution)
    (euclidean physical : ℕ → B.Index → B.Index → B.Index → Distribution) : Prop :=
  C.Compatible ∧ OPE.WeakBasisExpansion K B μ coeff ∧
  ∃ X : ExhaustiveMatching B C μ betaSeries gammaSeries coeff physical,
    FamilyContinuation X euclidean

/-- Same stress normalization for the common running system of ALL sectors. -/
def FamilyStressMatched {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
    {B : OPE.FilteredBasis G} {C : RenormalizedCompositeMap Q G}
    {μ : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : ℕ → B.Index → B.Index → ℂ}
    {coeff : B.Index → B.Index → B.Index → Distribution}
    {perturbative : ℕ → B.Index → B.Index → B.Index → Distribution}
    (X : ExhaustiveMatching B C μ betaSeries gammaSeries coeff perturbative)
    (form : InvariantForm G) (T : StressTensorData Q G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  T.Compatible ∧ T.traceForm = form ∧ T.scale = μ ∧
  T.coupling.val = X.running.coupling 0 ∧
  T.HasTraceAnomaly (X.running.beta (X.running.coupling 0)) curvatureSquare

/-- Assembled central RELATIONS, still parameterized by formal prediction data.
This is deliberately not a full Yang--Mills target: the Euclidean series and
beta/gamma series must be outputs of the unfinished fixed renormalization
prescription. One common exact coefficient family, correspondence and running
system links all sectors, the physical OPE and the same stress/Hamiltonian. -/
def CoupledSectorConditions {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
    {C : RenormalizedCompositeMap Q G} (K : OPE.PairKernels C)
    (B : OPE.FilteredBasis G) (μ : RenormalizationScale) (form : InvariantForm G)
    (betaSeries : ℕ → ℝ) (gammaSeries : ℕ → B.Index → B.Index → ℂ)
    (coeff : B.Index → B.Index → B.Index → Distribution)
    (euclidean physical : ℕ → B.Index → B.Index → B.Index → Distribution)
    (T : StressTensorData Q G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  C.Compatible ∧ OPE.WeakBasisExpansion K B μ coeff ∧
  ∃ X : ExhaustiveMatching B C μ betaSeries gammaSeries coeff physical,
    FamilyStressMatched X form T curvatureSquare ∧
    FamilyContinuation X euclidean

end YangMills.RG
