import YangMills.RenormalizationGroup
import YangMills.MultiWickRotation

/-!
# Shared RG and stress matching for every insertion arity

All arities use the same filtered label basis, actual composite fields,
running coupling and mixing transport. Pair coefficients are restrictions of
the multi-insertion family rather than separately selected data. The fixed
renormalized YM generator must still authorize the Euclidean series.
-/
noncomputable section
open Filter
namespace YangMills.RG

/-- The unique relative coordinate of a two-input cluster. -/
def singletonRelative : OPE.RelativeSpace 1 ≃ₗ[ℝ] Spacetime where
  toFun r := r 0
  invFun x := fun _ => x
  left_inv := by intro r; funext i; have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
  right_inv := by intro x; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def pairFromMulti {G : CompactSimpleGaugeGroup} {B : OPE.FilteredBasis G}
    (coeff : OPE.MultiCoefficients B) (a b c : B.Index) : OPE.CoefficientDistribution :=
  (coeff 1 (fun _ => a) b c).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      singletonRelative.toContinuousLinearEquiv).toLinearMap

/-- Tensor transport and canonical dilation in all relative coordinates.
Each incoming field contributes its own inverse transport factor. -/
def multiStrippedPairing {G : CompactSimpleGaugeGroup} {m n : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}
    (F : Frame labels betaSeries gammaSeries)
    (coeff : (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (scale : ℝ) (inputs : Fin n → Fin m) (last output : Fin m)
    (test : OPE.RelativeTest n) : ℂ :=
  ∑ is : Fin n → Fin m, ∑ j : Fin m, ∑ k : Fin m,
    F.transport (time scale) (Pi.single k 1) output *
      (∏ r : Fin n, (F.transport (time scale)).symm (Pi.single (inputs r) 1) (is r)) *
      (F.transport (time scale)).symm (Pi.single last 1) j *
      (((scale ^ (((∑ r : Fin n, OPE.dimension (labels (is r))) : ℤ) +
        OPE.dimension (labels j) - OPE.dimension (labels k)) : ℝ)) : ℂ) *
      coeff is j k (OPE.dilateRelative scale test)

/-- All finite perturbative orders at every arity, in the same weak topology
as the exact multi-insertion OPE. Flat corrections remain permissible. -/
def AllOrderMultiMatch {G : CompactSimpleGaugeGroup} {m : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}
    (F : Frame labels betaSeries gammaSeries)
    (coeff : (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (perturbative : ℕ → (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n) : Prop :=
  (∀ n inputs last output, OPE.IsLocalMultiDistribution (coeff n inputs last output)) ∧
  (∀ k n inputs last output, OPE.IsLocalMultiDistribution (perturbative k n inputs last output)) ∧
  ∀ n, 0 < n → ∀ inputs last output (test : OPE.RelativeTest n),
    OPE.MultiOffDiagonal test → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ scale : ℝ, 0 < scale → scale < δ →
      ‖multiStrippedPairing F (coeff n) scale inputs last output test -
        ∑ k ∈ Finset.range (N + 1),
          ((F.running.coupling (time scale) : ℂ) ^ k) *
            perturbative k n inputs last output test‖ ≤
        ε * F.running.coupling (time scale) ^ N

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}

/-- One raw coordinate boundary family and the fixed label Wick substitution
on all inputs/output of every finite filtered sector. -/
def MultiFamilyContinuation
    {B : OPE.FilteredBasis G} {C : RenormalizedCompositeMap Q G}
    {μ : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : ℕ → B.Index → B.Index → ℂ}
    {coeff : OPE.MultiCoefficients B}
    {physical : ℕ → OPE.MultiCoefficients B}
    (X : ExhaustiveMatching B C μ betaSeries gammaSeries
      (pairFromMulti coeff) (fun k => pairFromMulti (physical k)))
    (euclidean : ℕ → OPE.MultiCoefficients B) : Prop :=
  ∃ raw : ℕ → OPE.MultiCoefficients B,
    (∀ k n inputs last output,
      Nonempty (Wick.MultiAnalyticContinuation
        (euclidean k n inputs last output) (raw k n inputs last output))) ∧
    ∀ D, ∃ W : Wick.LabelRotation (fun i => B.label (X.index D i)),
    ∀ k n inputs last output (test : OPE.RelativeTest n), HasCompactSupport test →
      physical k n (fun r => X.index D (inputs r)) (X.index D last) (X.index D output) test =
        Wick.rotateMultiPairing W
          (fun is j l => raw k n (fun r => X.index D (is r)) (X.index D j) (X.index D l))
          inputs last output test

/-- Integrated same-theory relations, not yet an admitted YM target: the
Euclidean and RG series require fixed action/Ward/extraction authorization. -/
def CoupledMultiSectorConditions
    {C : RenormalizedCompositeMap Q G} (K : OPE.MultiKernels C)
    (B : OPE.FilteredBasis G) (μ : RenormalizationScale) (form : InvariantForm G)
    (betaSeries : ℕ → ℝ) (gammaSeries : ℕ → B.Index → B.Index → ℂ)
    (coeff : OPE.MultiCoefficients B) (euclidean physical : ℕ → OPE.MultiCoefficients B)
    (T : StressTensorData Q G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  C.Compatible ∧ OPE.WeakMultiExpansion K B μ coeff ∧
  ∃ X : ExhaustiveMatching B C μ betaSeries gammaSeries
      (pairFromMulti coeff) (fun k => pairFromMulti (physical k)),
    FamilyStressMatched X form T curvatureSquare ∧
    MultiFamilyContinuation X euclidean ∧
    ∀ D, AllOrderMultiMatch (X.frame D)
      (fun n is j l => coeff n (fun r => X.index D (is r)) (X.index D j) (X.index D l))
      (fun k n is j l => physical k n (fun r => X.index D (is r)) (X.index D j) (X.index D l))

end YangMills.RG
