import Problems.YangMills.CompositeFields
import Problems.YangMills.Ultraviolet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Weak OPE of the same renormalized quantum fields

Cluster coordinates are (r,z)=(x-y,y): the center remains smeared while only
relative separation shrinks. Continuous product kernels agree on a dense
Schwartz tensor span with actual products of the same composite operators.
Exact coefficient distributions remain witness data; their prescribed
perturbative matching is separate. This pair-OPE presentation does not yet
supply the full multi-cluster/contact prescription or the fixed YM generator.
-/
noncomputable section
open Filter
namespace YangMills.OPE
abbrev PairTestFunction := SchwartzMap (Spacetime × Spacetime) ℂ
/-- Only compact tests are observed. No global tempered-growth condition is
imposed on OPE coefficients. Algebraic values on noncompact Schwartz tests are
an auxiliary extension; local distributions admit such extensions, and two
extensions agreeing on compact tests represent the same local distribution. -/
abbrev CoefficientDistribution := TestFunction →ₗ[ℂ] ℂ

/-- Standard finite-order continuity on each fixed compact support. -/
def IsLocalDistribution (L : CoefficientDistribution) : Prop :=
  ∀ K : Set Spacetime, IsCompact K → ∃ N : ℕ, ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ f : TestFunction, tsupport f ⊆ K →
      ‖L f‖ ≤ bound * ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j f

def clusterCoordinates : (Spacetime × Spacetime) ≃ₗ[ℝ] (Spacetime × Spacetime) where
  toFun xy := (xy.1 - xy.2, xy.2)
  invFun rz := (rz.1 + rz.2, rz.2)
  left_inv := by intro xy; ext <;> simp
  right_inv := by intro rz; ext <;> simp
  map_add' := by intro x y; ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' := by intro a x; ext <;> simp [smul_sub]

/-- Intrinsic engineering degree in the quotient by actual connection
identities. A candidate cannot inflate an upper bound to weaken UV estimates. -/
def dimension {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial.invariantAlgebra G) : ℕ := intrinsicEngineeringDimension p

/-- A finite truncation, spanning the actual classical filtration through D.
The spanning relation is equality on every smooth connection. -/
structure Truncation (G : CompactSimpleGaugeGroup) (D : ℕ) where
  count : ℕ
  label : Fin count → CurvatureJetPolynomial.invariantAlgebra G
  below : ∀ i, dimension (label i) < D
  spans : ∀ p : CurvatureJetPolynomial.invariantAlgebra G,
    dimension p < D →
    ∃ a : Fin count → ℝ, ∀ (A : Connection G) x,
      (p : CurvatureJetPolynomial G).onConnection A x =
        ∑ i : Fin count, a i * (label i : CurvatureJetPolynomial G).onConnection A x

/-- A coherent classical filtered basis. Independence is only CLASSICAL;
no injectivity or bijection of the quantum correspondence is required. -/
structure FilteredBasis (G : CompactSimpleGaugeGroup) where
  Index : Type
  [decidable : DecidableEq Index]
  label : Index → CurvatureJetPolynomial.invariantAlgebra G
  active : ℕ → Finset Index
  active_iff : ∀ i D, i ∈ active D ↔ dimension (label i) < D
  independent : ∀ a : Index →₀ ℝ,
    (∀ (A : Connection G) x,
      a.sum (fun i r => r * (label i : CurvatureJetPolynomial G).onConnection A x) = 0) → a = 0
  spans : ∀ p : CurvatureJetPolynomial.invariantAlgebra G,
    ∃ a : Index →₀ ℝ,
      (∀ i ∈ a.support, dimension (label i) ≤ dimension p) ∧
      ∀ (A : Connection G) x,
        (p : CurvatureJetPolynomial G).onConnection A x =
          a.sum (fun i r => r * (label i : CurvatureJetPolynomial G).onConnection A x)
attribute [instance] FilteredBasis.decidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}

/-- Tensor tests are fixed pointwise, and their span is dense. Hence continuous
kernels cannot hide arbitrary components not detected by field products.
Schwartz tensor-density and product-kernel existence are supporting analysis. -/
structure PairKernels (C : RenormalizedCompositeMap Q G) where
  tensor : TestFunction → TestFunction → PairTestFunction
  tensor_eq : ∀ f g xy, tensor f g xy = f xy.1 * g xy.2
  tensor_dense : Dense ((Submodule.span ℂ
    (Set.range fun fg : TestFunction × TestFunction => tensor fg.1 fg.2)) : Set PairTestFunction)
  kernel : RenormalizationScale →
    CurvatureJetPolynomial.invariantAlgebra G → CurvatureJetPolynomial.invariantAlgebra G →
    Q.domain → Q.domain → PairTestFunction →L[ℂ] ℂ
  actual_fields : ∀ μ p q v w f g,
    kernel μ p q v w (tensor f g) =
      inner ℂ (v : H) (C.field μ p f (C.field μ q g w) : H)

def clusterTest {C : RenormalizedCompositeMap Q G} (K : PairKernels C)
    (center relative : TestFunction) (scale : ℝ) : PairTestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    clusterCoordinates.toContinuousLinearEquiv (K.tensor (dilateTest scale relative) center)

@[simp] theorem clusterTest_apply {C : RenormalizedCompositeMap Q G}
    (K : PairKernels C) (center relative : TestFunction) {scale : ℝ} (hscale : scale ≠ 0)
    (xy : Spacetime × Spacetime) :
    clusterTest K center relative scale xy =
      (((scale⁻¹ ^ 4 : ℝ) : ℂ) * relative (scale⁻¹ • (xy.1 - xy.2))) * center xy.2 := by
  simp [clusterTest, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    clusterCoordinates, K.tensor_eq, dilateTest_apply hscale]

/-- Finite subtraction uses actual composite matrix elements and coefficient
distributions, with no separately supplied physical correlations. -/
def remainder {C : RenormalizedCompositeMap Q G} (K : PairKernels C)
    (μ : RenormalizationScale) (p q : CurvatureJetPolynomial.invariantAlgebra G)
    {D : ℕ} (T : Truncation G D)
    (coeff : CurvatureJetPolynomial.invariantAlgebra G → CoefficientDistribution)
    (v w : Q.domain) (center relative : TestFunction) (scale : ℝ) : ℂ :=
  K.kernel μ p q v w (clusterTest K center relative scale) -
    ∑ i : Fin T.count, coeff (T.label i) (dilateTest scale relative) *
      inner ℂ (v : H) (C.field μ (T.label i) center w : H)

def word (C : RenormalizedCompositeMap Q G) (μ : RenormalizationScale) :
    List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction) → Q.domain
  | [] => Q.vacuum
  | (p, f) :: rest => C.field μ p f (word C μ rest)

/-- Positive separation excludes extra spectator contact singularities. -/
def SeparatedSpectators (center : TestFunction)
    (spectators : List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction)) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ spectators,
    ∀ x ∈ tsupport center, ∀ y ∈ tsupport s.2, ρ ≤ ‖x - y‖

def OffDiagonal (f : TestFunction) : Prop :=
  HasCompactSupport f ∧ (0 : Spacetime) ∉ tsupport f

/-- Explicit weak remainder: scale^(dp+dq-D+δ)R→0 for every δ>0 through scale>0.
Physical weak tests are actual composite field words with separated spectators.
No norm convergence or point-field product is required. Full multi-cluster
compatibility and a source-fidelity argument remain separate obligations. -/
def WeakExpansion {C : RenormalizedCompositeMap Q G} (K : PairKernels C)
    (μ : RenormalizationScale) (p q : CurvatureJetPolynomial.invariantAlgebra G)
    {D : ℕ} (T : Truncation G D)
    (coeff : CurvatureJetPolynomial.invariantAlgebra G → CoefficientDistribution) : Prop :=
  (∀ r, IsLocalDistribution (coeff r)) ∧
  ∀ (center relative : TestFunction), HasCompactSupport center → OffDiagonal relative →
    ∀ left right : List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction),
    SeparatedSpectators center (left ++ right) → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun scale : ℝ =>
      ((Real.rpow scale ((dimension p : ℝ) + dimension q - D + δ) : ℝ) : ℂ) *
        remainder K μ p q T coeff (word C μ left) (word C μ right) center relative scale)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
/-- A single coefficient family and a coherent classical basis determine every
truncation. Repeated labels or independently chosen truncation multiplicities
cannot change the subtraction. -/
def basisRemainder {C : RenormalizedCompositeMap Q G} (K : PairKernels C)
    (B : FilteredBasis G) (μ : RenormalizationScale)
    (coeff : B.Index → B.Index → B.Index → CoefficientDistribution)
    (a b : B.Index) (D : ℕ) (v w : Q.domain)
    (center relative : TestFunction) (scale : ℝ) : ℂ :=
  K.kernel μ (B.label a) (B.label b) v w (clusterTest K center relative scale) -
    ∑ i ∈ B.active D, coeff a b i (dilateTest scale relative) *
      inner ℂ (v : H) (C.field μ (B.label i) center w : H)

/-- Exhaustive, coherent weak pair OPE on the same fields, with all orders of
engineering-dimension truncation and only relative cluster scaling. -/
def WeakBasisExpansion {C : RenormalizedCompositeMap Q G} (K : PairKernels C)
    (B : FilteredBasis G) (μ : RenormalizationScale)
    (coeff : B.Index → B.Index → B.Index → CoefficientDistribution) : Prop :=
  (∀ a b c, IsLocalDistribution (coeff a b c)) ∧
  ∀ a b (D : ℕ) (center relative : TestFunction),
    HasCompactSupport center → OffDiagonal relative →
    ∀ left right : List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction),
    SeparatedSpectators center (left ++ right) → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun scale : ℝ =>
      ((Real.rpow scale ((dimension (B.label a) : ℝ) + dimension (B.label b) - D + δ) : ℝ) : ℂ) *
        basisRemainder K B μ coeff a b D (word C μ left) (word C μ right) center relative scale)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

end YangMills.OPE
