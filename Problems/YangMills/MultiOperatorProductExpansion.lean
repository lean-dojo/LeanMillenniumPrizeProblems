import Problems.YangMills.OperatorProductExpansion

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Simultaneous multi-insertion OPE on the same fields

There are n relative points and one center. Every relative point contracts
about that center, while spectators remain separated. Kernels are fixed on
dense product tests by actual ordered products of the same C-fields. This
expresses the multi-insertion version of the weak scaling remainder and the
separate coefficient singularity bound in Fröb--Holland (1603.08012), Theorem 1.
Prescribed coefficients must additionally come from the fixed YM extraction.
Overlapping nested clusters and contact extensions are separate conditions.
-/
noncomputable section
open Filter
namespace YangMills.OPE

abbrev RelativeSpace (n : ℕ) := Fin n → Spacetime
abbrev RelativeTest (n : ℕ) := SchwartzMap (RelativeSpace n) ℂ
abbrev ClusterTest (n : ℕ) := SchwartzMap (RelativeSpace n × Spacetime) ℂ
abbrev MultiDistribution (n : ℕ) := RelativeTest n →ₗ[ℂ] ℂ

/-- Local distribution continuity, without a global tempered-growth axiom. -/
def IsLocalMultiDistribution {n : ℕ} (L : MultiDistribution n) : Prop :=
  ∀ K : Set (RelativeSpace n), IsCompact K → ∃ N : ℕ, ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ f : RelativeTest n, tsupport f ⊆ K →
      ‖L f‖ ≤ bound * ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j f

/-- Normalized dilation in 4n relative coordinates. -/
def dilateRelative {n : ℕ} (scale : ℝ) (f : RelativeTest n) : RelativeTest n :=
  if h : scale ≠ 0 then
    ((scale⁻¹ ^ (4 * n) : ℝ) : ℂ) •
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.smulLeft (Units.mk0 scale h)⁻¹) f
  else 0

@[simp] theorem dilateRelative_apply {n : ℕ} {scale : ℝ} (h : scale ≠ 0)
    (f : RelativeTest n) (x : RelativeSpace n) :
    dilateRelative scale f x = ((scale⁻¹ ^ (4 * n) : ℝ) : ℂ) * f (scale⁻¹ • x) := by
  simp [dilateRelative, h, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.smulLeft, Units.smul_def]

/-- x_i-z are all relative positions; z is the final insertion point. -/
def multiClusterCoordinates (n : ℕ) :
    (RelativeSpace n × Spacetime) ≃ₗ[ℝ] (RelativeSpace n × Spacetime) where
  toFun xz := (fun i => xz.1 i - xz.2, xz.2)
  invFun rz := (fun i => rz.1 i + rz.2, rz.2)
  left_inv := by intro xz; ext <;> simp
  right_inv := by intro rz; ext <;> simp
  map_add' := by intro x y; ext <;> simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' := by intro a x; ext <;> simp; ring

/-- Compact configurations avoid every pairwise collision, including a
relative insertion hitting the final insertion at the origin. -/
def MultiOffDiagonal {n : ℕ} (f : RelativeTest n) : Prop :=
  HasCompactSupport f ∧ ∀ r ∈ tsupport f,
    (∀ i, r i ≠ 0) ∧ (∀ i j, i ≠ j → r i ≠ r j)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}

/-- Ordered products with an arbitrary state on the right, using the same
common invariant domain as all elementary/composite fields. -/
def actWord (C : RenormalizedCompositeMap Q G) (μ : RenormalizationScale) :
    List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction) → Q.domain → Q.domain
  | [], w => w
  | (p, f) :: rest, w => C.field μ p f (actWord C μ rest w)

structure MultiKernels (C : RenormalizedCompositeMap Q G) where
  tensor : (n : ℕ) → (Fin n → TestFunction) → TestFunction → ClusterTest n
  tensor_eq : ∀ n fs f xz, tensor n fs f xz = (∏ i : Fin n, fs i (xz.1 i)) * f xz.2
  tensor_dense : ∀ n, Dense ((Submodule.span ℂ
    (Set.range fun fsf : (Fin n → TestFunction) × TestFunction => tensor n fsf.1 fsf.2)) :
      Set (ClusterTest n))
  separatedTensor : (n : ℕ) → RelativeTest n → TestFunction → ClusterTest n
  separatedTensor_eq : ∀ n f g rz, separatedTensor n f g rz = f rz.1 * g rz.2
  kernel : (n : ℕ) → RenormalizationScale →
    (Fin n → CurvatureJetPolynomial.invariantAlgebra G) →
    CurvatureJetPolynomial.invariantAlgebra G → Q.domain → Q.domain → ClusterTest n →L[ℂ] ℂ
  actual_fields : ∀ n μ labels last v w fs f,
    kernel n μ labels last v w (tensor n fs f) =
      inner ℂ (v : H) (actWord C μ (List.ofFn (fun i => (labels i, fs i)))
        (C.field μ last f w) : H)

def multiClusterTest {C : RenormalizedCompositeMap Q G} (K : MultiKernels C)
    {n : ℕ} (center : TestFunction) (relative : RelativeTest n) (scale : ℝ) : ClusterTest n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (multiClusterCoordinates n).toContinuousLinearEquiv
      (K.separatedTensor n (dilateRelative scale relative) center)

/-- One coefficient family for every arity, input label and output label. -/
abbrev MultiCoefficients (B : FilteredBasis G) :=
  (n : ℕ) → (Fin n → B.Index) → B.Index → B.Index → MultiDistribution n

def inputDimension (B : FilteredBasis G) {n : ℕ}
    (labels : Fin n → B.Index) (last : B.Index) : ℕ :=
  (∑ i : Fin n, dimension (B.label (labels i))) + dimension (B.label last)

def multiRemainder {C : RenormalizedCompositeMap Q G} (K : MultiKernels C)
    (B : FilteredBasis G) (μ : RenormalizationScale) (coeff : MultiCoefficients B)
    {n : ℕ} (labels : Fin n → B.Index) (last : B.Index) (D : ℕ)
    (v w : Q.domain) (center : TestFunction) (relative : RelativeTest n) (scale : ℝ) : ℂ :=
  K.kernel n μ (fun i => B.label (labels i)) (B.label last) v w
      (multiClusterTest K center relative scale) -
    ∑ b ∈ B.active D, coeff n labels last b (dilateRelative scale relative) *
      inner ℂ (v : H) (C.field μ (B.label b) center w : H)

/-- Separate coefficient scaling bound from Theorem 1, equation (1.1.3).
It is not replaced by a remainder condition that could hide cancellation
between redundant quantum fields. Only noncoincident relative tests occur. -/
def MultiSingularityBounds (B : FilteredBasis G) (coeff : MultiCoefficients B) : Prop :=
  ∀ n, 0 < n → ∀ labels last b (relative : RelativeTest n), MultiOffDiagonal relative →
    ∀ δ : ℝ, 0 < δ →
    Tendsto (fun scale : ℝ =>
      ((Real.rpow scale ((inputDimension B labels last : ℝ) -
        dimension (B.label b) + δ) : ℝ) : ℂ) *
          coeff n labels last b (dilateRelative scale relative))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- Fixed simultaneous-cluster weak OPE of the actual C-fields for every
number of inputs, engineering truncation, and separated physical spectators. -/
def WeakMultiExpansion {C : RenormalizedCompositeMap Q G} (K : MultiKernels C)
    (B : FilteredBasis G) (μ : RenormalizationScale) (coeff : MultiCoefficients B) : Prop :=
  (∀ n labels last b, IsLocalMultiDistribution (coeff n labels last b)) ∧
  MultiSingularityBounds B coeff ∧
  ∀ n, 0 < n → ∀ labels last (D : ℕ) (center : TestFunction) (relative : RelativeTest n),
    HasCompactSupport center → MultiOffDiagonal relative →
    ∀ left right : List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction),
    SeparatedSpectators center (left ++ right) → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun scale : ℝ =>
      ((Real.rpow scale ((inputDimension B labels last : ℝ) - D + δ) : ℝ) : ℂ) *
        multiRemainder K B μ coeff labels last D (word C μ left) (word C μ right)
          center relative scale)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

end YangMills.OPE
