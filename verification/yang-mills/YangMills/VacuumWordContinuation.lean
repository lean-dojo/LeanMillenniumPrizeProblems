import YangMills.MultiOperatorProductExpansion
import YangMills.MultiWickRotation

/-!
# Wick boundary values of the actual composite vacuum words

This is NONPERTURBATIVE analytic-continuation data for the same C-fields on
the same Q.domain and vacuum. Its Minkowski boundary is fixed by K's actual
field-product kernel; no independently selected physical correlations occur.
The compact boundary growth is the standard local polynomial tube bound
used for distributional boundary values/uniqueness in the Wightman framework.
Proving that this presentation follows from the selected Wightman axioms is
a supporting equivalence theorem, not a Yang--Mills existence assertion.

The separate UV bridge will match these observations asymptotically, never
identify them with a convergent or resummed formal perturbative series.
-/
noncomputable section
open Filter MeasureTheory
namespace YangMills.PhysicalWords

abbrev WordTest (arity : ℕ) := SchwartzMap (Fin arity → Spacetime) ℂ
abbrev WordDistribution (arity : ℕ) := WordTest arity →ₗ[ℂ] ℂ
abbrev ComplexWordSpace (arity : ℕ) := Fin arity → Wick.ComplexSpacetime

/-- Absolute ordered points; every successive imaginary difference is past
 timelike. No imaginary absolute center is artificially fixed. -/
def WordTube (arity : ℕ) : Set (ComplexWordSpace arity) :=
  {z | ∀ i j, i < j → z i - z j ∈ Wick.LowerTube}

def euclideanWordPoint {arity : ℕ} (x : Fin arity → Spacetime) : ComplexWordSpace arity :=
  fun i => Wick.euclideanPoint (x i)

def boundaryWordPoint {arity : ℕ} (epsilon : ℝ) (x : Fin arity → Spacetime) :
    ComplexWordSpace arity :=
  fun i mu => (x i mu : ℂ) - if mu = 0 then
    Complex.I * (epsilon : ℂ) * ((arity - i.val : ℕ) : ℂ) else 0

/-- The strict Euclidean time order fixes the actual Wightman word order.
Such compact supports automatically avoid every insertion coincidence. -/
def OrderedEuclideanWord {arity : ℕ} (x : Fin arity → Spacetime) : Prop :=
  ∀ i j, i < j → x j 0 < x i 0

def OrderedEuclideanTest {arity : ℕ} (test : WordTest arity) : Prop :=
  HasCompactSupport test ∧ ∀ x ∈ tsupport test, OrderedEuclideanWord x

/-- Split the final insertion from its predecessors, preserving order. -/
def wordClusterCoordinates (n : ℕ) :
    (Fin (n + 1) → Spacetime) ≃ₗ[ℝ] ((Fin n → Spacetime) × Spacetime) where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun xz := Fin.lastCases xz.2 xz.1
  left_inv := by
    intro x
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv := by
    intro xz
    apply Prod.ext
    · funext i; simp
    · simp
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}

/-- Full-position vacuum distribution, fixed by the SAME actual C product
kernel. The auxiliary coordinate equivalence introduces no new data. -/
def vacuumWordDistribution {C : RenormalizedCompositeMap Q G} (K : OPE.MultiKernels C)
    (n : ℕ) (mu : RenormalizationScale)
    (labels : Fin (n + 1) → CurvatureJetPolynomial.invariantAlgebra G) :
    WordDistribution (n + 1) :=
  (K.kernel n mu (fun i => labels i.castSucc) (labels (Fin.last n)) Q.vacuum Q.vacuum).toLinearMap.comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (wordClusterCoordinates n).toContinuousLinearEquiv.symm).toLinearMap

/-- Product tests on which K is explicitly fixed by ordered operators. -/
def wordTensorTest {C : RenormalizedCompositeMap Q G} (K : OPE.MultiKernels C)
    (n : ℕ) (fs : Fin n → TestFunction) (last : TestFunction) : WordTest (n + 1) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (wordClusterCoordinates n).toContinuousLinearEquiv (K.tensor n fs last)

/-- The bridge is anchored in actual same-domain operators, not labels. -/
theorem vacuumWordDistribution_tensor {C : RenormalizedCompositeMap Q G}
    (K : OPE.MultiKernels C) (n : ℕ) (mu : RenormalizationScale)
    (labels : Fin (n + 1) → CurvatureJetPolynomial.invariantAlgebra G)
    (fs : Fin n → TestFunction) (last : TestFunction) :
    vacuumWordDistribution K n mu labels (wordTensorTest K n fs last) =
      inner ℂ (Q.vacuum : H)
        (OPE.actWord C mu (List.ofFn (fun i => (labels i.castSucc, fs i)))
          (C.field mu (labels (Fin.last n)) last Q.vacuum) : H) := by
  have inverse : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (wordClusterCoordinates n).toContinuousLinearEquiv.symm
      (wordTensorTest K n fs last) = K.tensor n fs last := by
    ext xz
    simp [wordTensorTest]
  unfold vacuumWordDistribution
  change K.kernel n mu (fun i => labels i.castSucc) (labels (Fin.last n))
    Q.vacuum Q.vacuum
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (wordClusterCoordinates n).toContinuousLinearEquiv.symm)
          (wordTensorTest K n fs last)) = _
  rw [inverse]
  exact K.actual_fields n mu (fun i => labels i.castSucc) (labels (Fin.last n))
    Q.vacuum Q.vacuum fs last

/-- Ordered words use exactly the same common invariant C-domain. -/
theorem compositeWord_append (C : RenormalizedCompositeMap Q G) (mu : RenormalizationScale)
    (left right : List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction)) :
    C.word mu (left ++ right) = OPE.actWord C mu left (C.word mu right) := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      cases head
      simp only [List.cons_append, RenormalizedCompositeMap.word, OPE.actWord, induction]

/-- Literal same-C vacuum words, including the distinguished final field. -/
theorem vacuumWordDistribution_tensor_word {C : RenormalizedCompositeMap Q G}
    (K : OPE.MultiKernels C) (n : ℕ) (mu : RenormalizationScale)
    (labels : Fin (n + 1) → CurvatureJetPolynomial.invariantAlgebra G)
    (fs : Fin n → TestFunction) (last : TestFunction) :
    vacuumWordDistribution K n mu labels (wordTensorTest K n fs last) =
      inner ℂ (Q.vacuum : H)
        (C.word mu ((List.ofFn (fun i => (labels i.castSucc, fs i))) ++
          [(labels (Fin.last n), last)]) : H) := by
  rw [vacuumWordDistribution_tensor, compositeWord_append]
  rfl

/-- Nonperturbative vacuum-word continuation with the fixed C boundary.
Only compact observations are imposed; no extra global Euclidean tempered
condition or arbitrary-vector norm-convergent expansion is demanded. -/
structure VacuumWordContinuation {C : RenormalizedCompositeMap Q G} (K : OPE.MultiKernels C) where
  analytic : (n : ℕ) → RenormalizationScale →
    (Fin (n + 1) → CurvatureJetPolynomial.invariantAlgebra G) → ComplexWordSpace (n + 1) → ℂ
  holomorphic : ∀ n mu labels, DifferentiableOn ℂ (analytic n mu labels) (WordTube (n + 1))
  translation : ∀ n mu labels z, z ∈ WordTube (n + 1) → ∀ a : Wick.ComplexSpacetime,
    analytic n mu labels (fun i => z i + a) = analytic n mu labels z
  euclidean_integrable : ∀ n mu labels (test : WordTest (n + 1)), OrderedEuclideanTest test →
    Integrable (fun x => analytic n mu labels (euclideanWordPoint x) * test x)
  scaled_euclidean_integrable : ∀ n mu labels scale, 0 < scale →
    ∀ test : WordTest (n + 1), OrderedEuclideanTest test →
      Integrable (fun x => analytic n mu labels (euclideanWordPoint (scale • x)) * test x)
  boundary_integrable : ∀ n mu labels epsilon, 0 < epsilon →
    ∀ test : WordTest (n + 1), HasCompactSupport test →
      Integrable (fun x => analytic n mu labels (boundaryWordPoint epsilon x) * test x)
  boundary_growth : ∀ n mu labels (compact : Set (Fin (n + 1) → Spacetime)), IsCompact compact →
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      ∀ x ∈ compact, ‖analytic n mu labels (boundaryWordPoint epsilon x)‖ ≤ A * epsilon⁻¹ ^ N
  actual_boundary : ∀ n mu labels (test : WordTest (n + 1)), HasCompactSupport test →
    Tendsto (fun epsilon : ℝ => ∫ x,
      analytic n mu labels (boundaryWordPoint epsilon x) * test x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (vacuumWordDistribution K n mu labels test))

/-- Actual Euclidean observation of the above physical analytic word. -/
def VacuumWordContinuation.euclideanObservation {C : RenormalizedCompositeMap Q G}
    {K : OPE.MultiKernels C} (V : VacuumWordContinuation K) (n : ℕ)
    (mu : RenormalizationScale) (labels : Fin (n + 1) → CurvatureJetPolynomial.invariantAlgebra G)
    (test : WordTest (n + 1)) : ℂ :=
  ∫ x, V.analytic n mu labels (euclideanWordPoint x) * test x

/-- Normalized short-distance observation, after the coordinate change
x_physical=scale*x. No inverse-volume factor remains in this integration
variable; canonical field dimensions are supplied by the RG stripping. -/
def VacuumWordContinuation.scaledEuclideanObservation {C : RenormalizedCompositeMap Q G}
    {K : OPE.MultiKernels C} (V : VacuumWordContinuation K) (n : ℕ)
    (mu : RenormalizationScale) (labels : Fin (n + 1) → CurvatureJetPolynomial.invariantAlgebra G)
    (scale : ℝ) (test : WordTest (n + 1)) : ℂ :=
  ∫ x, V.analytic n mu labels (euclideanWordPoint (scale • x)) * test x

end YangMills.PhysicalWords
