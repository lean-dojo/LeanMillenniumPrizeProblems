import Problems.YangMills.MultiOperatorProductExpansion
import Problems.YangMills.WickRotation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Ordered multi-insertion coefficient continuation

The tube ordering is the Wightman ordering of all n+1 inputs, with the last
input at zero. Requiring each relative imaginary point to lie in a cone
alone would omit the relative ordering of two nonfinal inputs. Tensor label
rotation is applied to every incoming slot and the outgoing slot.
-/
noncomputable section
open MeasureTheory Filter
namespace YangMills.Wick

abbrev MultiComplexSpacetime (n : ℕ) := Fin n → ComplexSpacetime

/-- Successive ordered imaginary separations are past timelike. The pairwise
form is equivalent by convexity of the forward cone. -/
def MultiLowerTube (n : ℕ) : Set (MultiComplexSpacetime n) :=
  {z | (∀ i, z i ∈ LowerTube) ∧ ∀ i j, i < j → z i - z j ∈ LowerTube}

def multiEuclideanPoint {n : ℕ} (x : OPE.RelativeSpace n) : MultiComplexSpacetime n :=
  fun i => euclideanPoint (x i)

/-- Imaginary times strictly increase toward the final point zero. -/
def multiBoundaryPoint {n : ℕ} (ε : ℝ) (x : OPE.RelativeSpace n) : MultiComplexSpacetime n :=
  fun i μ => (x i μ : ℂ) -
    if μ = 0 then Complex.I * (ε : ℂ) * ((n - i.val : ℕ) : ℂ) else 0

def OrderedEuclidean {n : ℕ} (x : OPE.RelativeSpace n) : Prop :=
  (∀ i, 0 < x i 0) ∧ ∀ i j, i < j → x j 0 < x i 0

/-- Fixed analytic relation between the generated Euclidean coefficients and
the physical ordered coefficient boundary values. It observes compact tests;
it does not add global temperedness of finite-IR-cutoff OPE coefficients. -/
structure MultiAnalyticContinuation {n : ℕ} (E M : OPE.MultiDistribution n) where
  analytic : MultiComplexSpacetime n → ℂ
  holomorphic : DifferentiableOn ℂ analytic (MultiLowerTube n)
  euclidean_integrable : ∀ f : OPE.RelativeTest n, HasCompactSupport f →
    (∀ x ∈ tsupport f, OrderedEuclidean x) →
    Integrable (fun x => analytic (multiEuclideanPoint x) * f x)
  euclidean_agreement : ∀ f : OPE.RelativeTest n, HasCompactSupport f →
    (∀ x ∈ tsupport f, OrderedEuclidean x) →
    E f = ∫ x, analytic (multiEuclideanPoint x) * f x
  boundary_integrable : ∀ ε : ℝ, 0 < ε → ∀ f : OPE.RelativeTest n,
    HasCompactSupport f → Integrable (fun x => analytic (multiBoundaryPoint ε x) * f x)
  physical_boundary : ∀ f : OPE.RelativeTest n, OPE.MultiOffDiagonal f →
    Tendsto (fun ε : ℝ => ∫ x, analytic (multiBoundaryPoint ε x) * f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (M f))
  euclidean_local : OPE.IsLocalMultiDistribution E
  minkowski_local : OPE.IsLocalMultiDistribution M

/-- Q_E(v)=Q_M(Wv): one W on the output and W⁻¹ on EVERY input. -/
def rotateMultiPairing {G : CompactSimpleGaugeGroup} {m n : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    (W : LabelRotation labels)
    (raw : (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (inputs : Fin n → Fin m) (last output : Fin m) (test : OPE.RelativeTest n) : ℂ :=
  ∑ is : Fin n → Fin m, ∑ j : Fin m, ∑ k : Fin m,
    W.map (Pi.single k 1) output *
      (∏ r : Fin n, W.map.symm (Pi.single (inputs r) 1) (is r)) *
      W.map.symm (Pi.single last 1) j * raw is j k test

end YangMills.Wick
