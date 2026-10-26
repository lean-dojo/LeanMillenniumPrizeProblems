import Problems.YangMills.MultiOperatorProductExpansion
import Problems.YangMills.StressTensor

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Explicit coincidence counterterms

A derivative of a delta distribution is fixed by its action on Schwartz
tests. For a cluster, its center remains a test function for the same local
quantum field. This gives concrete total-diagonal contact distributions;
partial-diagonal compositions and their Ward constraints are still separate.
-/
noncomputable section
namespace YangMills.OPE

/-- The embedding of the coincidence diagonal in relative/center coordinates. -/
def diagonalEmbedding (n : ℕ) : Spacetime →L[ℝ] (RelativeSpace n × Spacetime) :=
  ContinuousLinearMap.inr ℝ (RelativeSpace n) Spacetime

/-- Actual continuous restriction f(r,z)↦f(0,z), obtained by proper linear
pullback. It is not an independent choice of contact-term values. -/
def diagonalRestriction (n : ℕ) : ClusterTest n →L[ℂ] TestFunction :=
  SchwartzMap.compCLM ℂ (diagonalEmbedding n).hasTemperateGrowth
    ⟨1, 1, by
      intro x
      simp only [diagonalEmbedding, ContinuousLinearMap.inr_apply, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg x), pow_one, one_mul]
      linarith [norm_nonneg x]⟩

@[simp] theorem diagonalRestriction_apply (n : ℕ) (f : ClusterTest n) (z : Spacetime) :
    diagonalRestriction n f z = f (0, z) := rfl

/-- Relative derivative direction; the center coordinate is held fixed. -/
def relativeDerivative {n : ℕ} (i : Fin n) (μ : Fin 4) :
    ClusterTest n →L[ℂ] ClusterTest n :=
  LineDeriv.lineDerivOpCLM (V := RelativeSpace n × Spacetime) ℂ (ClusterTest n) (Pi.single i (Pi.single μ 1), 0)

def orderedRelativeDerivative {n : ℕ} : List (Fin n × Fin 4) →
    ClusterTest n →L[ℂ] ClusterTest n
  | [] => ContinuousLinearMap.id ℂ _
  | (i, μ) :: rest => (relativeDerivative i μ).comp (orderedRelativeDerivative rest)

/-- ∂^α δ(r) paired with a center-dependent test. The sign is the
usual distributional derivative sign, including repeated directions. -/
def deltaCluster {n : ℕ} (directions : List (Fin n × Fin 4)) :
    ClusterTest n →L[ℂ] TestFunction :=
  ((-1 : ℂ) ^ directions.length) •
    (diagonalRestriction n).comp (orderedRelativeDerivative directions)

@[simp] theorem deltaCluster_nil (n : ℕ) :
    deltaCluster (n := n) [] = diagonalRestriction n := by
  simp [deltaCluster, orderedRelativeDerivative]

/-- Only finitely many derivatives of bounded total order may occur.
Their coefficients still must be extracted from the same insertion flow
and satisfy restored quantum Ward identities. -/
structure ClusterCounterterm (n degree : ℕ) where
  coefficient : List (Fin n × Fin 4) →₀ ℂ
  order_bound : ∀ d ∈ coefficient.support, d.length ≤ degree

def ClusterCounterterm.testMap {n degree : ℕ} (c : ClusterCounterterm n degree) :
    ClusterTest n →L[ℂ] TestFunction :=
  c.coefficient.sum (fun directions a => a • deltaCluster directions)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}

/-- The contact term acts through the same renormalized local field at the
cluster center; no independent physical correlation is inserted. -/
def ClusterCounterterm.matrixElement {n degree : ℕ} (c : ClusterCounterterm n degree)
    (C : RenormalizedCompositeMap Q G) (μ : RenormalizationScale)
    (p : CurvatureJetPolynomial.invariantAlgebra G) (v w : Q.domain)
    (f : ClusterTest n) : ℂ :=
  inner ℂ (v : H) (C.field μ p (c.testMap f) w : H)

end YangMills.OPE
