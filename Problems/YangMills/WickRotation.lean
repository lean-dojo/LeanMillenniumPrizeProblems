import Problems.YangMills.OperatorProductExpansion

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Explicit Euclidean-to-Minkowski coefficient boundary relation

A real coordinate type alone never identifies Euclidean perturbative kernels
with physical Wightman coefficients. This relation records the holomorphic
continuation and weak boundary limit that must connect them. Only compact tests
are used: finite-IR-cutoff Euclidean coefficients can continue to functions of
exponential timelike growth, so global temperedness is not imposed on them.
Contact extensions at the origin and compatibility for many collision clusters
are not specified by this off-diagonal relation and remain separate work.
-/
noncomputable section
open MeasureTheory Filter
namespace YangMills.Wick
abbrev ComplexSpacetime := Fin 4 → ℂ

def LowerTube : Set ComplexSpacetime :=
  {z | 0 < -(z 0).im ∧ 0 < minkowski (fun i => -(z i).im) (fun i => -(z i).im)}

/-- Positive Euclidean time is negative imaginary physical time. -/
def euclideanPoint (x : Spacetime) : ComplexSpacetime :=
  fun i => if i = 0 then -Complex.I * (x i : ℂ) else (x i : ℂ)

/-- Approach the physical boundary from negative imaginary time. -/
def boundaryPoint (ε : ℝ) (x : Spacetime) : ComplexSpacetime :=
  fun i => (x i : ℂ) - if i = 0 then Complex.I * (ε : ℂ) else 0

/-- Mathematical relation, not permission to select independent coefficient
predictions: E must already be extracted from the fixed Euclidean generator.
Integrability is explicit because the Bochner integral is totalized. -/
structure AnalyticContinuation (E M : OPE.CoefficientDistribution) where
  analytic : ComplexSpacetime → ℂ
  holomorphic : DifferentiableOn ℂ analytic LowerTube
  euclidean_integrable : ∀ f : TestFunction, HasCompactSupport f →
    (∀ x ∈ tsupport f, 0 < x 0) →
    Integrable (fun x : Spacetime => analytic (euclideanPoint x) * f x)
  euclidean_agreement : ∀ f : TestFunction, HasCompactSupport f →
    (∀ x ∈ tsupport f, 0 < x 0) →
    E f = ∫ x : Spacetime, analytic (euclideanPoint x) * f x
  boundary_integrable : ∀ ε : ℝ, 0 < ε → ∀ f : TestFunction,
    HasCompactSupport f →
    Integrable (fun x : Spacetime => analytic (boundaryPoint ε x) * f x)
  physical_boundary : ∀ f : TestFunction, OPE.OffDiagonal f →
    Tendsto (fun ε : ℝ => ∫ x : Spacetime, analytic (boundaryPoint ε x) * f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (M f))
  euclidean_local : OPE.IsLocalDistribution E
  minkowski_local : OPE.IsLocalDistribution M
/-- Pullback of a covariant time index under x_M^0=-i x_E^0.
Curvature has two covariant indices, and each derivative adds one. -/
def jetFactor (j : CurvatureJet) : ℂ :=
  (-Complex.I) ^ ((if j.mu = 0 then 1 else 0) +
    (if j.nu = 0 then 1 else 0) + j.derivatives.count 0)

/-- Fixed complexified Wick substitution on actual invariant jet polynomials.
This transforms tensor/derivative labels as well as the coordinate argument. -/
def observableValue {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial.invariantAlgebra G) (A : Connection G) (x : Spacetime) : ℂ :=
  MvPolynomial.eval₂ (algebraMap ℝ ℂ)
    (fun c : CurvatureJetCoordinate G => jetFactor c.1 * ((c.1.evaluate A x c.2 : ℝ) : ℂ))
    (p : CurvatureJetPolynomial G)

/-- The matrix is fixed by the actual time-index substitution on labels.
It is not a freely selected Wick mixing convention. -/
structure LabelRotation {G : CompactSimpleGaugeGroup} {n : ℕ}
    (labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G) where
  map : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)
  meaning : ∀ i (A : Connection G) x,
    ∑ j : Fin n, map (Pi.single i 1) j *
      (((labels j : CurvatureJetPolynomial G).onConnection A x : ℝ) : ℂ) =
        observableValue (labels i) A x
  homogeneous : ∀ i j, OPE.dimension (labels i) ≠ OPE.dimension (labels j) →
    map (Pi.single j 1) i = 0

/-- Q_E(v)=Q_M(Wv), hence C_M=W C_E (W^-1 tensor W^-1)
after the coordinate boundary limit. -/
def rotatePairing {G : CompactSimpleGaugeGroup} {n : ℕ}
    {labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G}
    (W : LabelRotation labels)
    (raw : Fin n → Fin n → Fin n → OPE.CoefficientDistribution)
    (a b c : Fin n) (test : TestFunction) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    W.map (Pi.single k 1) c *
      W.map.symm (Pi.single a 1) i * W.map.symm (Pi.single b 1) j * raw i j k test

end YangMills.Wick
