import Problems.YangMills.IntegratedMarginalFlow
import Problems.YangMills.FullBVBridge

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! Source355–359's integrated sB0 is dimension5, ghost1. Its
normalization is independent of the pointwise insertion basis (source123). -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The seed is the actual integrated BV variation of the prescribed
primitive density, computed from the SAME full master action. -/
def integratedWardSeed {B : InvariantForm G} (e : ColorFrame B)
    (terms : ℝ → List (LocalVertex G)) (μ g : ℝ) : OrderedAmplitude G :=
  FullBV.densityAmplitude
    (FullBV.classicalSTDensity e g (FullBV.densityOfVertices g (terms μ)))

/-- TableII's integrated dimension5 normalization for sB0. Below4 jets
vanish at IR0; dimensions4–5 are normalized at mu; above5 vanish at UV.
The actual scalar kernels and their derivatives determine every condition. -/
structure IntegratedWardConditions {B : InvariantForm G} (e : ColorFrame B)
    (A I : ScaleCouplingFamily G) (terms : ℝ → List (LocalVertex G)) : Prop where
  dimension : ∀ μ v, v ∈ terms μ → v.degree = 4
  ghost : ∀ μ v, v ∈ terms μ → v.ghostNumber = 0
  parity : ∀ μ v, v ∈ terms μ → v.parity = false
  momentum_smooth : ∀ μ g loop Λ UV legs,
    0 < μ → μ ≤ UV → 0 < Λ → Λ ≤ UV → ContDiff ℝ ∞ (I μ g loop Λ UV legs)
  positive_scale_jet_continuity : ∀ μ g loop UV legs
      (d : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ UV → ContinuousOn
      (fun Λ => momentumJet d (I μ g loop Λ UV legs) q) (Set.Ioc 0 UV)
  reduced_extension : ∀ μ g loop Λ UV legs q,
    I μ g loop Λ UV legs q = I μ g loop Λ UV legs (conservingMomenta legs q)
  statistics : ∀ μ g loop Λ UV legs q,
    (totalGhostNumber legs ≠ 1 ∨ oddCount legs % 2 ≠ 1) → I μ g loop Λ UV legs q = 0
  graded_symmetry : ∀ μ g loop Λ UV legs q (π : Equiv.Perm (Fin legs.length)),
    BalancedMomenta legs q →
    I μ g loop Λ UV (permutedLegs legs π) (permutedMomenta legs π q) =
      permutationSign legs π * I μ g loop Λ UV legs q
  integrable : ∀ μ g loop Λ UV legs q,
    0 < μ → μ ≤ UV → 0 < Λ → Λ < UV → BalancedMomenta legs q →
      Integrable (linearFlowIntegrand (I μ g) loop Λ UV legs q)
  flow : ∀ μ g loop Λ UV legs q,
    0 < μ → μ ≤ UV → 0 < Λ → Λ < UV → legs ≠ [] → BalancedMomenta legs q →
      HasDerivAt (fun scale : ℝ => I μ g loop scale UV legs q)
        (insertionHomogeneousRHS (A μ g) (I μ g) loop Λ UV legs q) Λ
  relevant_ir_regularity : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ UV → ReducedDirections legs d →
      totalDimension legs + d.length < 4 → ContDiffAt ℝ d.length (I μ g loop 0 UV legs) 0
  relevant_ir : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ UV → ReducedDirections legs d →
      totalDimension legs + d.length < 4 → momentumJet d (I μ g loop 0 UV legs) 0 = 0
  relevant_ir_limit : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ UV → ReducedDirections legs d → totalDimension legs + d.length < 4 →
      Tendsto (fun Λ => momentumJet d (I μ g loop Λ UV legs) 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  normalization : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ UV → ReducedDirections legs d →
      4 ≤ totalDimension legs + d.length → totalDimension legs + d.length ≤ 5 →
      marginalJet (I μ g) loop μ UV legs d =
        momentumJet d (fun q =>
          (if loop = 0 then integratedWardSeed e terms μ g else 0)
            legs (conservingMomenta legs q)) 0
  irrelevant_uv : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ UV → ReducedDirections legs d → totalDimension legs + d.length > 5 →
      momentumJet d (I μ g loop UV UV legs) q = 0

/-- The leading Ward residual is computed against this normalized
integrated response. Its vanishing is not inserted as a conclusion. -/
def leadingIntegratedWardResidual (anomaly response : ScaleCouplingFamily G) (order : ℕ) :
    ScaleCouplingFamily G :=
  fun μ g loop Λ UV legs q => anomaly μ g loop Λ UV legs q -
    if loop = order then response μ g 0 Λ UV legs q else 0

/-- The finite-cutoff seed has the SAME actual BV action, with no
independently chosen classical Ward tensor. -/
theorem integratedWardSeed_eq {B : InvariantForm G} (e : ColorFrame B)
    (terms : ℝ → List (LocalVertex G)) (μ g : ℝ) :
    integratedWardSeed e terms μ g =
      FullBV.densityAmplitude (FullBV.densityBracket (FullBV.masterActionDensity e g)
        (FullBV.densityOfVertices g (terms μ))) := rfl

end YangMills.IntegratedNormalization
