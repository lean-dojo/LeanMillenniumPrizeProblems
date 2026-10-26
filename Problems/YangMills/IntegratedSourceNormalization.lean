import Problems.YangMills.IntegratedPointwiseComparison
import Problems.YangMills.IntegratedMarginalUniqueness
import Problems.YangMills.PerturbativeCoefficientLimits

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

def IntegratedWardConditions.reducedRegularity {B : InvariantForm G} {e : ColorFrame B}
    {A I : ScaleCouplingFamily G} {terms : ℝ → List (LocalVertex G)}
    (h : IntegratedWardConditions e A I terms) (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV) :
    ReducedLinearInsertionRegularity (A μ g) (I μ g) UV where
  smooth loop Λ labels hp hle := h.momentum_smooth μ g loop Λ UV labels hμ hUV hp hle
  continuous loop labels d q := h.positive_scale_jet_continuity μ g loop UV labels d q hμ hUV
  extension loop Λ labels q := h.reduced_extension μ g loop Λ UV labels q
  vacuum loop Λ q := h.statistics μ g loop Λ UV [] q (Or.inl (by simp [totalGhostNumber]))
  flow loop Λ labels q hp hlt hn hb := h.flow μ g loop Λ UV labels q hμ hUV hp hlt hn hb

/-- Dimension-four massless integrated primitive normalization is recovered
from the SAME fixed flow's pointwise insertions by the actual finite matrix
algorithm, rather than an independent renormalization-map witness. -/
theorem fixedFlow_integratedMarginal_normalization {B : InvariantForm G} {e : ColorFrame B}
    (S : FixedFlowSystem e) {I : ScaleCouplingFamily G} {terms : ℝ → List (LocalVertex G)}
    (hI : IntegratedMarginalConditions S.background I terms)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) :
    I μ g loop Λ UV labels q =
      conservingPointwiseNormalizationResponse S.insertions I 4 μ g loop Λ UV labels q := by
  exact integrated_eq_computed_pointwise_normalization S.insertions I 4 μ g UV
    ((S.insertion_equations μ hμ).per_coupling g) hUV (hI.reducedRegularity μ g UV hμ hUV)
    (fun l labels q π hb => hI.graded_symmetry μ g l μ UV labels q π hb)
    (fun l labels d hr hd q => hI.irrelevant_uv μ g l UV labels d q hμ hUV hr hd)
    (fun scale labels q hs hsUV hlen =>
      S.background_equations.no_free_interaction μ g scale UV labels q hlen)
    loop Λ hp hle labels q

/-- The dimension-five integrated sB0 response has the same computed
pointwise bridge for the SAME fixed flow and actual full BV seed. This
establishes the normalization comparison, not anomaly cancellation or
existence of a cohomological primitive. -/
theorem fixedFlow_integratedWard_normalization {B : InvariantForm G} {e : ColorFrame B}
    (S : FixedFlowSystem e) {I : ScaleCouplingFamily G} {terms : ℝ → List (LocalVertex G)}
    (hI : IntegratedWardConditions e S.background I terms)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (loop : ℕ) (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) :
    I μ g loop Λ UV labels q =
      conservingPointwiseNormalizationResponse S.insertions I 5 μ g loop Λ UV labels q := by
  exact integrated_eq_computed_pointwise_normalization S.insertions I 5 μ g UV
    ((S.insertion_equations μ hμ).per_coupling g) hUV (hI.reducedRegularity μ g UV hμ hUV)
    (fun l labels q π hb => hI.graded_symmetry μ g l μ UV labels q π hb)
    (fun l labels d hr hd q => hI.irrelevant_uv μ g l UV labels d q hμ hUV hr hd)
    (fun scale labels q hs hsUV hlen =>
      S.background_equations.no_free_interaction μ g scale UV labels q hlen)
    loop Λ hp hle labels q

end YangMills.IntegratedNormalization
