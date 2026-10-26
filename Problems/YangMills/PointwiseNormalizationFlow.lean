import Problems.YangMills.PointwiseNormalizationRegularity
import Problems.YangMills.InsertionScalarConvolution
import Problems.YangMills.OversubtractedFlow

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow MeasureTheory
variable {G : CompactSimpleGaugeGroup}
attribute [local irreducible] monomialsBelow

theorem linearFlowIntegrand_congr_atUV (F H : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ)
    (agree : ∀ l labels p, F l Λ UV labels p = H l Λ UV labels p)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand F loop Λ UV labels q p = linearFlowIntegrand H loop Λ UV labels q p := by
  unfold linearFlowIntegrand
  split_ifs
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro M hM
    apply Finset.sum_congr rfl
    intro N hN
    rw [agree]

theorem insertionHomogeneousRHS_congr_atUV (A F H : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ)
    (agree : ∀ l labels p, F l Λ UV labels p = H l Λ UV labels p)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) :
    insertionHomogeneousRHS A F loop Λ UV labels q =
      insertionHomogeneousRHS A H loop Λ UV labels q := by
  have hl : linearFlowRHS F loop Λ UV labels q = linearFlowRHS H loop Λ UV labels q := by
    unfold linearFlowRHS
    congr 1
    funext p
    exact linearFlowIntegrand_congr_atUV F H loop Λ UV agree labels q p
  have hq : quadraticFlowRHS A F loop Λ UV labels q = quadraticFlowRHS A H loop Λ UV labels q := by
    unfold quadraticFlowRHS
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro ss hs
    unfold quadraticSplit
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro M hM
    apply Finset.sum_congr rfl
    intro N hN
    rw [agree]
  simp only [insertionHomogeneousRHS, hl, hq]

/-- A proof device freezing only the UV parameter of the already COMPUTED
normalization coefficients. The differentiated flow cutoff remains free. -/
def frozenNormalizationResponse (L : ℝ → ℝ → InsertedFlowFamily G)
    (I : ScaleCouplingFamily G) (D : ℕ) (μ g UV : ℝ) : FlowFamily G :=
  finiteFlowSum (monomialsBelow G (D+1)) fun m =>
    scalarConvolution (fun r => normalizationCoefficient (L μ g) I D μ g UV r m)
      (L μ g [⟨m, 0⟩])

theorem frozenNormalizationResponse_atUV (L : ℝ → ℝ → InsertedFlowFamily G)
    (I : ScaleCouplingFamily G) (D : ℕ) (μ g UV : ℝ)
    (loop : ℕ) (Λ : ℝ) (labels : List (ExternalLeg G))
    (q : Fin labels.length → Spacetime) :
    frozenNormalizationResponse L I D μ g UV loop Λ UV labels q =
      pointwiseNormalizationResponse L I D μ g loop Λ UV labels q := rfl

/-- Integrability is inherited from the SAME single-insertion kernels by
actual finite Cauchy and finite-sum integral closure. -/
theorem pointwiseNormalizationResponse_integrable
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    {background : FlowFamily G} {F : OversubtractedFamily G}
    (D : ℕ) (μ g UV Λ : ℝ) (loop : ℕ)
    (h : InsertionFlowConditions background (L μ g) F μ)
    (hΛ : 0 < Λ) (hUV : Λ < UV)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) :
    Integrable (linearFlowIntegrand (pointwiseNormalizationResponse L I D μ g)
      loop Λ UV labels q) := by
  have he : linearFlowIntegrand (pointwiseNormalizationResponse L I D μ g) loop Λ UV labels q =
      linearFlowIntegrand (frozenNormalizationResponse L I D μ g UV) loop Λ UV labels q := by
    funext p
    apply linearFlowIntegrand_congr_atUV
    intro k ls pp
    exact (frozenNormalizationResponse_atUV L I D μ g UV k Λ ls pp).symm
  rw [he]
  exact linearFlowIntegrand_finiteFlowSum_integrable (monomialsBelow G (D+1))
    (fun m => scalarConvolution
      (fun r => normalizationCoefficient (L μ g) I D μ g UV r m) (L μ g [⟨m, 0⟩]))
    loop Λ UV labels q (by
      intro m hm
      exact linearFlowIntegrand_scalarConvolution_integrable
        (fun r => normalizationCoefficient (L μ g) I D μ g UV r m) (L μ g [⟨m, 0⟩])
        loop Λ UV labels q (fun k hk => h.single_loop_integrable m 0 k Λ UV labels q hΛ hUV))

/-- The actual computed finite pointwise response solves the SAME background
linear insertion flow. Its loop coefficients are the fixed triangular
normalization coefficients; no independent response RHS is chosen. -/
theorem pointwiseNormalizationResponse_flow
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    {background : FlowFamily G} {F : OversubtractedFamily G}
    (D : ℕ) (μ g UV Λ : ℝ) (loop : ℕ)
    (h : InsertionFlowConditions background (L μ g) F μ)
    (hΛ : 0 < Λ) (hUV : Λ < UV)
    (labels : List (ExternalLeg G)) (q : Fin labels.length → Spacetime) :
    HasDerivAt (fun scale => pointwiseNormalizationResponse L I D μ g loop scale UV labels q)
      (insertionHomogeneousRHS background (pointwiseNormalizationResponse L I D μ g)
        loop Λ UV labels q) Λ := by
  classical
  let c (m : LocalMonomial G) (r : ℕ) :=
    normalizationCoefficient (L μ g) I D μ g UV r m
  have hint (m : LocalMonomial G) (k : ℕ) :
      Integrable (linearFlowIntegrand (L μ g [⟨m, 0⟩]) k Λ UV labels q) :=
    h.single_loop_integrable m 0 k Λ UV labels q hΛ hUV
  have hcint (m : LocalMonomial G) :
      Integrable (linearFlowIntegrand (scalarConvolution (c m) (L μ g [⟨m, 0⟩]))
        loop Λ UV labels q) :=
    linearFlowIntegrand_scalarConvolution_integrable (c m) _ loop Λ UV labels q
      (fun k hk => hint m k)
  have hrhs : insertionHomogeneousRHS background (pointwiseNormalizationResponse L I D μ g)
      loop Λ UV labels q =
      ∑ m ∈ monomialsBelow G (D+1), ∑ r ∈ Finset.range (loop+1),
        c m r * insertionHomogeneousRHS background (L μ g [⟨m, 0⟩])
          (loop-r) Λ UV labels q := by
    rw [insertionHomogeneousRHS_congr_atUV background
      (pointwiseNormalizationResponse L I D μ g) (frozenNormalizationResponse L I D μ g UV)
      loop Λ UV (fun k ls pp =>
        (frozenNormalizationResponse_atUV L I D μ g UV k Λ ls pp).symm) labels q]
    rw [frozenNormalizationResponse, insertionHomogeneousRHS_finiteFlowSum_right _ _ _
      loop Λ UV labels q (fun m hm => hcint m)]
    apply Finset.sum_congr rfl
    intro m hm
    exact insertionHomogeneousRHS_scalarConvolution_right (c m) background
      (L μ g [⟨m, 0⟩]) loop Λ UV labels q (fun k hk => hint m k)
  rw [hrhs]
  change HasDerivAt (fun scale => ∑ m ∈ monomialsBelow G (D+1),
    ∑ r ∈ Finset.range (loop+1), c m r * L μ g [⟨m, 0⟩] (loop-r) scale UV labels q) _ Λ
  have hfun : (fun scale => ∑ m ∈ monomialsBelow G (D+1),
      ∑ r ∈ Finset.range (loop+1), c m r * L μ g [⟨m, 0⟩] (loop-r) scale UV labels q) =
      ∑ m ∈ monomialsBelow G (D+1), ∑ r ∈ Finset.range (loop+1),
        (fun scale => c m r * L μ g [⟨m, 0⟩] (loop-r) scale UV labels q) := by
    funext scale
    simp only [Finset.sum_apply]
  rw [hfun]
  apply HasDerivAt.sum
  intro m hm
  apply HasDerivAt.sum
  intro r hr
  exact (h.single_flow m 0 (loop-r) Λ UV labels q hΛ hUV).const_mul (c m r)

end YangMills.IntegratedNormalization
