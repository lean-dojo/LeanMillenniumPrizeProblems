import Problems.YangMills.FiniteWardRestoration

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
FHH1511.09425 (84),(94), TableII and (123): an integrated dimension-four
insertion is an independent conserving-momentum linear response with zero
relevant IR boundary, not the integral of the pointwise insertion family.
The following concrete normalization keeps the massless background class.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- A fixed dimension-four integrated insertion has its prescribed tree
marginal tensor and zero higher-loop marginal renormalizations. -/
def integratedMarginalSeed (terms : List (LocalVertex G)) (g : ℝ) (loop : ℕ) :
    OrderedAmplitude G :=
  if loop = 0 then localPolynomialAmplitude terms g else 0

/-- The SAME covariance and background contraction as (94), with its
independent massless integrated boundary conditions from TableII. No
identification with a pointwise insertion at zero insertion momentum is made. -/
structure IntegratedMarginalConditions (A I : ScaleCouplingFamily G)
    (terms : ℝ → List (LocalVertex G)) : Prop where
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
    (totalGhostNumber legs ≠ 0 ∨ oddCount legs % 2 ≠ 0) → I μ g loop Λ UV legs q = 0
  graded_symmetry : ∀ μ g loop Λ UV legs q (π : Equiv.Perm (Fin legs.length)),
    BalancedMomenta legs q →
    I μ g loop Λ UV (permutedLegs legs π) (permutedMomenta legs π q) =
      permutationSign legs π * I μ g loop Λ UV legs q
  vacuum_subtraction : ∀ μ g loop Λ UV q, I μ g loop Λ UV [] q = 0
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
  marginal : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ UV → ReducedDirections legs d → totalDimension legs + d.length = 4 →
      marginalJet (I μ g) loop μ UV legs d =
        momentumJet d
          (fun q => integratedMarginalSeed (terms μ) g loop legs (conservingMomenta legs q)) 0
  irrelevant_uv : ∀ μ g loop UV legs (d : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ UV → ReducedDirections legs d → totalDimension legs + d.length > 4 →
      momentumJet d (I μ g loop UV UV legs) q = 0

/-- The leading finite renormalization uses the renormalized INTEGRATED
response, including its actual UV counterterms. It is not subtraction of
its tree marginal seed at every momentum and cutoff. Higher orders require
nonlinear reflow and are not defined by this relation. -/
def LeadingIntegratedShift (before after response : ScaleCouplingFamily G) (order : ℕ) : Prop :=
  ∀ μ g loop, loop ≤ order → ∀ Λ UV legs q,
    after μ g loop Λ UV legs q = before μ g loop Λ UV legs q -
      if loop = order then response μ g 0 Λ UV legs q else 0

/-- Momentum derivatives are additive on the actual regularity domain;
no linearity is claimed for totalized derivatives of arbitrary functions. -/
theorem momentumJet_sub_regular {legs : List (ExternalLeg G)}
    (d : List (Fin legs.length × Fin 4))
    (F H : (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime)
    (hF : ContDiffAt ℝ d.length F q) (hH : ContDiffAt ℝ d.length H q) :
    momentumJet d (fun p => F p - H p) q = momentumJet d F q - momentumJet d H q := by
  unfold momentumJet
  simp only [sub_eq_add_neg]
  rw [fun_iteratedFDeriv_add_apply hF hH.neg]
  rw [show (fun p => -H p) = -H from rfl, iteratedFDeriv_neg_apply]
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.neg_apply]

/-- Source TableII's zero relevant IR jets are preserved at the leading
restoration order by a massless integrated response. No broader relevant
normalization or physical mass term is needed for this step. -/
theorem LeadingIntegratedShift.relevant_ir {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {before after response : ScaleCouplingFamily G}
    {terms : ℝ → List (LocalVertex G)} {order : ℕ}
    (hA : CoefficientFlowConditions e scheme before)
    (hI : IntegratedMarginalConditions before response terms)
    (hshift : LeadingIntegratedShift before after response order)
    (μ g UV : ℝ) (loop : ℕ) (hle : loop ≤ order)
    (legs : List (ExternalLeg G)) (d : List (Fin legs.length × Fin 4))
    (hμ : 0 < μ) (hUV : μ ≤ UV) (hd : ReducedDirections legs d)
    (hdeg : totalDimension legs + d.length < 4) :
    momentumJet d (after μ g loop 0 UV legs) 0 = 0 := by
  have hf : after μ g loop 0 UV legs = fun q => before μ g loop 0 UV legs q -
      if loop = order then response μ g 0 0 UV legs q else 0 := by
    funext q
    exact hshift μ g loop hle 0 UV legs q
  rw [hf]
  by_cases hl : loop = order
  · simp only [hl, if_true]
    rw [momentumJet_sub_regular d _ _ 0
      (hA.relevant_ir_regularity μ g order UV legs d hμ hUV hd hdeg)
      (hI.relevant_ir_regularity μ g 0 UV legs d hμ hUV hd hdeg),
      hA.relevant_ir μ g order UV legs d hμ hUV hd hdeg,
      hI.relevant_ir μ g 0 UV legs d hμ hUV hd hdeg, sub_self]
  · simpa only [hl, if_false, sub_zero] using!
      hA.relevant_ir μ g loop UV legs d hμ hUV hd hdeg

/-- The finite leading change is entirely in the dimension-four marginal
normalization. The relevant IR jets remain the same by the preceding theorem. -/
theorem LeadingIntegratedShift.marginal {B : InvariantForm G} {e : ColorFrame B}
    {scheme : LocalMarginalData G} {before after response : ScaleCouplingFamily G}
    {terms : ℝ → List (LocalVertex G)} {order : ℕ}
    (hA : CoefficientFlowConditions e scheme before)
    (hI : IntegratedMarginalConditions before response terms)
    (hshift : LeadingIntegratedShift before after response order)
    (μ g UV : ℝ) (legs : List (ExternalLeg G)) (d : List (Fin legs.length × Fin 4))
    (hμ : 0 < μ) (hUV : μ ≤ UV) (hd : ReducedDirections legs d)
    (hdeg : totalDimension legs + d.length = 4) :
    marginalJet (after μ g) order μ UV legs d =
      momentumJet d
        (fun q => marginalNormalization e scheme order g legs (conservingMomenta legs q)) 0 -
      momentumJet d
        (fun q => localPolynomialAmplitude (terms μ) g legs (conservingMomenta legs q)) 0 := by
  have hf : after μ g order μ UV legs = fun q => before μ g order μ UV legs q -
      response μ g 0 μ UV legs q := by
    funext q
    simpa only [if_pos rfl] using! hshift μ g order (le_refl order) μ UV legs q
  change momentumJet d (after μ g order μ UV legs) 0 = _
  rw [hf, momentumJet_sub_regular d _ _ 0
    ((hA.momentum_smooth μ g order μ UV legs hμ hUV hμ hUV).contDiffAt.of_le (by exact_mod_cast (le_top : (d.length : ℕ∞) ≤ ⊤)))
    ((hI.momentum_smooth μ g 0 μ UV legs hμ hUV hμ hUV).contDiffAt.of_le (by exact_mod_cast (le_top : (d.length : ℕ∞) ≤ ⊤)))]
  have hbefore := hA.marginal μ g order UV legs d hμ hUV hd hdeg
  have hresponse := hI.marginal μ g 0 UV legs d hμ hUV hd hdeg
  simp only [marginalJet] at hbefore
  simp only [marginalJet, integratedMarginalSeed, ↓reduceIte] at hresponse
  rw [hbefore, hresponse]

/-- The actual finite-cutoff seed includes the UV endpoint of the
renormalized integrated response, not just its marginal tree polynomial. -/
theorem LeadingIntegratedShift.ultraviolet {before after response : ScaleCouplingFamily G}
    {order : ℕ} (h : LeadingIntegratedShift before after response order)
    (μ g UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    after μ g order UV UV legs q = before μ g order UV UV legs q -
      response μ g 0 UV UV legs q := by
  simpa only [if_pos rfl] using! h μ g order (le_refl order) UV UV legs q

/-- The shifted Ward seed is the defect of the SAME actual regulated
background, with the actual integrated-response UV counterterms. -/
theorem LeadingIntegratedShift.bare_defect
    {before after response : ScaleCouplingFamily G} {order : ℕ}
    (h : LeadingIntegratedShift before after response order) (μ g UV : ℝ) :
    bareActionWardDefect (after μ g) order UV =
      bareActionWardDefect
        (FiniteWard.boundaryShift (before μ g) order (response μ g 0 UV UV)) order UV := by
  apply FiniteWard.bareActionWardDefect_congr_prefix
  intro loop hloop
  funext legs q
  exact h μ g loop hloop UV UV legs q

/-- The older literal-polynomial UV shift is a special presentation. The
precise extra condition it needs is equality with the renormalized response's
UV endpoint; it does NOT follow merely from the marginal normalization. -/
theorem LeadingIntegratedShift.raw_boundary_iff
    {before after response : ScaleCouplingFamily G} {order : ℕ}
    (h : LeadingIntegratedShift before after response order) (μ g : ℝ)
    (P : OrderedAmplitude G) :
    FiniteWard.UVBoundaryStep (before μ g) (after μ g) order P ↔
      ∀ UV : ℝ, 0 < UV → response μ g 0 UV UV = P := by
  constructor
  · intro hb UV hUV
    funext legs q
    have hs := h.ultraviolet μ g UV legs q
    have hr := hb order (le_refl order) UV hUV legs q
    simp only [FiniteWard.boundaryShift, ↓reduceIte] at hr
    exact sub_right_inj.mp (hs.symm.trans hr)
  · intro hend loop hloop UV hUV legs q
    rw [h μ g loop hloop UV UV legs q]
    unfold FiniteWard.boundaryShift
    by_cases hl : loop = order
    · simp only [hl, ↓reduceIte, hend UV hUV]
    · simp only [hl, if_false]

/-- A source massless finite-normalization step. The new background is
required to solve the actual nonlinear flow; a leading linear response
alone is never promoted to a full nonlinear solution. Ward-anomaly removal
is a theorem still to derive from the computed seed and primitive. -/
structure IntegratedFiniteNormalizationStep {B : InvariantForm G} (e : ColorFrame B)
    (beforeScheme afterScheme : LocalMarginalData G)
    (before after response : ScaleCouplingFamily G) (terms : ℝ → List (LocalVertex G))
    (order : ℕ) : Prop where
  before_flow : CoefficientFlowConditions e beforeScheme before
  after_flow : CoefficientFlowConditions e afterScheme after
  integrated_response : IntegratedMarginalConditions before response terms
  leading_shift : LeadingIntegratedShift before after response order

/-- Explicit compatibility with the previous literal-polynomial
RestorationStep API. Such a step forces the additional endpoint identity;
it is not inferred just from equal marginal tensors at mu. -/
theorem restorationStep_integrated_endpoint
    {B : InvariantForm G} {e : ColorFrame B}
    {before after response : ScaleCouplingFamily G}
    {L : ℝ → ℝ → InsertedFlowFamily G} {anomaly : ℝ → ℝ → FlowFamily G}
    {order : ℕ} (step : YangMills.FiniteWard.RestorationStep e before after L anomaly order)
    (hshift : LeadingIntegratedShift before after response order)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : 0 < UV) :
    response μ g 0 UV UV =
      localPolynomialAmplitude ((step.correction μ).atScale μ) g := by
  exact (hshift.raw_boundary_iff μ g _).mp (step.boundary μ g hμ) UV hUV

end YangMills.IntegratedNormalization
