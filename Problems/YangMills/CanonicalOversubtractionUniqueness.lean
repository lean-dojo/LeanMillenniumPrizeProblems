import Problems.YangMills.CanonicalLinearInsertionUniqueness
import Problems.YangMills.InsertionExtractionCongruence

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped ContDiff
open Filter
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Analytic hypotheses of the actual inhomogeneous oversubtraction equation
with its fixed SAME single-insertion source. -/
structure InhomogeneousInsertionRegularity (background source F : FlowFamily G) (UV : ℝ) : Prop where
  smooth : ∀ loop Λ legs, 0 < Λ → Λ ≤ UV → ContDiff ℝ ∞ (F loop Λ UV legs)
  continuous : ∀ loop legs directions q,
    ContinuousOn (fun Λ => momentumJet directions (F loop Λ UV legs) q) (Set.Ioc 0 UV)
  flow : ∀ loop Λ legs q, 0 < Λ → Λ < UV →
    HasDerivAt (fun scale => F loop scale UV legs q)
      (insertionHomogeneousRHS background F loop Λ UV legs q - source loop Λ UV legs q) Λ

/-- Changing only the written source by a proved equality leaves the SAME
actual differential equation unchanged on its physical cutoff interval. -/
def InhomogeneousInsertionRegularity.changeSource
    {background source target F : FlowFamily G} {UV : ℝ}
    (h : InhomogeneousInsertionRegularity background source F UV)
    (eq : ∀ loop Λ legs q, 0 < Λ → Λ < UV → source loop Λ UV legs q = target loop Λ UV legs q) :
    InhomogeneousInsertionRegularity background target F UV where
  smooth := h.smooth
  continuous := h.continuous
  flow loop Λ legs q hp hlt := by
    simpa only [eq loop Λ legs q hp hlt] using! h.flow loop Λ legs q hp hlt

/-- Original strict-low/nonstrict-high canonical rows determine the actual
inhomogeneous response for its fixed SAME source and background. -/
theorem InhomogeneousInsertionRegularity.unique_of_canonical_projectors
    {background source F H : FlowFamily G} {UV μ : ℝ}
    (hF : InhomogeneousInsertionRegularity background source F UV)
    (hH : InhomogeneousInsertionRegularity background source H UV) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (degree : ℕ)
    (free : ∀ Λ legs q, 0 < Λ → Λ < UV → legs.length ≤ 2 → background 0 Λ UV legs q = 0)
    (gradedF : ∀ loop Λ legs q (pi : Equiv.Perm (Fin legs.length)),
      F loop Λ UV (permutedLegs legs pi) (permutedMomenta legs pi q) =
        permutationSign legs pi * F loop Λ UV legs q)
    (gradedH : ∀ loop Λ legs q (pi : Equiv.Perm (Fin legs.length)),
      H loop Λ UV (permutedLegs legs pi) (permutedMomenta legs pi q) =
        permutationSign legs pi * H loop Λ UV legs q)
    (low : ∀ loop (m : LocalMonomial G), m.Admissible → m.dimension < degree →
      extractCoefficient m (F loop μ UV) 0 = extractCoefficient m (H loop μ UV) 0)
    (high : ∀ loop (m : LocalMonomial G), m.Admissible → degree ≤ m.dimension → ∀ p,
      extractCoefficient m (F loop UV UV) p = extractCoefficient m (H loop UV UV) p)
    (loop : ℕ) (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    F loop Λ UV legs q = H loop Λ UV legs q := by
  have uvpos := hμ.trans_le hUV
  have main : ∀ loop n, ∀ legs : List (ExternalLeg G), legs.length = n →
      ∀ Λ, 0 < Λ → Λ ≤ UV → ∀ q, F loop Λ UV legs q = H loop Λ UV legs q := by
    intro loop
    induction loop using Nat.strong_induction_on with
    | h loop ihloop =>
      intro n
      induction n using Nat.strong_induction_on with
      | h n iharity =>
        have rhs : ∀ ls : List (ExternalLeg G), ls.length = n → ∀ t p, 0 < t → t < UV →
            insertionHomogeneousRHS background F loop t UV ls p =
              insertionHomogeneousRHS background H loop t UV ls p := by
          intro ls hls t p ht htUV
          apply insertionHomogeneousRHS_congr_lower
          · intro l smaller p' hl
            rcases hl with hl | ⟨hl, hsmall⟩
            · exact ihloop l hl smaller.length smaller rfl t ht htUV.le p'
            · subst l
              exact iharity smaller.length (by omega) smaller rfl t ht htUV.le p'
          · exact fun smaller p' hs => free t smaller p' ht htUV hs
        have constant : ∀ ls : List (ExternalLeg G), ls.length = n → ∀ t, 0 < t → t ≤ UV →
            (fun p => F loop UV UV ls p - H loop UV UV ls p) =
              (fun p => F loop t UV ls p - H loop t UV ls p) := by
          intro ls hls t ht htUV
          funext p
          apply positiveScale_constancy (UV := UV)
            (f := fun s => F loop s UV ls p - H loop s UV ls p)
          · have cf := hF.continuous loop ls [] p
            have ch := hH.continuous loop ls [] p
            have cf' : ContinuousOn (fun s => F loop s UV ls p) (Set.Ioc 0 UV) := by
              simpa [momentumJet, iteratedFDeriv_zero_apply] using! cf
            have ch' : ContinuousOn (fun s => H loop s UV ls p) (Set.Ioc 0 UV) := by
              simpa [momentumJet, iteratedFDeriv_zero_apply] using! ch
            exact cf'.sub ch'
          · intro s hs hsUV
            have hd := (hF.flow loop s ls p hs hsUV).sub (hH.flow loop s ls p hs hsUV)
            simpa only [rhs ls hls s p hs hsUV, sub_self] using! hd
          all_goals first | assumption | exact le_rfl
        let A : OrderedAmplitude G := fun ls p => F loop UV UV ls p - H loop UV UV ls p
        have smooth : ∀ ls, ContDiff ℝ ∞ (A ls) :=
          fun ls => (hF.smooth loop UV ls uvpos le_rfl).sub (hH.smooth loop UV ls uvpos le_rfl)
        have graded : ∀ ls p (pi : Equiv.Perm (Fin ls.length)),
            A (permutedLegs ls pi) (permutedMomenta ls pi p) = permutationSign ls pi * A ls p := by
          intro ls p pi
          dsimp only [A]
          rw [gradedF, gradedH, mul_sub]
        have zero := canonicalProjectorDeterminacy (arityRestricted n A)
          (arityRestricted_smooth n A smooth) (arityRestricted_graded n A graded) degree
          (by
            intro m hm hd
            rw [extractCoefficient_arityRestricted]
            split_ifs with hlen
            · by_cases strict : m.dimension < degree
              · have eq : A m.legs = fun p => F loop μ UV m.legs p - H loop μ UV m.legs p :=
                  constant m.legs hlen μ hμ hUV
                unfold extractCoefficient
                rw [eq]
                change extractCoefficient m (fun ls p => F loop μ UV ls p - H loop μ UV ls p) 0 = 0
                rw [extractCoefficient_difference_smooth m _ _
                  (fun ls => hF.smooth loop μ ls hμ hUV) (fun ls => hH.smooth loop μ ls hμ hUV),
                  low loop m hm strict, sub_self]
              · change extractCoefficient m (fun ls p => F loop UV UV ls p - H loop UV UV ls p) 0 = 0
                rw [extractCoefficient_difference_smooth m _ _
                  (fun ls => hF.smooth loop UV ls uvpos le_rfl)
                  (fun ls => hH.smooth loop UV ls uvpos le_rfl),
                  high loop m hm (by omega) 0, sub_self]
            · rfl)
          (by
            intro m hm hd p
            rw [extractCoefficient_arityRestricted]
            split_ifs
            · change extractCoefficient m (fun ls p => F loop UV UV ls p - H loop UV UV ls p) p = 0
              rw [extractCoefficient_difference_smooth m _ _
                (fun ls => hF.smooth loop UV ls uvpos le_rfl)
                (fun ls => hH.smooth loop UV ls uvpos le_rfl), high loop m hm (by omega) p, sub_self]
            · rfl)
        intro ls hls t ht htUV p
        have hz := zero ls p
        simp only [arityRestricted, if_pos hls, A] at hz
        have hv := congrFun (constant ls hls t ht htUV) p
        exact sub_eq_zero.mp (hv.symm.trans hz)
  exact main loop legs.length legs rfl Λ hp hle q


/-- The SAME insertion cluster with its final point moved to zero. -/
def InsertionCluster.originCluster (input : InsertionCluster G) : InsertionCluster G :=
  ⟨shiftInsertions input.initial input.last.position, ⟨input.last.monomial,0⟩⟩

theorem InsertionCluster.originCluster_insertions (input : InsertionCluster G) :
    input.originCluster.insertions = input.atOrigin := by
  simp [InsertionCluster.originCluster, InsertionCluster.insertions,
    InsertionCluster.atOrigin, shiftInsertions, List.map_append]

def InsertionFlowConditions.oversubtractionRegularity
    {background : FlowFamily G} {L : InsertedFlowFamily G}
    {F : OversubtractedFamily G} {μ : ℝ}
    (h : InsertionFlowConditions background L F μ)
    (D : ℕ) (input : InsertionCluster G) (UV : ℝ) :
    InhomogeneousInsertionRegularity background (oversubtractionSource L input.atOrigin)
      (F D input.atOrigin) UV where
  smooth loop Λ legs hp hle := h.oversubtraction_boundary.smooth D input.atOrigin loop Λ UV hp hle legs
  continuous loop legs directions q :=
    h.oversubtraction_boundary.scale_jet_continuous D input.atOrigin loop UV legs directions q
  flow loop Λ legs q hp hlt := by
    have hf := h.oversubtraction_flow D input.originCluster loop Λ UV legs q hp hlt
    simpa only [InsertionCluster.originCluster_insertions, oversubtractionFlowRHS] using! hf

/-- Actual multiple-insertion oversubtractions are unique for the SAME
single-insertion source and background, under precisely (4.4)'s <D/≥D rows. -/
theorem InsertionFlowConditions.oversubtraction_unique_of_free
    {background : FlowFamily G} {L : InsertedFlowFamily G}
    {F H : OversubtractedFamily G} {μ UV : ℝ}
    (hF : InsertionFlowConditions background L F μ)
    (hH : InsertionFlowConditions background L H μ) (hUV : μ ≤ UV)
    (free : ∀ Λ legs q, 0 < Λ → Λ < UV → legs.length ≤ 2 → background 0 Λ UV legs q = 0)
    (D : ℕ) (input : InsertionCluster G) (loop : ℕ) (Λ : ℝ)
    (hp : 0 < Λ) (hle : Λ ≤ UV) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    F D input.insertions loop Λ UV legs q = H D input.insertions loop Λ UV legs q := by
  have origin : ∀ loop Λ, 0 < Λ → Λ ≤ UV → ∀ legs q,
      F D input.atOrigin loop Λ UV legs q = H D input.atOrigin loop Λ UV legs q := by
    apply InhomogeneousInsertionRegularity.unique_of_canonical_projectors
      (hF.oversubtractionRegularity D input UV) (hH.oversubtractionRegularity D input UV)
      hF.oversubtraction_boundary.scale_positive hUV D free
    · exact fun loop Λ legs q pi => hF.oversubtraction_graded_symmetry D input.atOrigin loop Λ UV legs q pi
    · exact fun loop Λ legs q pi => hH.oversubtraction_graded_symmetry D input.atOrigin loop Λ UV legs q pi
    · intro loop m hm hd
      rw [hF.oversubtraction_boundary.low D input m hm hd loop UV hUV,
        hH.oversubtraction_boundary.low D input m hm hd loop UV hUV]
    · intro loop m hm hd p
      rw [hF.oversubtraction_boundary.high D input m hm hd loop UV hUV p,
        hH.oversubtraction_boundary.high D input m hm hd loop UV hUV p]
  rw [hF.oversubtraction_boundary.translation D input.insertions input.last.position loop Λ UV legs q,
    hH.oversubtraction_boundary.translation D input.insertions input.last.position loop Λ UV legs q]
  rw [show shiftInsertions input.insertions input.last.position = input.atOrigin from rfl,
    origin loop Λ hp hle legs q]

/-- The fixed actual G/action background supplies the free-tree premise. -/
theorem InsertionFlowConditions.oversubtraction_unique
    {form : InvariantForm G} {e : ColorFrame form} {scheme : LocalMarginalData G}
    {background : ScaleCouplingFamily G} (hb : CoefficientFlowConditions e scheme background)
    {L : InsertedFlowFamily G} {F H : OversubtractedFamily G} {μ g UV : ℝ}
    (hF : InsertionFlowConditions (background μ g) L F μ)
    (hH : InsertionFlowConditions (background μ g) L H μ) (hUV : μ ≤ UV)
    (D : ℕ) (input : InsertionCluster G) (loop : ℕ) (Λ : ℝ)
    (hp : 0 < Λ) (hle : Λ ≤ UV) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    F D input.insertions loop Λ UV legs q = H D input.insertions loop Λ UV legs q :=
  hF.oversubtraction_unique_of_free hH hUV
    (fun Λ legs q _ _ hlen => hb.no_free_interaction μ g Λ UV legs q hlen)
    D input loop Λ hp hle legs q

theorem InsertionFlowConditions.oversubtraction_unique_of_single_equality
    {background : FlowFamily G} {L M : InsertedFlowFamily G}
    {F H : OversubtractedFamily G} {μ UV : ℝ}
    (hF : InsertionFlowConditions background L F μ)
    (hH : InsertionFlowConditions background M H μ) (hUV : μ ≤ UV)
    (free : ∀ Λ legs q, 0 < Λ → Λ < UV → legs.length ≤ 2 → background 0 Λ UV legs q = 0)
    (singles : ∀ a r Λ legs q, 0 < Λ → Λ ≤ UV →
      L [a] r Λ UV legs q = M [a] r Λ UV legs q)
    (D : ℕ) (input : InsertionCluster G) (loop : ℕ) (Λ : ℝ)
    (hp : 0 < Λ) (hle : Λ ≤ UV) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    F D input.insertions loop Λ UV legs q = H D input.insertions loop Λ UV legs q := by
  have origin : ∀ loop Λ, 0 < Λ → Λ ≤ UV → ∀ legs q,
      F D input.atOrigin loop Λ UV legs q = H D input.atOrigin loop Λ UV legs q := by
    apply InhomogeneousInsertionRegularity.unique_of_canonical_projectors
      (hF.oversubtractionRegularity D input UV)
      ((hH.oversubtractionRegularity D input UV).changeSource (by
        intro r Λ legs q hp hlt
        apply oversubtractionSource_congr_at
        intro a k ls p
        exact (singles a k Λ ls p hp hlt.le).symm))
      hF.oversubtraction_boundary.scale_positive hUV D free
    · exact fun loop Λ legs q pi => hF.oversubtraction_graded_symmetry D input.atOrigin loop Λ UV legs q pi
    · exact fun loop Λ legs q pi => hH.oversubtraction_graded_symmetry D input.atOrigin loop Λ UV legs q pi
    · intro loop m hm hd
      rw [hF.oversubtraction_boundary.low D input m hm hd loop UV hUV,
        hH.oversubtraction_boundary.low D input m hm hd loop UV hUV]
    · intro loop m hm hd p
      rw [hF.oversubtraction_boundary.high D input m hm hd loop UV hUV p,
        hH.oversubtraction_boundary.high D input m hm hd loop UV hUV p]
  rw [hF.oversubtraction_boundary.translation D input.insertions input.last.position loop Λ UV legs q,
    hH.oversubtraction_boundary.translation D input.insertions input.last.position loop Λ UV legs q]
  rw [show shiftInsertions input.insertions input.last.position = input.atOrigin from rfl,
    origin loop Λ hp hle legs q]

/-- Uniqueness across two auxiliary insertion families: equality of their
actual singles is derived from the SAME fixed action, not assumed as data. -/
theorem InsertionFlowConditions.oversubtraction_unique_between
    {form : InvariantForm G} {e : ColorFrame form} {scheme : LocalMarginalData G}
    {background : ScaleCouplingFamily G} (hb : CoefficientFlowConditions e scheme background)
    {L M : InsertedFlowFamily G} {F H : OversubtractedFamily G} {μ g UV : ℝ}
    (hF : InsertionFlowConditions (background μ g) L F μ)
    (hH : InsertionFlowConditions (background μ g) M H μ) (hUV : μ ≤ UV)
    (D : ℕ) (input : InsertionCluster G) (loop : ℕ) (Λ : ℝ)
    (hp : 0 < Λ) (hle : Λ ≤ UV) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    F D input.insertions loop Λ UV legs q = H D input.insertions loop Λ UV legs q := by
  apply hF.oversubtraction_unique_of_single_equality hH hUV
    (fun Λ legs q _ _ hlen => hb.no_free_interaction μ g Λ UV legs q hlen)
    _ D input loop Λ hp hle legs q
  intro a r Λ legs q hp hle
  exact InsertionFlowConditions.single_unique hb hF hH hUV a.monomial a.position r Λ hp hle legs q

/-- The literal triangular OPE extractor has a uniquely fixed prediction
for the SAME G/action background and canonical normalization prescription. -/
theorem InsertionFlowConditions.regulatedOPECoefficient_unique
    {form : InvariantForm G} {e : ColorFrame form} {scheme : LocalMarginalData G}
    {background : ScaleCouplingFamily G} (hb : CoefficientFlowConditions e scheme background)
    {L M : InsertedFlowFamily G} {F H : OversubtractedFamily G} {μ g UV : ℝ}
    (hF : InsertionFlowConditions (background μ g) L F μ)
    (hH : InsertionFlowConditions (background μ g) M H μ) (hUV : μ ≤ UV)
    (input : InsertionCluster G) (loop : ℕ) (output : LocalMonomial G) :
    regulatedOPECoefficient L F μ UV input loop output =
      regulatedOPECoefficient M H μ UV input loop output := by
  apply regulatedOPECoefficient_congr_at _ input _ loop output
  · intro a r legs q
    exact InsertionFlowConditions.single_unique hb hF hH hUV a.monomial a.position r μ
      hF.single_boundary.scale_positive hUV legs q
  · intro r legs q
    exact InsertionFlowConditions.oversubtraction_unique_between hb hF hH hUV 0 input r μ
      hF.single_boundary.scale_positive hUV legs q

/-- The actual cofinal UV scalar limit is unique across auxiliary families
with the SAME fixed G/action and normalization prescription. Contact
extensions of distributions are not declared unique by this scalar theorem. -/
theorem InsertionFlowConditions.ultravioletOPECoefficient_unique
    {form : InvariantForm G} {e : ColorFrame form} {scheme : LocalMarginalData G}
    {background : ScaleCouplingFamily G} (hb : CoefficientFlowConditions e scheme background)
    {L M : InsertedFlowFamily G} {F H : OversubtractedFamily G} {μ g : ℝ}
    (hF : InsertionFlowConditions (background μ g) L F μ)
    (hH : InsertionFlowConditions (background μ g) M H μ)
    (input : InsertionCluster G) (loop : ℕ) (output : LocalMonomial G) {a b : ℂ}
    (ha : IsUltravioletOPECoefficient L F μ input loop output a)
    (hb' : IsUltravioletOPECoefficient M H μ input loop output b) : a = b := by
  have eq : ∀ᶠ UV : ℝ in Filter.atTop,
      regulatedOPECoefficient M H μ UV input loop output =
        regulatedOPECoefficient L F μ UV input loop output := by
    filter_upwards [Filter.eventually_ge_atTop μ] with UV hUV
    exact (InsertionFlowConditions.regulatedOPECoefficient_unique hb hF hH hUV input loop output).symm
  exact tendsto_nhds_unique ha.2 (hb'.2.congr' eq)

end YangMills.PerturbativeFlow
