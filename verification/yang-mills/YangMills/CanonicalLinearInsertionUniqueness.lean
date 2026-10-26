import YangMills.LinearInsertionUniqueness
import YangMills.CanonicalProjectorDeterminacy
import YangMills.OversubtractedFlow

noncomputable section
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Canonical extraction is genuinely linear on the actual smooth amplitudes. -/
theorem extractCoefficient_difference_smooth (m : LocalMonomial G)
    (F H : OrderedAmplitude G) (hF : ∀ legs, ContDiff ℝ ∞ (F legs))
    (hH : ∀ legs, ContDiff ℝ ∞ (H legs)) (q : Fin m.legs.length → Spacetime) :
    extractCoefficient m (fun legs p => F legs p - H legs p) q =
      extractCoefficient m F q - extractCoefficient m H q := by
  change (Complex.I ^ m.momentumDirections.length / (m.momentumFactorial : ℂ)) *
    momentumJet m.momentumDirections (fun p => F m.legs p - H m.legs p) q = _
  rw [momentumJet_difference_smooth _ (hF _) (hH _)]
  exact mul_sub _ _ _

/-- The actual insertion boundary regularity supplies the actual homogeneous
linear flow hypotheses, without an additional coordinate normalization. -/
def InsertionFlowConditions.singleRegularity {background : FlowFamily G}
    {L : InsertedFlowFamily G} {F : OversubtractedFamily G} {μ : ℝ}
    (h : InsertionFlowConditions background L F μ)
    (A : LocalMonomial G) (x : Spacetime) (UV : ℝ) :
    LinearInsertionRegularity background (L [⟨A,x⟩]) UV where
  smooth loop Λ legs hp hle := (h.single_boundary.smooth _ loop Λ UV hp hle legs).of_le (by simp)
  continuous loop legs directions q :=
    h.single_boundary.scale_jet_continuous _ loop UV legs directions q
  flow loop Λ legs q hp hlt := h.single_flow A x loop Λ UV legs q hp hlt

/-- Restriction to a fixed external arity preserves the actual canonical
projectors and full graded symmetry. It is only a proof device. -/
def arityRestricted (n : ℕ) (A : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => if legs.length = n then A legs q else 0

lemma arityRestricted_eq (n : ℕ) (A : OrderedAmplitude G) (legs : List (ExternalLeg G)) :
    arityRestricted n A legs = if legs.length = n then A legs else 0 := by
  split_ifs with h <;> funext q <;> simp [arityRestricted,h]

lemma arityRestricted_smooth (n : ℕ) (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs)) :
    ∀ legs, ContDiff ℝ ∞ (arityRestricted n A legs) := by
  intro legs
  rw [arityRestricted_eq]
  split_ifs
  · exact smooth legs
  · exact contDiff_const

lemma extractCoefficient_arityRestricted (n : ℕ) (A : OrderedAmplitude G)
    (m : LocalMonomial G) (q : Fin m.legs.length → Spacetime) :
    extractCoefficient m (arityRestricted n A) q =
      if m.legs.length = n then extractCoefficient m A q else 0 := by
  unfold extractCoefficient
  rw [arityRestricted_eq]
  split_ifs
  · rfl
  · change _ * (iteratedFDeriv ℝ _ (fun _ : Fin m.legs.length → Spacetime => (0:ℂ)) q) _ = 0
    rw [iteratedFDeriv_zero_fun]
    simp

lemma arityRestricted_graded (n : ℕ) (A : OrderedAmplitude G)
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q) :
    ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      arityRestricted n A (permutedLegs legs pi) (permutedMomenta legs pi q) =
        permutationSign legs pi * arityRestricted n A legs q := by
  intro legs q pi
  have hlen : (permutedLegs legs pi).length = legs.length := by
    simp [permutedLegs]
  by_cases h : legs.length = n
  · simpa only [arityRestricted, hlen, if_pos h] using graded legs q pi
  · simp only [arityRestricted, hlen, if_neg h, mul_zero]

/-- The source's admissible canonical low/high rows determine the actual
homogeneous insertion response. No all-coordinate boundary is substituted. -/
theorem LinearInsertionRegularity.unique_of_canonical_projectors
    {background F H : FlowFamily G} {UV μ : ℝ}
    (hF : LinearInsertionRegularity background F UV)
    (hH : LinearInsertionRegularity background H UV) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (degree : ℕ)
    (free : ∀ Λ legs q, 0 < Λ → Λ < UV → legs.length ≤ 2 → background 0 Λ UV legs q = 0)
    (gradedF : ∀ loop Λ legs q (pi : Equiv.Perm (Fin legs.length)),
      F loop Λ UV (permutedLegs legs pi) (permutedMomenta legs pi q) =
        permutationSign legs pi * F loop Λ UV legs q)
    (gradedH : ∀ loop Λ legs q (pi : Equiv.Perm (Fin legs.length)),
      H loop Λ UV (permutedLegs legs pi) (permutedMomenta legs pi q) =
        permutationSign legs pi * H loop Λ UV legs q)
    (low : ∀ loop (m : LocalMonomial G), m.Admissible → m.dimension ≤ degree →
      extractCoefficient m (F loop μ UV) 0 = extractCoefficient m (H loop μ UV) 0)
    (high : ∀ loop (m : LocalMonomial G), m.Admissible → degree < m.dimension → ∀ p,
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
              simpa [momentumJet, iteratedFDeriv_zero_apply] using cf
            have ch' : ContinuousOn (fun s => H loop s UV ls p) (Set.Ioc 0 UV) := by
              simpa [momentumJet, iteratedFDeriv_zero_apply] using ch
            exact cf'.sub ch'
          · intro s hs hsUV
            have hd := (hF.flow loop s ls p hs hsUV).sub (hH.flow loop s ls p hs hsUV)
            simpa only [rhs ls hls s p hs hsUV, sub_self] using hd
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
            · have eq : A m.legs = fun p => F loop μ UV m.legs p - H loop μ UV m.legs p :=
                constant m.legs hlen μ hμ hUV
              unfold extractCoefficient
              rw [eq]
              change extractCoefficient m (fun ls p => F loop μ UV ls p - H loop μ UV ls p) 0 = 0
              rw [extractCoefficient_difference_smooth m _ _
                (fun ls => hF.smooth loop μ ls hμ hUV) (fun ls => hH.smooth loop μ ls hμ hUV),
                low loop m hm hd, sub_self]
            · rfl)
          (by
            intro m hm hd p
            rw [extractCoefficient_arityRestricted]
            split_ifs
            · change extractCoefficient m (fun ls p => F loop UV UV ls p - H loop UV UV ls p) p = 0
              rw [extractCoefficient_difference_smooth m _ _
                (fun ls => hF.smooth loop UV ls uvpos le_rfl)
                (fun ls => hH.smooth loop UV ls uvpos le_rfl), high loop m hm hd p, sub_self]
            · rfl)
        intro ls hls t ht htUV p
        have hz := zero ls p
        simp only [arityRestricted, if_pos hls, A] at hz
        have hv := congrFun (constant ls hls t ht htUV) p
        exact sub_eq_zero.mp (hv.symm.trans hz)
  exact main loop legs.length legs rfl Λ hp hle q

/-- Uniqueness of the actual single insertion, with its original canonical
boundary conditions and the SAME background. Translation transports the
origin result to the SAME insertion at every position. -/
theorem InsertionFlowConditions.single_unique_of_free
    {background : FlowFamily G} {L M : InsertedFlowFamily G}
    {F H : OversubtractedFamily G} {μ UV : ℝ}
    (hL : InsertionFlowConditions background L F μ)
    (hM : InsertionFlowConditions background M H μ) (hUV : μ ≤ UV)
    (free : ∀ Λ legs q, 0 < Λ → Λ < UV → legs.length ≤ 2 → background 0 Λ UV legs q = 0)
    (A : LocalMonomial G) (x : Spacetime) (loop : ℕ) (Λ : ℝ)
    (hp : 0 < Λ) (hle : Λ ≤ UV) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    L [⟨A,x⟩] loop Λ UV legs q = M [⟨A,x⟩] loop Λ UV legs q := by
  by_cases admissible : A.Admissible
  · have origin : ∀ loop Λ, 0 < Λ → Λ ≤ UV → ∀ legs q,
        L [⟨A,0⟩] loop Λ UV legs q = M [⟨A,0⟩] loop Λ UV legs q := by
      apply LinearInsertionRegularity.unique_of_canonical_projectors
        (hL.singleRegularity A 0 UV) (hM.singleRegularity A 0 UV)
        hL.single_boundary.scale_positive hUV A.dimension free
      · exact fun loop Λ legs q pi => hL.single_graded_symmetry A 0 loop Λ UV legs q pi
      · exact fun loop Λ legs q pi => hM.single_graded_symmetry A 0 loop Λ UV legs q pi
      · intro loop m hm hd
        rw [hL.single_boundary.normalized A m admissible hm hd loop UV hUV,
          hM.single_boundary.normalized A m admissible hm hd loop UV hUV]
      · intro loop m hm hd p
        rw [hL.single_boundary.irrelevant A m admissible hm hd loop UV hUV p,
          hM.single_boundary.irrelevant A m admissible hm hd loop UV hUV p]
    rw [hL.single_translation A x x loop Λ UV legs q,
      hM.single_translation A x x loop Λ UV legs q, sub_self,
      origin loop Λ hp hle legs q]
  · rw [hL.single_boundary.invalid A admissible x loop Λ UV legs q,
      hM.single_boundary.invalid A admissible x loop Λ UV legs q]

/-- For an actual fixed G/action background, the free-tree condition used
above is already a proved field of its fixed coefficient conditions. -/
theorem InsertionFlowConditions.single_unique
    {form : InvariantForm G} {e : ColorFrame form} {scheme : LocalMarginalData G}
    {background : ScaleCouplingFamily G} (hb : CoefficientFlowConditions e scheme background)
    {L M : InsertedFlowFamily G} {F H : OversubtractedFamily G} {μ g UV : ℝ}
    (hL : InsertionFlowConditions (background μ g) L F μ)
    (hM : InsertionFlowConditions (background μ g) M H μ) (hUV : μ ≤ UV)
    (A : LocalMonomial G) (x : Spacetime) (loop : ℕ) (Λ : ℝ)
    (hp : 0 < Λ) (hle : Λ ≤ UV) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    L [⟨A,x⟩] loop Λ UV legs q = M [⟨A,x⟩] loop Λ UV legs q :=
  hL.single_unique_of_free hM hUV
    (fun Λ legs q _ _ hlen => hb.no_free_interaction μ g Λ UV legs q hlen)
    A x loop Λ hp hle legs q

end YangMills.PerturbativeFlow
