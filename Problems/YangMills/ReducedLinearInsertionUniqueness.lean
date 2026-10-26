import Problems.YangMills.LinearInsertionUniqueness
import Problems.YangMills.FlowBoundaryUniqueness

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative Filter
open scoped ContDiff
variable {G : CompactSimpleGaugeGroup}

/-- Analytic ingredients of the actual homogeneous equation, separated from
its normalization data. This is a supporting theorem interface; it is not a
replacement for the fixed supermonomial insertion boundary conditions. -/
structure ReducedLinearInsertionRegularity (background F : FlowFamily G) (UV : ℝ) : Prop where
  smooth : ∀ loop Λ legs, 0 < Λ → Λ ≤ UV → ContDiff ℝ ∞ (F loop Λ UV legs)
  continuous : ∀ loop legs directions q,
    ContinuousOn (fun Λ => momentumJet directions (F loop Λ UV legs) q) (Set.Ioc 0 UV)
  extension : ∀ loop Λ legs q, F loop Λ UV legs q = F loop Λ UV legs (conservingMomenta legs q)
  vacuum : ∀ loop Λ q, F loop Λ UV [] q = 0
  flow : ∀ loop Λ legs q, 0 < Λ → Λ < UV → legs ≠ [] → BalancedMomenta legs q →
    HasDerivAt (fun scale => F loop scale UV legs q)
      (insertionHomogeneousRHS background F loop Λ UV legs q) Λ

/-- Actual balanced flow derivatives imply scale constancy on the entire
conserving extension, before any momentum derivative is taken. -/
theorem ReducedLinearInsertionRegularity.scaleConstant_all {background F H : FlowFamily G}
    {UV : ℝ} (hF : ReducedLinearInsertionRegularity background F UV)
    (hH : ReducedLinearInsertionRegularity background H UV)
    (loop : ℕ) (legs : List (ExternalLeg G)) (nonempty : legs ≠ [])
    (rhs : ∀ Λ q, 0 < Λ → Λ < UV → BalancedMomenta legs q →
      insertionHomogeneousRHS background F loop Λ UV legs q =
        insertionHomogeneousRHS background H loop Λ UV legs q)
    {x y : ℝ} (hx : 0 < x) (hxUV : x ≤ UV) (hy : 0 < y) (hyUV : y ≤ UV) :
    (fun q => F loop x UV legs q - H loop x UV legs q) =
      (fun q => F loop y UV legs q - H loop y UV legs q) := by
  funext q
  rw [hF.extension loop x legs q, hH.extension loop x legs q,
    hF.extension loop y legs q, hH.extension loop y legs q]
  let p := conservingMomenta legs q
  apply positiveScale_constancy (UV := UV) (f := fun Λ => F loop Λ UV legs p - H loop Λ UV legs p)
  · have cf := hF.continuous loop legs [] p
    have ch := hH.continuous loop legs [] p
    have cf' : ContinuousOn (fun Λ => F loop Λ UV legs p) (Set.Ioc 0 UV) := by
      simpa [momentumJet, iteratedFDeriv_zero_apply] using! cf
    have ch' : ContinuousOn (fun Λ => H loop Λ UV legs p) (Set.Ioc 0 UV) := by
      simpa [momentumJet, iteratedFDeriv_zero_apply] using! ch
    exact cf'.sub ch'
  · intro Λ hp hl
    have hd := (hF.flow loop Λ legs p hp hl nonempty (conservingMomenta_balanced G legs q)).sub
      (hH.flow loop Λ legs p hp hl nonempty (conservingMomenta_balanced G legs q))
    simpa only [rhs Λ p hp hl (conservingMomenta_balanced G legs q), sub_self] using! hd
  all_goals assumption

/-- Equality of the actual reduced coordinate normalization jets at mu and of all
irrelevant UV jets determines a cutoff-constant linear response. -/
theorem reducedLinearDifference_zero_of_normalization {background F H : FlowFamily G}
    {UV μ : ℝ} (hF : ReducedLinearInsertionRegularity background F UV)
    (hH : ReducedLinearInsertionRegularity background H UV) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (degree loop : ℕ) (legs : List (ExternalLeg G))
    (constant : ∀ Λ, 0 < Λ → Λ ≤ UV →
      (fun q => F loop UV UV legs q - H loop UV UV legs q) =
        (fun q => F loop Λ UV legs q - H loop Λ UV legs q))
    (low : ∀ directions : List (Fin legs.length × Fin 4), ReducedDirections legs directions →
      totalDimension legs + directions.length ≤ degree →
      momentumJet directions (F loop μ UV legs) 0 = momentumJet directions (H loop μ UV legs) 0)
    (high : ∀ directions : List (Fin legs.length × Fin 4), ReducedDirections legs directions →
      degree < totalDimension legs + directions.length → ∀ q,
      momentumJet directions (F loop UV UV legs) q = momentumJet directions (H loop UV UV legs) q) :
    (fun q => F loop UV UV legs q - H loop UV UV legs q) = 0 := by
  have uvpos := hμ.trans_le hUV
  let f := fun q => F loop UV UV legs q - H loop UV UV legs q
  have smooth : ContDiff ℝ ∞ f := (hF.smooth loop UV legs uvpos le_rfl).sub
    (hH.smooth loop UV legs uvpos le_rfl)
  have extension : ∀ q, f q = f (conservingMomenta legs q) := by
    intro q
    exact congrArg₂ (· - ·) (hF.extension loop UV legs q) (hH.extension loop UV legs q)
  have jet_at (d : List (Fin legs.length × Fin 4)) (q : Fin legs.length → Spacetime)
      (Λ : ℝ) (hp : 0 < Λ) (hle : Λ ≤ UV) :
      momentumJet d f q = momentumJet d (F loop Λ UV legs) q - momentumJet d (H loop Λ UV legs) q := by
    change momentumJet d (fun q => F loop UV UV legs q - H loop UV UV legs q) q = _
    rw [constant Λ hp hle]
    exact momentumJet_difference_smooth d (hF.smooth loop Λ legs hp hle)
      (hH.smooth loop Λ legs hp hle) q
  have irrelevant (d : List (Fin legs.length × Fin 4)) (reduced : ReducedDirections legs d)
      (hd : degree < totalDimension legs + d.length) (q : Fin legs.length → Spacetime) :
      momentumJet d f q = 0 := by
    rw [jet_at d q UV uvpos le_rfl, high d reduced hd q, sub_self]
  by_cases highDim : degree < totalDimension legs
  · funext q
    simpa only [momentumJet, List.length_nil, iteratedFDeriv_zero_apply, Pi.zero_apply]
      using! irrelevant [] (by intro d hd; simp at hd) (by simpa using! highDim) q
  · apply reducedJet_determinacy smooth extension (degree-totalDimension legs)
    · intro d reduced hd q
      exact irrelevant d reduced (by omega) q
    · intro d reduced hd
      rw [jet_at d 0 μ hμ hUV, low d reduced (by omega), sub_self]

/-- Uniqueness for the actual linear response once its independent momentum
jets have been fixed. Canonical supermonomial projector adequacy is a
separate algebraic theorem, not an extra candidate boundary assumption. -/
theorem ReducedLinearInsertionRegularity.unique_of_reduced_jets {background F H : FlowFamily G}
    {UV μ : ℝ} (hF : ReducedLinearInsertionRegularity background F UV)
    (hH : ReducedLinearInsertionRegularity background H UV) (hμ : 0 < μ) (hUV : μ ≤ UV)
    (degree : ℕ)
    (free : ∀ Λ legs q, 0 < Λ → Λ < UV → legs.length ≤ 2 → background 0 Λ UV legs q = 0)
    (low : ∀ loop legs (d : List (Fin legs.length × Fin 4)), ReducedDirections legs d →
      totalDimension legs + d.length ≤ degree →
      momentumJet d (F loop μ UV legs) 0 = momentumJet d (H loop μ UV legs) 0)
    (high : ∀ loop legs (d : List (Fin legs.length × Fin 4)), ReducedDirections legs d →
      degree < totalDimension legs + d.length → ∀ q,
      momentumJet d (F loop UV UV legs) q = momentumJet d (H loop UV UV legs) q)
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
        intro legs hlen Λ hp hle q
        by_cases empty : legs = []
        · subst legs
          rw [hF.vacuum, hH.vacuum]
        · have rhs : ∀ t p, 0 < t → t < UV →
              insertionHomogeneousRHS background F loop t UV legs p =
                insertionHomogeneousRHS background H loop t UV legs p := by
            intro t p ht htUV
            apply insertionHomogeneousRHS_congr_lower
            · intro l ls p' hl
              rcases hl with hl | ⟨hl, hls⟩
              · exact ihloop l hl ls.length ls rfl t ht htUV.le p'
              · subst l
                exact iharity ls.length (by omega) ls rfl t ht htUV.le p'
            · exact fun ls p' hls => free t ls p' ht htUV hls
          have constant : ∀ t, 0 < t → t ≤ UV →
              (fun p => F loop UV UV legs p - H loop UV UV legs p) =
                (fun p => F loop t UV legs p - H loop t UV legs p) := by
            intro t ht htUV
            funext q'
            rw [hF.extension loop UV legs q', hH.extension loop UV legs q',
              hF.extension loop t legs q', hH.extension loop t legs q']
            let p := conservingMomenta legs q'
            apply positiveScale_constancy (UV := UV)
              (f := fun s => F loop s UV legs p - H loop s UV legs p)
            · have cf := hF.continuous loop legs [] p
              have ch := hH.continuous loop legs [] p
              have cf' : ContinuousOn (fun s => F loop s UV legs p) (Set.Ioc 0 UV) := by
                simpa [momentumJet, iteratedFDeriv_zero_apply] using! cf
              have ch' : ContinuousOn (fun s => H loop s UV legs p) (Set.Ioc 0 UV) := by
                simpa [momentumJet, iteratedFDeriv_zero_apply] using! ch
              exact cf'.sub ch'
            · intro s hs hsUV
              have hd := (hF.flow loop s legs p hs hsUV empty (conservingMomenta_balanced G legs q')).sub
                (hH.flow loop s legs p hs hsUV empty (conservingMomenta_balanced G legs q'))
              simpa only [rhs s p hs hsUV, sub_self] using! hd
            all_goals first | assumption | exact le_rfl
          have hz := reducedLinearDifference_zero_of_normalization hF hH hμ hUV degree loop legs
            constant (low loop legs) (high loop legs)
          have hv := congrFun ((constant Λ hp hle).symm.trans hz) q
          exact sub_eq_zero.mp hv
  exact main loop legs.length legs rfl Λ hp hle q

end YangMills.PerturbativeFlow
