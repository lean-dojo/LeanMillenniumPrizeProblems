import Problems.YangMills.CanonicalCornerApplication
import Problems.YangMills.FlatMomentumCoordinates
import Problems.YangMills.AnchoredCoordinateDeterminacy

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 3200000
open scoped ContDiff BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative YangMills.CanonicalUV
variable {G : CompactSimpleGaugeGroup}
local instance determinacyDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

/-- Every origin jet is fixed by the source's low origin rows and high
ultraviolet rows. Nonadmissible rows vanish by actual odd graded symmetry. -/
theorem canonicalOriginJet_zero (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (low : ∀ m : LocalMonomial G, m.Admissible → m.dimension ≤ D → extractCoefficient m A 0 = 0)
    (high : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4)) :
    momentumJet directions (A legs) 0 = 0 := by
  apply (canonicalJetExtraction_zero_iff A smooth graded legs directions 0).mp
  rw [map_zero]
  by_cases admissible : (directionMonomial legs directions).Admissible
  · by_cases small : (directionMonomial legs directions).dimension ≤ D
    · exact low _ admissible small
    · exact high _ admissible (by omega) _
  · exact extractCoefficient_nonadmissible_zero A smooth graded _ admissible

/-- Genuine smooth determinacy from precisely the admissible canonical
normalization rows: low rows at zero, high rows at all independent momenta.
No analyticity or additional all-coordinate ultraviolet clauses are assumed. -/
theorem canonicalProjectorDeterminacy (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (low : ∀ m : LocalMonomial G, m.Admissible → m.dimension ≤ D → extractCoefficient m A 0 = 0)
    (high : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0) :
    ∀ legs q, A legs q = 0 := by
  classical
  intro legs q
  let f : ((Fin legs.length × Fin 4) → ℝ) → ℂ :=
    A legs ∘ (flattenMomentumCoordinates legs.length).symm
  have fsmooth : ContDiff ℝ ∞ f := (smooth legs).comp (flattenMomentumCoordinates legs.length).symm.contDiff
  have zero : f = 0 := anchored_coordinate_determinacy (L := D+legs.length+1) fsmooth (by
    intro directions bounded p anchored
    change directionalWord _ f p = 0
    rw [flattenedDirectionalWord_eq_momentumJet legs directions (smooth legs)]
    let a : Fin legs.length → Fin 4 → ℕ := fun i mu => directions.count (i,mu)
    let S : Finset (Fin legs.length × Fin 4) := Finset.univ.filter (fun z => directions.count z = D+legs.length+1)
    have permutation : (coordinateDirections a).Perm directions := by
      apply List.perm_iff_count.mpr
      rintro ⟨i,mu⟩
      exact coordinateDirections_count a i mu
    have corner_eq : corner S (D+legs.length+1) a = a := by
      funext i mu
      unfold corner
      split_ifs with h
      · exact (Finset.mem_filter.mp h).2.symm
      · rfl
    by_cases nonempty : S.Nonempty
    · rw [← momentumJet_perm legs permutation (smooth legs),← corner_eq]
      apply canonicalCorner_zero A smooth graded D high legs S nonempty a
      intro i mu inactive
      apply anchored (i,mu) (by simp)
      have not_equal : directions.count (i,mu) ≠ D+legs.length+1 := by
        intro equal
        exact inactive (Finset.mem_filter.mpr ⟨Finset.mem_univ _,equal⟩)
      exact lt_of_le_of_ne (bounded (i,mu)) not_equal
    · have origin : (flattenMomentumCoordinates legs.length).symm p = 0 := by
        funext i mu
        apply anchored (i,mu) (by simp)
        have not_equal : directions.count (i,mu) ≠ D+legs.length+1 := by
          intro equal
          exact nonempty ⟨(i,mu),Finset.mem_filter.mpr ⟨Finset.mem_univ _,equal⟩⟩
        exact lt_of_le_of_ne (bounded (i,mu)) not_equal
      rw [origin]
      exact canonicalOriginJet_zero A smooth graded D low high legs directions)
  have value := congrFun zero ((flattenMomentumCoordinates legs.length) q)
  simpa only [f,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply,Pi.zero_apply] using value

end YangMills.PerturbativeFlow
