import YangMills.RepeatedOddProjector

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- All actual coordinate Taylor jets through the engineering cutoff are
fixed by the admissible canonical monomial projectors at zero. Odd-square
nilpotence is proved from graded symmetry, not added as a boundary clause. -/
theorem lowProjectorAdequacy (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (normalized : ∀ m : LocalMonomial G, m.Admissible → m.dimension ≤ D → extractCoefficient m A 0 = 0)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (degree : totalDimension legs + directions.length ≤ D) : momentumJet directions (A legs) 0 = 0 := by
  apply (canonicalJetExtraction_zero_iff A smooth graded legs directions 0).mp
  rw [map_zero]
  by_cases admissible : (directionMonomial legs directions).Admissible
  · exact normalized _ admissible (by rw [directionMonomial_dimension]; exact degree)
  · exact extractCoefficient_nonadmissible_zero A smooth graded _ admissible

end YangMills.PerturbativeFlow
