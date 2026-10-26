import YangMills.CanonicalProjectorCovariance

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

lemma orderedAmplitude_component_congr (A : OrderedAmplitude G)
    {legs other : List (ExternalLeg G)} (equal : legs = other)
    (q : Fin legs.length → Spacetime) (p : Fin other.length → Spacetime)
    (momenta : ∀ i, q i = p (Fin.cast (congrArg List.length equal) i)) :
    A legs q = A other p := by
  subst other
  congr 1
  funext i
  exact momenta i

/-- Canonical component covariance is derived from the SAME amplitude's
actual graded external permutation law. No independent derivative law enters. -/
theorem canonicalProjector_transport (A : OrderedAmplitude G)
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4)) :
    A (directionMonomial legs directions).legs ∘
      momentumCoordinateRelabel (canonicalProjectorSlotEquiv legs directions) =
      fun q => permutationSign legs (canonicalExternalPermutation legs directions) * A legs q := by
  funext q
  have actual := graded legs q (canonicalExternalPermutation legs directions)
  have components := orderedAmplitude_component_congr A
    (canonicalExternalPermutation_fields legs directions)
    (permutedMomenta legs (canonicalExternalPermutation legs directions) q)
    (momentumCoordinateRelabel (canonicalProjectorSlotEquiv legs directions) q)
    (by intro i; rfl)
  exact components.symm.trans actual

/-- The original momentum jet is exactly the canonical normalized
monomial's jet, up to its fixed nonzero graded permutation sign. -/
theorem canonicalJetExtraction (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (q : Fin legs.length → Spacetime) :
    momentumJet (directionMonomial legs directions).momentumDirections (A (directionMonomial legs directions).legs)
      (momentumCoordinateRelabel (canonicalProjectorSlotEquiv legs directions) q) =
      permutationSign legs (canonicalExternalPermutation legs directions) * momentumJet directions (A legs) q := by
  exact canonicalProjector_momentumJet legs directions _ (smooth legs) (smooth _)
    (canonicalProjector_transport A graded legs directions) q

lemma LocalMonomial.momentumFactorial_pos (m : LocalMonomial G) : 0 < m.momentumFactorial := by
  have positive (items : List (JetVariable G)) :
      0 < (items.map (fun v => ∏ mu : Fin 4, Nat.factorial (v.2 mu))).prod := by
    induction items with
    | nil => simp
    | cons v rest ih =>
      simp only [List.map_cons,List.prod_cons]
      exact mul_pos (Finset.prod_pos (fun mu _ => Nat.factorial_pos _)) ih
  exact positive m.orderedJets

lemma extractCoefficient_zero_iff (m : LocalMonomial G) (A : OrderedAmplitude G)
    (q : Fin m.legs.length → Spacetime) :
    extractCoefficient m A q = 0 ↔ momentumJet m.momentumDirections (A m.legs) q = 0 := by
  have denominator : (m.momentumFactorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt m.momentumFactorial_pos)
  have scalar : Complex.I ^ m.momentumDirections.length / (m.momentumFactorial : ℂ) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ Complex.I_ne_zero) denominator
  change (_ * momentumJet m.momentumDirections (A m.legs) q = 0) ↔ _
  simp only [mul_eq_zero,scalar,false_or]

/-- Exact projector adequacy for an arbitrary direction list: the canonical
projector vanishes iff that actual coordinate jet vanishes. Its monomial
admissibility is deliberately NOT inferred; the graded UV PDE issue is separate. -/
theorem canonicalJetExtraction_zero_iff (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (q : Fin legs.length → Spacetime) :
    extractCoefficient (directionMonomial legs directions) A
      (momentumCoordinateRelabel (canonicalProjectorSlotEquiv legs directions) q) = 0 ↔
      momentumJet directions (A legs) q = 0 := by
  rw [extractCoefficient_zero_iff,canonicalJetExtraction A smooth graded]
  have sign : permutationSign legs (canonicalExternalPermutation legs directions) ≠ 0 := by
    unfold permutationSign
    exact pow_ne_zero _ (by norm_num)
  simp only [mul_eq_zero,sign,false_or]

end YangMills.PerturbativeFlow
