import YangMills.LegendreCompositionGraded
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

theorem gammaCoeff_recurrence (F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    gammaCoeff F s order loop legs q = legendreTarget F s order loop legs q -
      lowerComposition (gammaCoeff F s) F s order loop legs q := by
  conv_lhs => rw [gammaCoeff]
  apply congrArg (fun z : ℂ => legendreTarget F s order loop legs q - z)
  unfold lowerComposition
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro go _
  apply Finset.sum_congr rfl
  intro ho _
  split_ifs with h
  · apply substitutionSummand_congr_outer
    simp only [h, dite_true]
  · rfl


/-- The background recursion is exactly the same deterministic insertion
recursion applied to its fixed quadratic-subtracted target. This identity
is algebraic and does not strengthen balanced background symmetry. -/
theorem gammaCoeff_eq_insertion (F : FormalAmplitude G) (s : CutoffScales) :
    gammaCoeff F s = insertionGammaCoeff F (legendreTarget F s) s := by
  have all : ∀ order loop legs q, gammaCoeff F s order loop legs q =
      insertionGammaCoeff F (legendreTarget F s) s order loop legs q := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro loop legs q
      rw [gammaCoeff_recurrence, insertionGammaCoeff_recurrence]
      apply congrArg (fun z : ℂ => legendreTarget F s order loop legs q - z)
      exact lowerComposition_congr_prefix (gammaCoeff F s)
        (insertionGammaCoeff F (legendreTarget F s) s) F s order loop legs q ih
  funext order loop legs q
  exact all order loop legs q


theorem gammaCoeff_graded_balanced (F : FormalAmplitude G) (s : CutoffScales)
    (backgroundGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (targetGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      legendreTarget F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * legendreTarget F s order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (balanced : BalancedMomenta legs q) :
    gammaCoeff F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * gammaCoeff F s order loop legs q := by
  rw [gammaCoeff_recurrence, gammaCoeff_recurrence, targetGraded _ _ _ _ e balanced,
    lowerComposition_graded (gammaCoeff F s) F s backgroundGraded]
  ring

/-- Pointwise free normalization needs the background graded identity
only on the balanced momentum tuple being evaluated. -/
theorem meanFieldCompose_identity_balanced (A : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      A order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * A order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (balanced : BalancedMomenta legs q) :
    meanFieldCompose A 0 s order loop legs q = A order loop legs q := by
  rw [meanFieldCompose_free_permutations]
  simp_rw [root_sum_permutation, partitionSign_perm]
  have term : ∀ e : Equiv.Perm (Fin legs.length),
      (Nat.factorial legs.length : ℂ)⁻¹ * permutationSign legs e.symm *
        A order loop (permutedLegs legs e.symm) (permutedMomenta legs e.symm q) =
      (Nat.factorial legs.length : ℂ)⁻¹ * A order loop legs q := by
    intro e
    rw [graded order loop legs q e.symm balanced]
    rw [mul_assoc, ← mul_assoc (permutationSign legs e.symm), permutationSign_square, one_mul]
  simp_rw [term]
  have hn : (Nat.factorial legs.length : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero legs.length
  simp [Fintype.card_perm, nsmul_eq_mul, hn]

/-- Actual background composition is recovered on momentum-conserving
coefficients. The remaining source combinatorics is explicitly the graded
law of the fixed quadratic target, rather than an assumed computed inverse. -/
theorem gammaCoeff_inverse_balanced (F : FormalAmplitude G) (s : CutoffScales)
    (free : ∀ loop legs q, F 0 loop legs q = 0)
    (backgroundGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (targetGraded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      legendreTarget F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * legendreTarget F s order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (balanced : BalancedMomenta legs q) :
    meanFieldCompose (gammaCoeff F s) F s order loop legs q = legendreTarget F s order loop legs q := by
  rw [meanFieldCompose_split, diagonalComposition_free _ F s free,
    diagonalComposition_eq_free_compose,
    meanFieldCompose_identity_balanced (gammaCoeff F s) s
      (gammaCoeff_graded_balanced F s backgroundGraded targetGraded) order loop legs q balanced,
    gammaCoeff_recurrence]
  ring

end YangMills.LegendreInsertionBridge
