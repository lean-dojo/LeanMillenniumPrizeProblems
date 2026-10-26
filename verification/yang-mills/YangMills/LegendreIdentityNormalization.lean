import YangMills.LegendreIdentityCoefficients
/-!
# Arbitrary-arity identity-root normalization

Every nonzero term of the actual finite graded partition sum has singleton
blocks and a bijective assignment. The roots are uniquely determined; the
partition sign equals the inverse permutation sign. The outer graded law
then cancels that sign, and n! permutations cancel the actual denominator.
No external arity cutoff or ghost-to-commuting-variable replacement is used.
-/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
open YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

def canonicalRoots (legs : List (ExternalLeg G)) (e : Equiv.Perm (Fin legs.length)) :
    Fin legs.length → ExternalLeg G := fun b => legs.get (e.symm b)

theorem rootMomenta_permutation (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) (q : Fin legs.length → Spacetime) :
    rootMomenta legs q e (canonicalRoots legs e) = permutedMomenta legs e.symm q := by
  funext i
  simp [rootMomenta, partitionBlock_perm, selectedMomentum, permutedMomenta]

theorem root_sum_permutation (A : FormalAmplitude G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    (∑ roots : Fin legs.length → ExternalLeg G,
      identityPartitionSummand A order loop legs q legs.length e roots) =
      (Nat.factorial legs.length : ℂ)⁻¹ * partitionSign legs e *
        A order loop (permutedLegs legs e.symm) (permutedMomenta legs e.symm q) := by
  rw [Finset.sum_eq_single (canonicalRoots legs e)]
  · have hNE : ∀ b, (partitionBlock e b).Nonempty := by
      intro b
      rw [partitionBlock_perm]
      exact Finset.singleton_nonempty _
    rw [identityPartitionSummand, if_pos hNE]
    simp only [partitionBlock_perm, selectedLegs_singleton]
    have hprod : (∏ b : Fin legs.length,
        identityRoot (canonicalRoots legs e b) [legs.get (e.symm b)]) = 1 := by
      simp [canonicalRoots, identityRoot]
    rw [hprod, mul_one, rootMomenta_permutation]
    rfl
  · intro roots _ hne
    have hex : ∃ b, roots b ≠ canonicalRoots legs e b := by
      by_contra hn
      push_neg at hn
      exact hne (funext hn)
    obtain ⟨b, hb⟩ := hex
    have hf : identityRoot (roots b) (selectedLegs legs (partitionBlock e b)) = 0 := by
      simp [partitionBlock_perm, selectedLegs_singleton, identityRoot, canonicalRoots] at hb ⊢
      exact Ne.symm hb
    have hp : (∏ b : Fin legs.length,
        identityRoot (roots b) (selectedLegs legs (partitionBlock e b))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) hf
    simp [identityPartitionSummand, hp]
  · simp

theorem permutationSign_square (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) :
    permutationSign legs e * permutationSign legs e = 1 := by
  unfold permutationSign
  rw [← mul_pow]
  norm_num

/-- Arbitrary-arity identity-root normalization for actual graded tensors.
The n! labelled singleton assignments cancel the explicit factorial. -/
theorem meanFieldCompose_identity_of_graded (A : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      A order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * A order loop legs q) :
    meanFieldCompose A 0 s = A := by
  funext order loop legs q
  rw [meanFieldCompose_free_permutations]
  simp_rw [root_sum_permutation, partitionSign_perm, graded]
  have term : ∀ e : Equiv.Perm (Fin legs.length),
      (Nat.factorial legs.length : ℂ)⁻¹ * permutationSign legs e.symm *
        (permutationSign legs e.symm * A order loop legs q) =
      (Nat.factorial legs.length : ℂ)⁻¹ * A order loop legs q := by
    intro e
    rw [mul_assoc, ← mul_assoc (permutationSign legs e.symm), permutationSign_square, one_mul]
  simp_rw [term]
  have hn : (Nat.factorial legs.length : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero legs.length
  simp [Fintype.card_perm, nsmul_eq_mul, hn]

/-- All-order computed insertion inversion under explicit algebraic
admissibility of its coefficients. Free identity normalization is a proved
lemma here, not an extra equation on the candidate inverse. -/
theorem insertion_inverse_of_graded (F I : FormalAmplitude G) (s : CutoffScales)
    (free : ∀ loop legs q, F 0 loop legs q = 0)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      insertionGammaCoeff F I s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * insertionGammaCoeff F I s order loop legs q) :
    meanFieldCompose (insertionGammaCoeff F I s) F s = I := by
  apply insertion_inverse_of_free_identity F I s free
  exact meanFieldCompose_identity_of_graded _ s graded

/-- The actual CS directional Legendre fidelity follows from g=0
vanishing and the explicit graded law of the computed recursion. Deriving
this law from source background/insertion gradedness remains supporting work. -/
theorem directionalLegendreCompatible_of_graded (A I : ℝ → FlowFamily G) (s : CutoffScales)
    (free : ∀ loop legs q, A 0 loop s.infrared s.ultraviolet legs q = 0)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      directionalGamma A I s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * directionalGamma A I s order loop legs q) :
    DirectionalLegendreCompatible A I s := by
  apply directionalLegendre_of_free_identity A I s free
  exact meanFieldCompose_identity_of_graded _ s graded

/-- Any graded inverse of this actual source map equals its deterministic
coupling recursion. No other inverse coefficient family may be selected. -/
theorem insertion_inverse_unique_of_graded (F I H : FormalAmplitude G) (s : CutoffScales)
    (free : ∀ loop legs q, F 0 loop legs q = 0)
    (solution : meanFieldCompose H F s = I)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      H order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * H order loop legs q) :
    H = insertionGammaCoeff F I s := by
  apply insertion_inverse_unique F I H s solution
  intro order loop legs q
  rw [diagonalComposition_free _ F s free, diagonalComposition_eq_free_compose,
    meanFieldCompose_identity_of_graded H s graded]

end YangMills.LegendreInsertionBridge
