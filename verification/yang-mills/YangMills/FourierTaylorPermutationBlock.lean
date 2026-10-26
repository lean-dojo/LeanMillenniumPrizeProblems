import YangMills.FourierTaylorAssignedPhase
import YangMills.FourierTaylorReducedCoordinates
import YangMills.FourierTaylorSigns

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- A whole reduced-direction sum in one actual source/external bijection
is its diagonal Taylor tensor at the inverse-permuted momenta. This computes
the amplitude's Fourier/Taylor contribution, without assuming it as a guard. -/
theorem actual_permutation_Taylor_block (legs : List (ExternalLeg G))
    (f : (Fin legs.length → Spacetime) → ℂ) (smooth : ContDiff ℝ ∞ f)
    (extension : ∀ q, f q = f (conservingMomenta legs q))
    (q : Fin legs.length → Spacetime) (π : Equiv.Perm (Fin legs.length)) (k : ℕ) :
    (∑ p : Fin k → Fin legs.length × Fin 4,
      if ReducedDirections legs (List.ofFn p) then
        momentumJet (List.ofFn p) f 0 *
          (Complex.I^k * assignedVertexTerm
            (fun j => ⟨legs.get (π.symm j), directionBucket (List.ofFn p) j⟩)
            (fun i => (legs.get i, q i)) π)
      else 0) =
      YangMills.LegendreInsertionBridge.parityExternalSign
          (fun j => (legs.get (π.symm j)).parity) π *
        iteratedFDeriv ℝ k f 0 (fun _ => fun j => q (π.symm j)) := by
  classical
  rw [diagonalTaylor_reduced_expansion f smooth extension k]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with h
  · have hc := assignedTaylorPhase legs (List.ofFn p) q π
    simp only [List.length_ofFn] at hc
    rw [hc]
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
    rw [Complex.real_smul, Complex.ofReal_prod]
    ring
  · simp only [mul_zero]

/-- Balanced gradedness cancels the second actual Koszul factor, after the
whole reduced-direction sum has been evaluated. Off-balanced gradedness is
not assumed. -/
theorem actual_permutation_Taylor_block_graded (legs : List (ExternalLeg G))
    (f h : (Fin legs.length → Spacetime) → ℂ)
    (smooth : ContDiff ℝ ∞ f) (smoothH : ContDiff ℝ ∞ h)
    (extension : ∀ p, f p = f (conservingMomenta legs p))
    (q : Fin legs.length → Spacetime) (hq : BalancedMomenta legs q)
    (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (graded : ∀ p, BalancedMomenta legs p →
      f (fun j => p (π.symm j)) =
        YangMills.LegendreInsertionBridge.parityExternalSign
          (fun j => (legs.get j).parity) π.symm * h p) :
    (∑ p : Fin k → Fin legs.length × Fin 4,
      if ReducedDirections legs (List.ofFn p) then
        momentumJet (List.ofFn p) f 0 *
          (Complex.I^k * assignedVertexTerm
            (fun j => ⟨legs.get (π.symm j), directionBucket (List.ofFn p) j⟩)
            (fun i => (legs.get i, q i)) π)
      else 0) = iteratedFDeriv ℝ k h 0 (fun _ => q) := by
  rw [actual_permutation_Taylor_block legs f smooth extension q π k]
  have hd := diagonalTaylor_of_radial f h smooth smoothH
    (fun j => q (π.symm j)) q
    (YangMills.LegendreInsertionBridge.parityExternalSign
      (fun j => (legs.get j).parity) π.symm) k
    (fun t => graded (fun j => t • q j) (BalancedMomenta_smul legs q hq t))
  rw [hd, ← mul_assoc,
    parityExternalSign_inverse_cancel legs.length (fun j => (legs.get j).parity) π, one_mul]

/-- The source word's amplitude, with its Fin index transported back to the
same external index type. This is literally the given OrderedAmplitude. -/
def indexedPermutedAmplitude (F : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (π : Equiv.Perm (Fin legs.length)) : (Fin legs.length → Spacetime) → ℂ :=
  fun q => F (permutedLegs legs π)
    (fun i => q (Fin.cast (by simp only [permutedLegs, List.length_ofFn]) i))

/-- Actual balanced external covariance gives exactly the indexed law used
in the computed Taylor block; no second amplitude family is introduced. -/
theorem indexedPermutedAmplitude_graded (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length))
    (graded : ∀ p, BalancedMomenta legs p →
      F (permutedLegs legs π.symm) (permutedMomenta legs π.symm p) =
        permutationSign legs π.symm * F legs p)
    (p : Fin legs.length → Spacetime) (hp : BalancedMomenta legs p) :
    indexedPermutedAmplitude F legs π.symm (fun j => p (π.symm j)) =
      YangMills.LegendreInsertionBridge.parityExternalSign
        (fun j => (legs.get j).parity) π.symm * F legs p := by
  have he : (fun i : Fin (permutedLegs legs π.symm).length =>
      p (π.symm (Fin.cast (by simp only [permutedLegs, List.length_ofFn]) i))) =
      permutedMomenta legs π.symm p := by
    rfl
  unfold indexedPermutedAmplitude
  rw [he]
  exact graded p hp

/-- Transport of the actual conserving extension under a pure arity cast. -/
theorem conservingMomenta_cast (legs other : List (ExternalLeg G))
    (h : other.length = legs.length) (q : Fin legs.length → Spacetime) :
    (fun i : Fin other.length => conservingMomenta legs q (Fin.cast h i)) =
      conservingMomenta other (fun i => q (Fin.cast h i)) := by
  classical
  funext i
  simp only [conservingMomenta, Fin.coe_cast]
  by_cases hi : i.val + 1 = legs.length
  · rw [if_pos hi, if_pos (show i.val + 1 = other.length by omega)]
    congr 1
    simp only [Finset.sum_filter]
    calc
      (∑ j : Fin legs.length, if j.val + 1 < legs.length then q j else 0) =
          ∑ j : Fin other.length,
            if j.val + 1 < legs.length then q (Fin.cast h j) else 0 := by
        simpa only [finCongr_apply, Fin.coe_cast] using
          (Equiv.sum_comp (finCongr h) (fun j =>
            if j.val + 1 < legs.length then q j else 0)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj' : j.val + 1 < legs.length
        · rw [if_pos hj', if_pos (by omega)]
        · rw [if_neg hj', if_neg (by omega)]
  · rw [if_neg hi, if_neg (show ¬ i.val + 1 = other.length by omega)]

theorem indexedPermutedAmplitude_smooth (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length))
    (smooth : ContDiff ℝ ∞ (F (permutedLegs legs π))) :
    ContDiff ℝ ∞ (indexedPermutedAmplitude F legs π) := by
  let C : (Fin legs.length → Spacetime) →L[ℝ]
      (Fin (permutedLegs legs π).length → Spacetime) :=
    ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (Fin.cast (by simp only [permutedLegs, List.length_ofFn]) i)
  exact smooth.comp C.contDiff

theorem indexedPermutedAmplitude_extension (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length))
    (extension : ∀ q, F (permutedLegs legs π) q =
      F (permutedLegs legs π) (conservingMomenta (permutedLegs legs π) q))
    (q : Fin legs.length → Spacetime) :
    indexedPermutedAmplitude F legs π q =
      indexedPermutedAmplitude F legs π (conservingMomenta legs q) := by
  unfold indexedPermutedAmplitude
  rw [extension]
  congr 1
  exact (conservingMomenta_cast legs (permutedLegs legs π)
    (by simp only [permutedLegs, List.length_ofFn]) q).symm

/-- The complete reduced-direction block uses the SAME actual amplitude
family on its permuted source word. Its hypotheses are just smoothness,
conserving extension and balanced graded external covariance. -/
theorem sameAmplitude_permutation_Taylor_block (F : OrderedAmplitude G)
    (smooth : ∀ labels, ContDiff ℝ ∞ (F labels))
    (extension : ∀ labels p, F labels p = F labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hq : BalancedMomenta legs q) (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (graded : ∀ p, BalancedMomenta legs p →
      F (permutedLegs legs π.symm) (permutedMomenta legs π.symm p) =
        permutationSign legs π.symm * F legs p) :
    (∑ p : Fin k → Fin legs.length × Fin 4,
      if ReducedDirections legs (List.ofFn p) then
        momentumJet (List.ofFn p) (indexedPermutedAmplitude F legs π.symm) 0 *
          (Complex.I^k * assignedVertexTerm
            (fun j => ⟨legs.get (π.symm j), directionBucket (List.ofFn p) j⟩)
            (fun i => (legs.get i, q i)) π)
      else 0) = iteratedFDeriv ℝ k (F legs) 0 (fun _ => q) := by
  apply actual_permutation_Taylor_block_graded legs
    (indexedPermutedAmplitude F legs π.symm) (F legs)
    (indexedPermutedAmplitude_smooth F legs π.symm (smooth _)) (smooth _)
    (indexedPermutedAmplitude_extension F legs π.symm (extension _)) q hq π k
  exact indexedPermutedAmplitude_graded F legs π graded

/-- Summing every actual external bijection and dividing by the source
functional-derivative multiplicity n! recovers the actual degree-k Taylor
tensor. The remaining 1/k! is the ordinary finite Taylor normalization. -/
theorem sameAmplitude_normalized_permutation_sum (F : OrderedAmplitude G)
    (smooth : ∀ labels, ContDiff ℝ ∞ (F labels))
    (extension : ∀ labels p, F labels p = F labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hq : BalancedMomenta legs q) (k : ℕ)
    (graded : ∀ π p, BalancedMomenta legs p →
      F (permutedLegs legs π) (permutedMomenta legs π p) =
        permutationSign legs π * F legs p) :
    (1 / ((Nat.factorial legs.length : ℂ) * (Nat.factorial k : ℂ))) *
      (∑ π : Equiv.Perm (Fin legs.length),
        ∑ p : Fin k → Fin legs.length × Fin 4,
          if ReducedDirections legs (List.ofFn p) then
            momentumJet (List.ofFn p) (indexedPermutedAmplitude F legs π.symm) 0 *
              (Complex.I^k * assignedVertexTerm
                (fun j => ⟨legs.get (π.symm j), directionBucket (List.ofFn p) j⟩)
                (fun i => (legs.get i, q i)) π)
          else 0) =
      (1 / (Nat.factorial k : ℂ)) * iteratedFDeriv ℝ k (F legs) 0 (fun _ => q) := by
  classical
  simp_rw [sameAmplitude_permutation_Taylor_block F smooth extension legs q hq _ k
    (graded _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hn : (Nat.factorial legs.length : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero legs.length
  have hk : (Nat.factorial k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

end YangMills.IntegratedNormalization
