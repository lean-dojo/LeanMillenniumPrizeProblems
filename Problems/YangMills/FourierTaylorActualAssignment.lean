import Problems.YangMills.FourierTaylorIndexCast
import Problems.YangMills.LocalVertexAmplitudePolarization

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Source directions in the actual permuted word. -/
def actualSourceDirections (legs : List (ExternalLeg G))
    (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) :
    List (Fin (permutedLegs legs π.symm).length × Fin 4) :=
  List.ofFn fun i =>
    (Fin.cast (by simp only [permutedLegs, List.length_ofFn]) (p i).1, (p i).2)

theorem actualSourceDirections_bucket (legs : List (ExternalLeg G))
    (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (j : Fin legs.length) :
    directionBucket (actualSourceDirections legs π k p)
        (Fin.cast (by simp only [permutedLegs, List.length_ofFn]) j) =
      directionBucket (List.ofFn p) j := by
  simpa only [actualSourceDirections, List.map_ofFn, Function.comp_apply] using!
    directionBucket_index_cast (permutedLegs legs π.symm) legs
      (by simp only [permutedLegs, List.length_ofFn]) (List.ofFn p) j

/-- The literal Taylor vertex's indexed source word is precisely the word
used by the verified permutation block, with no change of odd-jet order. -/
theorem actualTaylorVertex_source (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) :
    let v := reducedTaylorVertex F (permutedLegs legs π.symm)
      (actualSourceDirections legs π k p)
    (fun j : Fin legs.length =>
      v.legs.get (Fin.cast (show legs.length =
        (reducedTaylorVertex F (permutedLegs legs π.symm)
          (actualSourceDirections legs π k p)).legs.length by simp only [reducedTaylorVertex, reducedTaylorSource,
        permutedLegs, List.length_ofFn]) j)) =
      fun j => ⟨legs.get (π.symm j), directionBucket (List.ofFn p) j⟩ := by
  funext j
  simp only [reducedTaylorVertex, reducedTaylorSource, List.get_ofFn, Fin.cast_cast]
  have hb := actualSourceDirections_bucket legs π k p j
  rw [hb]
  simp only [permutedLegs, List.get_ofFn, Fin.cast_cast, Fin.cast_refl, id_eq]

/-- The coefficient in the literal finite local density is the SAME
amplitude's indexed source jet, with exactly the fixed Fourier/factorial
normalization. -/
theorem actualTaylorVertex_coefficient (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4)
    (smooth : ContDiff ℝ ∞ (F (permutedLegs legs π.symm))) :
    (reducedTaylorVertex F (permutedLegs legs π.symm)
      (actualSourceDirections legs π k p)).coefficient =
      (Complex.I^k / ((Nat.factorial legs.length : ℂ) * (Nat.factorial k : ℂ))) *
        momentumJet (List.ofFn p) (indexedPermutedAmplitude F legs π.symm) 0 := by
  rw [momentumJet_indexedPermutedAmplitude F legs π.symm smooth k p]
  simp only [reducedTaylorVertex, actualSourceDirections, List.length_ofFn, permutedLegs]

/-- One actual Taylor-vertex assignment is precisely a summand of the
already verified same-amplitude permutation block. -/
theorem actualTaylorVertex_assignment (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4)
    (q : Fin legs.length → Spacetime)
    (smooth : ContDiff ℝ ∞ (F (permutedLegs legs π.symm))) :
    let v := reducedTaylorVertex F (permutedLegs legs π.symm)
      (actualSourceDirections legs π k p)
    v.coefficient * assignedVertexTerm
      (fun j : Fin legs.length => v.legs.get
        (Fin.cast (show legs.length =
        (reducedTaylorVertex F (permutedLegs legs π.symm)
          (actualSourceDirections legs π k p)).legs.length by simp only [reducedTaylorVertex, reducedTaylorSource,
          permutedLegs, List.length_ofFn]) j))
      (fun i => (legs.get i, q i)) π =
      (1 / ((Nat.factorial legs.length : ℂ) * (Nat.factorial k : ℂ))) *
        (momentumJet (List.ofFn p) (indexedPermutedAmplitude F legs π.symm) 0 *
          (Complex.I^k * assignedVertexTerm
            (fun j => ⟨legs.get (π.symm j), directionBucket (List.ofFn p) j⟩)
            (fun i => (legs.get i, q i)) π)) := by
  dsimp only
  rw [actualTaylorVertex_source, actualTaylorVertex_coefficient F legs π k p smooth]
  ring

/-- A literal assignment contribution from the actual finite Taylor vertex. -/
def actualTaylorAssignment (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (q : Fin legs.length → Spacetime) : ℂ :=
  let v := reducedTaylorVertex F (permutedLegs legs π.symm)
    (actualSourceDirections legs π k p)
  v.coefficient * assignedVertexTerm
    (fun j : Fin legs.length => v.legs.get
      (Fin.cast (show legs.length =
        (reducedTaylorVertex F (permutedLegs legs π.symm)
          (actualSourceDirections legs π k p)).legs.length by
            simp only [reducedTaylorVertex, reducedTaylorSource,
              permutedLegs, List.length_ofFn]) j))
    (fun i => (legs.get i, q i)) π

/-- The actual vertex coefficients and actual source-word derivative,
summed over every reduced momentum direction and external assignment,
recover the SAME amplitude's degree-k diagonal Taylor coefficient. -/
theorem actualTaylorAssignments_recover (F : OrderedAmplitude G)
    (smooth : ∀ labels, ContDiff ℝ ∞ (F labels))
    (extension : ∀ labels p, F labels p = F labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hq : BalancedMomenta legs q) (k : ℕ)
    (graded : ∀ π p, BalancedMomenta legs p →
      F (permutedLegs legs π) (permutedMomenta legs π p) =
        permutationSign legs π * F legs p) :
    (∑ π : Equiv.Perm (Fin legs.length),
      ∑ p : Fin k → Fin legs.length × Fin 4,
        if ReducedDirections legs (List.ofFn p) then
          actualTaylorAssignment F legs π k p q else 0) =
      (1 / (Nat.factorial k : ℂ)) * iteratedFDeriv ℝ k (F legs) 0 (fun _ => q) := by
  classical
  rw [← sameAmplitude_normalized_permutation_sum F smooth extension legs q hq k graded]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs
  · exact actualTaylorVertex_assignment F legs π k p q (smooth _)
  · simp only [mul_zero]

end YangMills.IntegratedNormalization
