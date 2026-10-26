import YangMills.FourierTaylorUniformSource

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Actual change of the finite direction enumeration to a common external
index type, leaving the source momentum slots in the vertex cast back. -/
def directionIndexEquiv (legs : List (ExternalLeg G))
    (fields : Fin legs.length → ExternalLeg G) (k : ℕ) :
    (Fin k → Fin (List.ofFn fields).length × Fin 4) ≃
      (Fin k → Fin legs.length × Fin 4) :=
  Equiv.piCongrRight fun _ =>
    Equiv.prodCongr (finCongr List.length_ofFn) (Equiv.refl (Fin 4))

theorem uniform_direction_sum (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (fields : Fin legs.length → ExternalLeg G)
    (k : ℕ) (q : Fin legs.length → Spacetime) :
    (∑ dirs : Fin k → Fin (List.ofFn fields).length × Fin 4,
      if totalDimension (List.ofFn fields) + k ≤ D ∧
          ReducedDirections (List.ofFn fields) (List.ofFn dirs) then
        localVertexAmplitude (reducedTaylorVertex F (List.ofFn fields) (List.ofFn dirs))
          1 legs q else 0) =
      ∑ p : Fin k → Fin legs.length × Fin 4,
        if totalDimension (List.ofFn fields) + k ≤ D ∧
            ReducedDirections legs (List.ofFn p) then
          localVertexAmplitude (uniformTaylorVertex F legs fields k p) 1 legs q else 0 := by
  classical
  rw [← Equiv.sum_comp (directionIndexEquiv legs fields k).symm]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (directionIndexEquiv legs fields k).symm p =
      fun i => (Fin.cast List.length_ofFn.symm (p i).1, (p i).2) := rfl
  rw [he]
  have hr : ReducedDirections (List.ofFn fields)
      (List.ofFn fun i => (Fin.cast List.length_ofFn.symm (p i).1, (p i).2)) ↔
      ReducedDirections legs (List.ofFn p) := by
    simpa only [List.map_ofFn, Function.comp_apply] using
      ReducedDirections_index_cast (List.ofFn fields) legs List.length_ofFn.symm (List.ofFn p)
  rw [hr]
  rfl

theorem taylorArityAmplitude_uniform (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hne : legs.length ≠ 0) :
    taylorArityAmplitude D F legs q legs.length =
      ∑ fields : Fin legs.length → ExternalLeg G,
        ∑ k ∈ Finset.range (D+1),
          ∑ p : Fin k → Fin legs.length × Fin 4,
            if totalDimension (List.ofFn fields) + k ≤ D ∧
                ReducedDirections legs (List.ofFn p) then
              localVertexAmplitude (uniformTaylorVertex F legs fields k p) 1 legs q else 0 := by
  unfold taylorArityAmplitude
  rw [if_neg hne]
  apply Finset.sum_congr rfl
  intro fields hf
  apply Finset.sum_congr rfl
  intro k hk
  exact uniform_direction_sum D F legs fields k q

/-- Actual finite source-field summation and the engineering filter reduce
the vertex amplitudes to their literal external assignment contributions. -/
theorem uniform_filtered_amplitude_assignments (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (q : Fin legs.length → Spacetime) :
    (∑ fields : Fin legs.length → ExternalLeg G,
      if totalDimension (List.ofFn fields) + k ≤ D ∧
          ReducedDirections legs (List.ofFn p) then
        localVertexAmplitude (uniformTaylorVertex F legs fields k p) 1 legs q else 0) =
      if totalDimension legs + k ≤ D ∧ ReducedDirections legs (List.ofFn p) then
        ∑ π : Equiv.Perm (Fin legs.length), actualTaylorAssignment F legs π k p q else 0 := by
  classical
  by_cases hr : ReducedDirections legs (List.ofFn p)
  · simp only [hr, and_true]
    have expand (fields : Fin legs.length → ExternalLeg G) :
        (if totalDimension (List.ofFn fields) + k ≤ D then
          localVertexAmplitude (uniformTaylorVertex F legs fields k p) 1 legs q else 0) =
        ∑ π : Equiv.Perm (Fin legs.length),
          if totalDimension (List.ofFn fields) + k ≤ D then
            (uniformTaylorVertex F legs fields k p).coefficient *
              assignedVertexTerm (fun j => ⟨fields j, directionBucket (List.ofFn p) j⟩)
                (fun i => (legs.get i, q i)) π else 0 := by
      by_cases hd : totalDimension (List.ofFn fields) + k ≤ D
      · simp only [if_pos hd, uniformTaylorVertex_amplitude, Finset.mul_sum]
      · simp only [if_neg hd, Finset.sum_const_zero]
    simp_rw [expand]
    rw [Finset.sum_comm]
    simp_rw [uniformTaylorVertex_filtered_field_sum]
    by_cases hd : totalDimension legs + k ≤ D
    · simp only [if_pos hd]
    · simp only [if_neg hd, Finset.sum_const_zero]
  · simp only [hr, and_false, if_false, Finset.sum_const_zero]

/-- Actual balanced amplitude recovery of the computed finite local Taylor
density. The equality is proved from the same amplitude's derivative,
conserving-extension and graded laws; no reconstruction condition is assumed. -/
theorem reducedTaylorDensity_balanced_recovery (D : ℕ) (F : OrderedAmplitude G)
    (smooth : ∀ labels, ContDiff ℝ ∞ (F labels))
    (extension : ∀ labels p, F labels p = F labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hne : legs.length ≠ 0) (hD : legs.length ≤ D) (hq : BalancedMomenta legs q)
    (graded : ∀ π p, BalancedMomenta legs p →
      F (permutedLegs legs π) (permutedMomenta legs π p) =
        permutationSign legs π * F legs p) :
    FullBV.densityAmplitude (reducedTaylorDensity D F) legs q =
      ∑ k ∈ Finset.range (D+1),
        if totalDimension legs + k ≤ D then
          (1 / (Nat.factorial k : ℂ)) * iteratedFDeriv ℝ k (F legs) 0 (fun _ => q)
        else 0 := by
  classical
  rw [reducedTaylorDensity_amplitude_fixed_arity D F legs q hD,
    taylorArityAmplitude_uniform D F legs q hne, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  simp_rw [uniform_filtered_amplitude_assignments]
  by_cases hd : totalDimension legs + k ≤ D
  · simp only [hd, true_and, if_true]
    have hexpand (p : Fin k → Fin legs.length × Fin 4) :
        (if ReducedDirections legs (List.ofFn p) then
          ∑ π : Equiv.Perm (Fin legs.length), actualTaylorAssignment F legs π k p q else 0) =
        ∑ π : Equiv.Perm (Fin legs.length),
          if ReducedDirections legs (List.ofFn p) then actualTaylorAssignment F legs π k p q
          else 0 := by
      by_cases hr : ReducedDirections legs (List.ofFn p)
      · simp only [if_pos hr]
      · simp only [if_neg hr, Finset.sum_const_zero]
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    exact actualTaylorAssignments_recover F smooth extension legs q hq k graded
  · simp only [hd, false_and, if_false, Finset.sum_const_zero]

end YangMills.IntegratedNormalization
