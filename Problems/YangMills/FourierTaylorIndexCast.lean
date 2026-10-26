import Problems.YangMills.FourierTaylorPermutationBlock

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The arity transport is a fixed linear map, not a change of the amplitude. -/
def momentumIndexCast (legs other : List (ExternalLeg G)) (h : other.length = legs.length) :
    (Fin legs.length → Spacetime) →L[ℝ] (Fin other.length → Spacetime) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.cast h i)

@[simp] theorem momentumIndexCast_apply (legs other : List (ExternalLeg G))
    (h : other.length = legs.length) (q : Fin legs.length → Spacetime)
    (i : Fin other.length) : momentumIndexCast legs other h q i = q (Fin.cast h i) := rfl

theorem momentumIndexCast_basis (legs other : List (ExternalLeg G))
    (h : other.length = legs.length) (d : Fin legs.length × Fin 4) :
    momentumIndexCast legs other h (Pi.single d.1 (Pi.single d.2 1)) =
      Pi.single (Fin.cast h.symm d.1) (Pi.single d.2 1) := by
  classical
  ext i μ
  simp only [momentumIndexCast_apply, Pi.single_apply]
  by_cases hi : i = Fin.cast h.symm d.1
  · subst i
    simp
  · have hn : Fin.cast h i ≠ d.1 := by
      intro he
      apply hi
      simpa only [Fin.cast_cast, Fin.cast_refl] using! congrArg (Fin.cast h.symm) he
    simp only [if_neg hi, if_neg hn, Pi.zero_apply]

/-- Actual iterated coordinate derivatives commute with the literal arity
transport used by the same permuted amplitude. -/
theorem momentumJet_index_cast (legs other : List (ExternalLeg G))
    (h : other.length = legs.length)
    (f : (Fin other.length → Spacetime) → ℂ) (smooth : ContDiff ℝ ∞ f)
    (k : ℕ) (p : Fin k → Fin legs.length × Fin 4) :
    momentumJet (List.ofFn p) (f ∘ momentumIndexCast legs other h) 0 =
      momentumJet (List.ofFn fun i => (Fin.cast h.symm (p i).1, (p i).2)) f 0 := by
  rw [momentumJet_ofFn, momentumJet_ofFn]
  rw [(momentumIndexCast legs other h).iteratedFDeriv_comp_right smooth 0
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))]
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    momentumIndexCast_basis]

/-- Actual derivative buckets are preserved when their field slot and every
derivative direction are cast together. -/
theorem directionBucket_index_cast (legs other : List (ExternalLeg G))
    (h : other.length = legs.length)
    (directions : List (Fin other.length × Fin 4)) (i : Fin other.length) :
    directionBucket (legs := legs)
        (directions.map fun d => (Fin.cast h d.1, d.2)) (Fin.cast h i) =
      directionBucket (legs := other) directions i := by
  classical
  induction directions with
  | nil => simp [directionBucket]
  | cons d ds ih =>
    by_cases hd : d.1 = i
    · simp only [List.map_cons, directionBucket, List.filterMap_cons, hd, if_true]
      exact congrArg (List.cons d.2) ih
    · have hn : Fin.cast h d.1 ≠ Fin.cast h i := by
        intro he
        apply hd
        simpa only [Fin.cast_cast, Fin.cast_refl] using! congrArg (Fin.cast h.symm) he
      simp only [List.map_cons, directionBucket, List.filterMap_cons, if_neg hd, if_neg hn]
      exact ih

/-- The actual reduced-coordinate predicate is unchanged under this cast. -/
theorem ReducedDirections_index_cast (legs other : List (ExternalLeg G))
    (h : other.length = legs.length) (directions : List (Fin other.length × Fin 4)) :
    ReducedDirections legs (directions.map fun d => (Fin.cast h d.1, d.2)) ↔
      ReducedDirections other directions := by
  unfold ReducedDirections
  constructor
  · intro H d hd
    have hv := H (Fin.cast h d.1, d.2) (List.mem_map.mpr ⟨d, hd, rfl⟩)
    simpa only [Fin.val_cast, ← h] using! hv
  · intro H d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    have hv := H a ha
    simpa only [Fin.val_cast, h] using! hv

/-- Exact source-jet conversion for the SAME permuted OrderedAmplitude,
with every derivative slot transported to its literal source arity. -/
theorem momentumJet_indexedPermutedAmplitude (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length))
    (smooth : ContDiff ℝ ∞ (F (permutedLegs legs π)))
    (k : ℕ) (p : Fin k → Fin legs.length × Fin 4) :
    momentumJet (List.ofFn p) (indexedPermutedAmplitude F legs π) 0 =
      momentumJet (List.ofFn fun i =>
        (Fin.cast (by simp only [permutedLegs, List.length_ofFn]) (p i).1, (p i).2))
        (F (permutedLegs legs π)) 0 := by
  exact momentumJet_index_cast legs (permutedLegs legs π)
    (by simp only [permutedLegs, List.length_ofFn])
    (F (permutedLegs legs π)) smooth k p

end YangMills.IntegratedNormalization
