import Problems.YangMills.FourierTaylorActualAssignment

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Uniform external indexing for each source word in the actual finite
color/species sum. -/
def uniformSourceDirections (legs : List (ExternalLeg G))
    (fields : Fin legs.length → ExternalLeg G) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) :
    List (Fin (List.ofFn fields).length × Fin 4) :=
  List.ofFn fun i => (Fin.cast (List.length_ofFn.symm) (p i).1, (p i).2)

def uniformTaylorVertex (F : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (fields : Fin legs.length → ExternalLeg G) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) : LocalVertex G :=
  reducedTaylorVertex F (List.ofFn fields) (uniformSourceDirections legs fields k p)

def uniformSourceAmplitude (F : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (fields : Fin legs.length → ExternalLeg G) : (Fin legs.length → Spacetime) → ℂ :=
  F (List.ofFn fields) ∘ momentumIndexCast legs (List.ofFn fields) List.length_ofFn

theorem uniformSourceDirections_bucket (legs : List (ExternalLeg G))
    (fields : Fin legs.length → ExternalLeg G) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (j : Fin legs.length) :
    directionBucket (uniformSourceDirections legs fields k p)
        (Fin.cast List.length_ofFn.symm j) = directionBucket (List.ofFn p) j := by
  simpa only [uniformSourceDirections, List.map_ofFn, Function.comp_apply] using!
    directionBucket_index_cast (List.ofFn fields) legs List.length_ofFn.symm (List.ofFn p) j

theorem uniformTaylorVertex_source (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (fields : Fin legs.length → ExternalLeg G) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) :
    (fun j : Fin legs.length => (uniformTaylorVertex F legs fields k p).legs.get
      (Fin.cast (show legs.length = (uniformTaylorVertex F legs fields k p).legs.length by
        simp only [uniformTaylorVertex, reducedTaylorVertex, reducedTaylorSource,
          List.length_ofFn]) j)) =
      fun j => ⟨fields j, directionBucket (List.ofFn p) j⟩ := by
  funext j
  simp only [uniformTaylorVertex, reducedTaylorVertex, reducedTaylorSource,
    List.get_ofFn, Fin.cast_cast]
  rw [uniformSourceDirections_bucket]
  simp only [Fin.cast_refl, id_eq]

theorem uniformTaylorVertex_amplitude (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (fields : Fin legs.length → ExternalLeg G) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (q : Fin legs.length → Spacetime) :
    localVertexAmplitude (uniformTaylorVertex F legs fields k p) 1 legs q =
      (uniformTaylorVertex F legs fields k p).coefficient *
        ∑ π : Equiv.Perm (Fin legs.length),
          assignedVertexTerm (fun j => ⟨fields j, directionBucket (List.ofFn p) j⟩)
            (fun i => (legs.get i, q i)) π := by
  have ha : (uniformTaylorVertex F legs fields k p).legs.length = legs.length := by
    simp only [uniformTaylorVertex, reducedTaylorVertex, reducedTaylorSource, List.length_ofFn]
  rw [localVertexAmplitude_permutation_sum _ 1 legs q ha]
  rw [uniformTaylorVertex_source]
  simp only [uniformTaylorVertex, reducedTaylorVertex, pow_zero, mul_one]

/-- The scalar source coefficient remains its literal same-amplitude jet. -/
theorem uniformTaylorVertex_coefficient (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (fields : Fin legs.length → ExternalLeg G) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4)
    (smooth : ContDiff ℝ ∞ (F (List.ofFn fields))) :
    (uniformTaylorVertex F legs fields k p).coefficient =
      (Complex.I^k / ((Nat.factorial legs.length : ℂ) * (Nat.factorial k : ℂ))) *
        momentumJet (List.ofFn p) (uniformSourceAmplitude F legs fields) 0 := by
  rw [uniformSourceAmplitude, momentumJet_index_cast legs (List.ofFn fields)
    List.length_ofFn (F (List.ofFn fields)) smooth k p]
  simp only [uniformTaylorVertex, reducedTaylorVertex, uniformSourceDirections,
    List.length_ofFn]

/-- Every source field/color sum collapses to the corresponding literal
Taylor-vertex assignment. -/
theorem uniformTaylorVertex_field_sum (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (q : Fin legs.length → Spacetime)
    (π : Equiv.Perm (Fin legs.length)) :
    (∑ fields : Fin legs.length → ExternalLeg G,
      (uniformTaylorVertex F legs fields k p).coefficient *
        assignedVertexTerm (fun j => ⟨fields j, directionBucket (List.ofFn p) j⟩)
          (fun i => (legs.get i, q i)) π) = actualTaylorAssignment F legs π k p q := by
  rw [sum_actual_assigned_fields]
  unfold actualTaylorAssignment
  dsimp only
  rw [actualTaylorVertex_source]
  rfl

theorem totalDimension_permuted_source (legs : List (ExternalLeg G))
    (π : Equiv.Perm (Fin legs.length)) :
    totalDimension (List.ofFn fun j => legs.get (π.symm j)) = totalDimension legs := by
  unfold totalDimension
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Equiv.sum_comp π.symm (fun j => (legs.get j).dimension)]
  have ht := congrArg (fun labels : List (ExternalLeg G) =>
    (labels.map ExternalLeg.dimension).sum) (List.ofFn_get legs)
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using! ht

/-- The engineering-degree filter is transported through the ACTUAL source
sum; matching field words have the same total dimension. -/
theorem uniformTaylorVertex_filtered_field_sum (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4) (q : Fin legs.length → Spacetime)
    (π : Equiv.Perm (Fin legs.length)) :
    (∑ fields : Fin legs.length → ExternalLeg G,
      if totalDimension (List.ofFn fields) + k ≤ D then
        (uniformTaylorVertex F legs fields k p).coefficient *
          assignedVertexTerm (fun j => ⟨fields j, directionBucket (List.ofFn p) j⟩)
            (fun i => (legs.get i, q i)) π
      else 0) =
      if totalDimension legs + k ≤ D then actualTaylorAssignment F legs π k p q else 0 := by
  classical
  have hs := sum_actual_assigned_fields (fun j => directionBucket (List.ofFn p) j)
    (fun i => (legs.get i, q i)) π
    (fun fields => if totalDimension (List.ofFn fields) + k ≤ D then
      (uniformTaylorVertex F legs fields k p).coefficient else 0)
  simp only [ite_mul, zero_mul] at hs
  rw [totalDimension_permuted_source] at hs
  rw [hs]
  split_ifs
  · unfold actualTaylorAssignment
    dsimp only
    rw [actualTaylorVertex_source]
    rfl
  · rfl

end YangMills.IntegratedNormalization
