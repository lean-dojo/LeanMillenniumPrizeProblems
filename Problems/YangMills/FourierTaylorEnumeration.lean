import Problems.YangMills.FourierTaylorBuckets
import Problems.YangMills.LocalVertexPolarization
import Problems.YangMills.ActionProbeSupport

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem localMonomialDerivative_arity_zero (source : List (LocalVertexLeg G))
    (external : List (ExternalLeg G × Spacetime))
    (h : source.length ≠ external.length) :
    localMonomialDerivative source external = 0 := by
  by_contra hn
  have hp := YangMills.WardAction.localDerivative_support source external hn
  exact h (by simpa only [List.length_map] using hp.length_eq)

theorem localVertexAmplitude_arity_zero (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (h : v.legs.length ≠ legs.length) : localVertexAmplitude v g legs q = 0 := by
  unfold localVertexAmplitude
  rw [localMonomialDerivative_arity_zero _ _ (by simpa only [List.length_ofFn] using h)]
  simp

private theorem sum_map_flatMap {α β : Type*} (L : List α) (f : α → List β)
    (h : β → ℂ) :
    ((L.flatMap f).map h).sum = (L.map fun a => ((f a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

private theorem sum_map_range (n : ℕ) (f : ℕ → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.sum_toFinset f List.nodup_range]
  congr 1
  ext i
  simp

private theorem sum_map_univ {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℂ) :
    ((Finset.univ.toList).map f).sum = ∑ a, f a := by
  rw [← List.sum_toFinset f (Finset.nodup_toList _)]
  simp

private theorem sum_map_filterMap {α β : Type*} (L : List α) (f : α → Option β)
    (h : β → ℂ) :
    ((L.filterMap f).map h).sum =
      (L.map fun a => (f a).elim 0 h).sum := by
  induction L with
  | nil => simp
  | cons a L ih => cases ha : f a <;> simp [ha, ih]

/-- Evaluation retains the actual finite arity/color/derivative filters. -/
theorem reducedTaylorDensity_amplitude_enumeration (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    FullBV.densityAmplitude (reducedTaylorDensity D F) legs q =
      ∑ n ∈ Finset.range (D+1),
        if n = 0 then 0 else
        ∑ fields : Fin n → ExternalLeg G,
          ∑ k ∈ Finset.range (D+1),
            ∑ dirs : Fin k → (Fin (List.ofFn fields).length × Fin 4),
              if totalDimension (List.ofFn fields) + k ≤ D ∧
                  ReducedDirections (List.ofFn fields) (List.ofFn dirs) then
                localVertexAmplitude
                  (reducedTaylorVertex F (List.ofFn fields) (List.ofFn dirs)) 1 legs q
              else 0 := by
  classical
  rw [reducedTaylorDensity, FullBV.densityAmplitude_vertices]
  change ((reducedTaylorVertices D F).map fun v => localVertexAmplitude v 1 legs q).sum = _
  unfold reducedTaylorVertices
  rw [sum_map_flatMap, sum_map_range]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hn0
  · simp
  · rw [sum_map_flatMap, sum_map_univ]
    apply Finset.sum_congr rfl
    intro fields hf
    rw [sum_map_flatMap, sum_map_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [sum_map_filterMap, sum_map_univ]
    apply Finset.sum_congr rfl
    intro dirs hd
    dsimp only
    split_ifs <;> rfl

/-- The actual finite contribution at one source arity. -/
def taylorArityAmplitude (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
  ∑ fields : Fin n → ExternalLeg G,
    ∑ k ∈ Finset.range (D+1),
      ∑ dirs : Fin k → (Fin (List.ofFn fields).length × Fin 4),
        if totalDimension (List.ofFn fields) + k ≤ D ∧
            ReducedDirections (List.ofFn fields) (List.ofFn dirs) then
          localVertexAmplitude
            (reducedTaylorVertex F (List.ofFn fields) (List.ofFn dirs)) 1 legs q
        else 0

theorem taylorArityAmplitude_mismatch (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (n : ℕ) (hn : n ≠ legs.length) : taylorArityAmplitude D F legs q n = 0 := by
  classical
  unfold taylorArityAmplitude
  split_ifs
  · rfl
  · apply Finset.sum_eq_zero
    intro fields hf
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro dirs hd
    split_ifs
    · apply localVertexAmplitude_arity_zero
      simpa only [reducedTaylorVertex, reducedTaylorSource, List.length_ofFn] using hn
    · rfl

/-- The computed superalgebra Taylor density contains exactly the external
arity sector; all other sectors vanish by actual functional differentiation. -/
theorem reducedTaylorDensity_amplitude_fixed_arity (D : ℕ) (F : OrderedAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hD : legs.length ≤ D) :
    FullBV.densityAmplitude (reducedTaylorDensity D F) legs q =
      taylorArityAmplitude D F legs q legs.length := by
  classical
  rw [reducedTaylorDensity_amplitude_enumeration]
  change (∑ n ∈ Finset.range (D+1), taylorArityAmplitude D F legs q n) = _
  apply Finset.sum_eq_single legs.length
  · intro n hn hne
    exact taylorArityAmplitude_mismatch D F legs q n hne
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

end YangMills.IntegratedNormalization
