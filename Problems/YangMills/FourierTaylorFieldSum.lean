import Problems.YangMills.LocalVertexPolarization

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- A single actual source/external bijection fixes every field, including
color and antifield species, before a momentum or normalization is chosen. -/
theorem assignedVertexTerm_field_support {n : ℕ}
    (fields : Fin n → ExternalLeg G) (derivatives : Fin n → List (Fin 4))
    (external : Fin n → ExternalLeg G × Spacetime) (π : Equiv.Perm (Fin n))
    (h : fields ≠ (fun j => (external (π.symm j)).1)) :
    assignedVertexTerm (fun j => ⟨fields j, derivatives j⟩) external π = 0 := by
  classical
  have hn : ∃ i, fields (π i) ≠ (external i).1 := by
    by_contra hn
    push Not at hn
    apply h
    funext j
    simpa only [π.apply_symm_apply] using hn (π.symm j)
  obtain ⟨i, hi⟩ := hn
  unfold assignedVertexTerm
  have hz : (∏ j : Fin n,
      assignedFourierFactor ⟨fields (π j), derivatives (π j)⟩ (external j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [assignedFourierFactor, if_neg hi])
  rw [hz, mul_zero]

/-- The finite sum over actual source colors and species collapses for EACH
external permutation. Coefficients can depend on all actual source fields;
no independent invariant tensor or chosen coefficient is substituted. -/
theorem sum_actual_assigned_fields {n : ℕ}
    (derivatives : Fin n → List (Fin 4))
    (external : Fin n → ExternalLeg G × Spacetime) (π : Equiv.Perm (Fin n))
    (coefficient : (Fin n → ExternalLeg G) → ℂ) :
    (∑ fields : Fin n → ExternalLeg G,
      coefficient fields *
        assignedVertexTerm (fun j => ⟨fields j, derivatives j⟩) external π) =
      coefficient (fun j => (external (π.symm j)).1) *
        assignedVertexTerm
          (fun j => ⟨(external (π.symm j)).1, derivatives j⟩) external π := by
  classical
  apply Finset.sum_eq_single (fun j => (external (π.symm j)).1)
  · intro fields hf hn
    rw [assignedVertexTerm_field_support fields derivatives external π hn, mul_zero]
  · simp

end YangMills.IntegratedNormalization
