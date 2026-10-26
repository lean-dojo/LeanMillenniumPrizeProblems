import Problems.YangMills.LegendreIdentityNormalization

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
variable {G : CompactSimpleGaugeGroup}

/-- An adjacent transposition has exactly one ordered inversion. -/
theorem adjacentSwap_inversion {n : ℕ} (i j : Fin n) (adjacent : j.val = i.val+1)
    (a b : Fin n) :
    (a<b ∧ Equiv.swap i j b < Equiv.swap i j a) ↔ a=i ∧ b=j := by
  by_cases hai : a=i <;> by_cases haj : a=j <;>
    by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [Equiv.swap_apply_def] <;> omega

/-- The exact source Koszul sign for an adjacent external interchange. -/
theorem permutationSign_adjacent (legs : List (ExternalLeg G))
    (i j : Fin legs.length) (adjacent : j.val=i.val+1) :
    permutationSign legs (Equiv.swap i j) =
      (-1 : ℂ) ^ (if (legs.get i).parity=true ∧ (legs.get j).parity=true then 1 else 0) := by
  have term : ∀ a b : Fin legs.length,
      (if a<b ∧ Equiv.swap i j b < Equiv.swap i j a ∧
          (legs.get (Equiv.swap i j a)).parity=true ∧
          (legs.get (Equiv.swap i j b)).parity=true then (1:ℕ) else 0) =
      (if a=i ∧ b=j ∧ (legs.get i).parity=true ∧ (legs.get j).parity=true then 1 else 0) := by
    intro a b
    by_cases hab : a=i ∧ b=j
    · obtain ⟨ha,hb⟩ := hab
      subst a
      subst b
      have hi : i<j := by omega
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right, hi, and_comm]
    · have hnot : ¬ (a<b ∧ Equiv.swap i j b < Equiv.swap i j a) := by
        rw [adjacentSwap_inversion i j adjacent]
        exact hab
      have hcond : ¬ (a<b ∧ Equiv.swap i j b < Equiv.swap i j a ∧
          (legs.get (Equiv.swap i j a)).parity=true ∧
          (legs.get (Equiv.swap i j b)).parity=true) := by tauto
      rw [if_neg hcond]
      have hright : ¬ (a=i ∧ b=j ∧ (legs.get i).parity=true ∧ (legs.get j).parity=true) := by tauto
      rw [if_neg hright]
  unfold permutationSign
  simp_rw [term]
  by_cases hp : (legs.get i).parity=true ∧ (legs.get j).parity=true
  · simp only [hp.1, hp.2, and_true, ite_true]
    simp_rw [ite_and]
    simp
  · simp only [hp, and_false, ite_false, Finset.sum_const_zero, pow_zero]

end YangMills.LegendreInsertionBridge
