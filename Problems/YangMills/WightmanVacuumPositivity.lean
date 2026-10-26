import Problems.YangMills.WightmanVacuumKernels

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Positivity of the actual full Wightman kernels

The Borchers positivity form is the norm square of a finite linear
combination of the SAME field words on the SAME vacuum. Adjoint words
reverse the order and use the existing conjugate tests and adjoint indices.
No independent positive correlation functional is supplied.
-/
noncomputable section
namespace YangMills.WightmanData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def adjointWord (Q : WightmanData H) (w : List (Q.FieldIndex × TestFunction)) :
    List (Q.FieldIndex × TestFunction) :=
  w.reverse.map fun a => (Q.adjointIndex a.1, Q.conjugateTest a.2)

/-- Every mixed actual field-word inner product is an actual vacuum
correlation of the adjoint word followed by the second word. -/
theorem vacuumNPoint_adjoint_append (Q : WightmanData H) (h : WightmanAxioms H Q)
    (left right : List (Q.FieldIndex × TestFunction)) :
    Q.vacuumNPoint (Q.adjointWord left ++ right) =
      inner ℂ (Q.word left : H) (Q.word right : H) := by
  induction left generalizing right with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨i,f⟩
      change _ = inner ℂ (Q.field i f (Q.word tail) : H) (Q.word right : H)
      rw [h.adjoint_relation]
      have ht := ih ((Q.adjointIndex i, Q.conjugateTest f) :: right)
      simpa [adjointWord, List.reverse_cons, List.map_append, List.append_assoc,
        WightmanData.word] using ht

/-- Full finite Borchers positivity, with arbitrary complex coefficients
and arbitrary ordered words of the actual component fields. -/
theorem vacuumNPoint_borchers_positive (Q : WightmanData H) (h : WightmanAxioms H Q)
    {ι : Type*} [Fintype ι] (words : ι → List (Q.FieldIndex × TestFunction))
    (c : ι → ℂ) :
    0 ≤ (∑ i : ι, ∑ j : ι, star (c i) * c j *
      Q.vacuumNPoint (Q.adjointWord (words i) ++ words j)).re := by
  have norm_square : (∑ i : ι, ∑ j : ι, star (c i) * c j *
      Q.vacuumNPoint (Q.adjointWord (words i) ++ words j)) =
      inner ℂ (∑ i : ι, c i • (Q.word (words i) : H))
        (∑ i : ι, c i • (Q.word (words i) : H)) := by
    simp only [Q.vacuumNPoint_adjoint_append h, inner_sum, sum_inner,
      inner_smul_left, inner_smul_right]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  rw [norm_square]
  exact inner_self_nonneg (𝕜 := ℂ)

end YangMills.WightmanData
