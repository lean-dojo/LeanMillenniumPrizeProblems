import YangMills.FullBVTotalDerivativeAlgebra
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

theorem derivativeList_shift_perm (alpha : Multiindex) (mu : Fin 4) :
    (derivativeList (alpha + Pi.single mu 1)).Perm (mu :: derivativeList alpha) := by
  apply List.perm_iff_count.mpr
  intro nu
  rw [derivativeList_count, List.count_cons, derivativeList_count]
  by_cases h : mu = nu <;> simp [Pi.add_apply, h]

/-- Prolongation by a shifted actual jet equals one more ordinary derivative
of its characteristic. The order convention in derivativeList is irrelevant. -/
theorem totalDerivatives_shift (alpha : Multiindex) (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivatives (alpha + Pi.single mu 1) P =
      totalDerivative mu (totalDerivatives alpha P) := by
  letI : LeftCommutative (totalDerivative (G := G)) := ⟨totalDerivative_comm⟩
  exact (derivativeList_shift_perm alpha mu).foldr_eq P

theorem totalDerivative_foldr (l : List (Fin 4)) (mu : Fin 4) (P : JetAlgebra G) :
    totalDerivative mu (l.foldr totalDerivative P) =
      l.foldr totalDerivative (totalDerivative mu P) := by
  induction l with
  | nil => rfl
  | cons nu l ih =>
      simpa only [List.foldr_cons, ih] using
        totalDerivative_comm mu nu (l.foldr totalDerivative P)

theorem totalDerivative_totalDerivatives (mu : Fin 4) (alpha : Multiindex) (P : JetAlgebra G) :
    totalDerivative mu (totalDerivatives alpha P) =
      totalDerivatives alpha (totalDerivative mu P) :=
  totalDerivative_foldr (derivativeList alpha) mu P

end YangMills.FullBV
