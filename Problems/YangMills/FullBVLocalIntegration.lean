import Problems.YangMills.FullBVEvolutionaryDerivation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

/-- Actual integration by parts is an equality in the fixed quotient of
local functionals, and retains the order of all possibly odd factors. -/
theorem localClass_integrateByParts (mu : Fin 4) (P Q : JetAlgebra G) :
    localClass (totalDerivative mu P * Q) = -localClass (P * totalDerivative mu Q) := by
  have h := totalDerivative_class_zero mu (P*Q)
  rw [totalDerivative_mul] at h
  change (divergences G).mkQ _ = 0 at h
  rw [map_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem localClass_integrateByParts_list (l : List (Fin 4)) (P Q : JetAlgebra G) :
    localClass (l.foldr totalDerivative P * Q) =
      ((-1 : ℂ) ^ l.length) • localClass (P * l.foldr totalDerivative Q) := by
  induction l generalizing Q with
  | nil => simp
  | cons mu l ih =>
      rw [List.foldr_cons, localClass_integrateByParts, ih]
      rw [← totalDerivative_foldr]
      simp [pow_succ]

/-- The precise Euler integration-by-parts sign for the actual ordered
multi-derivative convention. No odd factors are interchanged. -/
theorem localClass_integrateByParts_multi (alpha : Multiindex) (P Q : JetAlgebra G) :
    localClass (totalDerivatives alpha P * Q) =
      ((-1 : ℂ) ^ derivativeOrder alpha) • localClass (P * totalDerivatives alpha Q) := by
  simpa only [totalDerivatives, derivativeList_length] using
    localClass_integrateByParts_list (derivativeList alpha) P Q

/-- Evolutionary prolongation preserves the actual span of divergences. -/
theorem localST_preserves_divergences (S : JetAlgebra G) :
    divergences G ≤ Submodule.comap (localSTLinear S) (divergences G) := by
  apply Submodule.span_le.mpr
  intro P hP
  obtain ⟨⟨mu,Q⟩,rfl⟩ := hP
  change localST S (totalDerivative mu Q) ∈ divergences G
  rw [← totalDerivative_localST]
  exact Submodule.subset_span ⟨(mu,localST S Q),rfl⟩

/-- A fixed induced operation on integrated local functionals. Its
well-definedness is proved from the actual pointwise ST operator. -/
def localSTFunctional (S : JetAlgebra G) : LocalFunctional G →ₗ[ℂ] LocalFunctional G :=
  (divergences G).mapQ (divergences G) (localSTLinear S) (localST_preserves_divergences S)

@[simp] theorem localSTFunctional_localClass (S P : JetAlgebra G) :
    localSTFunctional S (localClass P) = localClass (localST S P) := rfl

/-- Any two representatives of the same integrated functional have the
same ST image in that same quotient. -/
theorem localST_localClass_eq (S P Q : JetAlgebra G) (h : localClass P = localClass Q) :
    localClass (localST S P) = localClass (localST S Q) :=
  congrArg (localSTFunctional S) h

end YangMills.FullBV
