import YangMills.FullBVPartialTotalDerivative
import YangMills.FullBVMultiDerivativeAlgebra
noncomputable section
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

def positiveMultiindexEquiv (mu : Fin 4) : Multiindex ≃ {alpha : Multiindex // 0 < alpha mu} where
  toFun alpha := ⟨alpha + Pi.single mu 1, by simp⟩
  invFun alpha := alpha.val - Pi.single mu 1
  left_inv alpha := by
    funext nu
    by_cases h : mu = nu
    · subst nu; simp
    · simp [Pi.single_apply, h]
  right_inv alpha := by
    apply Subtype.ext
    funext nu
    by_cases h : mu = nu
    · subst nu
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
      have := alpha.property
      omega
    · simp [Pi.single_apply, h]

theorem derivativeOrder_shift (alpha : Multiindex) (mu : Fin 4) :
    derivativeOrder (alpha + Pi.single mu 1) = derivativeOrder alpha + 1 := by
  simp [derivativeOrder, Pi.add_apply, Finset.sum_add_distrib]

/-- Exact reindexing onto all indices having a predecessor in one direction. -/
theorem finsum_multiindex_shift {A : Type*} [AddCommMonoid A]
    (mu : Fin 4) (f : Multiindex → A) :
    (∑ᶠ alpha : Multiindex, if 0 < alpha mu then f alpha else 0) =
      ∑ᶠ beta : Multiindex, f (beta + Pi.single mu 1) := by
  classical
  calc
    _ = ∑ᶠ alpha : {alpha : Multiindex // 0 < alpha mu}, f alpha.val := by
      symm
      simpa only [finsum_eq_if] using finsum_subtype_eq_finsum_cond (f := f) (fun a => 0 < a mu)
    _ = _ := (finsum_comp_equiv (positiveMultiindexEquiv mu) (f := fun a => f a.val)).symm

/-- The shifted predecessor contribution is precisely the negative total
derivative of the unshifted Euler sum, with all finite-support guards. -/
theorem eulerPredecessor_sum (field : ExternalLeg G) (mu : Fin 4) (P : JetAlgebra G) :
    (∑ᶠ alpha : Multiindex, if 0 < alpha mu then
      ((-1 : ℂ) ^ derivativeOrder alpha) • totalDerivatives alpha
        (leftPartialJet ((⟨field,alpha⟩ : Jet G).unshift mu) P) else 0) =
      -totalDerivative mu (leftEuler field P) := by
  classical
  rw [finsum_multiindex_shift]
  have pointwise (beta : Multiindex) :
      ((-1 : ℂ) ^ derivativeOrder (beta + Pi.single mu 1)) •
        totalDerivatives (beta + Pi.single mu 1)
          (leftPartialJet ((⟨field,beta + Pi.single mu 1⟩ : Jet G).unshift mu) P) =
      -totalDerivative mu (((-1 : ℂ) ^ derivativeOrder beta) •
        totalDerivatives beta (leftPartialJet ⟨field,beta⟩ P)) := by
    have index : ((⟨field,beta + Pi.single mu 1⟩ : Jet G).unshift mu) = ⟨field,beta⟩ := by
      apply Jet.eq_of_coordinates (j := (⟨field,beta + Pi.single mu 1⟩ : Jet G).unshift mu)
        (k := ⟨field,beta⟩)
      · rfl
      · funext nu
        simp only [Jet.unshift, Pi.add_apply, Pi.sub_apply]
        omega
    rw [index, derivativeOrder_shift, totalDerivatives_shift, totalDerivative_smul, pow_succ]
    rw [mul_smul, complex_neg_one_smul, smul_neg]
  simp_rw [pointwise]
  let L : JetAlgebra G →ₗ[ℂ] JetAlgebra G := -(totalDerivativeLinear mu)
  change (∑ᶠ beta, L (((-1 : ℂ) ^ derivativeOrder beta) •
    totalDerivatives beta (leftPartialJet ⟨field,beta⟩ P))) = L (leftEuler field P)
  exact (L.toAddMonoidHom.map_finsum (leftEulerSummands_finite field P)).symm

/-- A total divergence has identically zero actual left variational Euler
derivative, before any quotient is taken. The two finite sums telescope. -/
theorem leftEuler_totalDerivative (field : ExternalLeg G) (mu : Fin 4) (P : JetAlgebra G) :
    leftEuler field (totalDerivative mu P) = 0 := by
  classical
  let A : Multiindex → JetAlgebra G := fun alpha =>
    ((-1 : ℂ) ^ derivativeOrder alpha) •
      totalDerivatives alpha (leftPartialJet ⟨field,alpha⟩ P)
  let B : Multiindex → JetAlgebra G := fun alpha => totalDerivative mu (A alpha)
  let E : Multiindex → JetAlgebra G := fun alpha => if 0 < alpha mu then
    ((-1 : ℂ) ^ derivativeOrder alpha) • totalDerivatives alpha
      (leftPartialJet ((⟨field,alpha⟩ : Jet G).unshift mu) P) else 0
  let T : Multiindex → JetAlgebra G := fun alpha =>
    ((-1 : ℂ) ^ derivativeOrder alpha) •
      totalDerivatives alpha (leftPartialJet ⟨field,alpha⟩ (totalDerivative mu P))
  have ha : (Function.support A).Finite := leftEulerSummands_finite field P
  have hb : (Function.support B).Finite := by
    apply ha.subset
    intro alpha halpha
    contrapose! halpha
    have hz : A alpha = 0 := not_not.mp halpha
    simp [B,hz]
  have ht : (Function.support T).Finite := leftEulerSummands_finite field (totalDerivative mu P)
  have pointwise (alpha : Multiindex) : T alpha = B alpha + E alpha := by
    dsimp [T,B,A,E]
    rw [leftPartialJet_totalDerivative, totalDerivatives_add, smul_add,
      totalDerivative_smul, totalDerivative_totalDerivatives]
    by_cases h : 0 < alpha mu <;>
      simp only [h, if_true, if_false, totalDerivatives_zeroInput, smul_zero]
  have he : (Function.support E).Finite := by
    apply (ht.union hb).subset
    intro alpha halpha
    change E alpha ≠ 0 at halpha
    by_cases hz : T alpha = 0
    · right
      change B alpha ≠ 0
      intro hzero
      have equation := pointwise alpha
      rw [hz,hzero,zero_add] at equation
      exact halpha equation.symm
    · exact Or.inl hz
  change (∑ᶠ alpha, T alpha) = 0
  simp_rw [pointwise]
  rw [finsum_add_distrib hb he]
  have hsum : (∑ᶠ alpha, B alpha) = totalDerivative mu (leftEuler field P) :=
    ((totalDerivativeLinear mu).toAddMonoidHom.map_finsum ha).symm
  have esum : (∑ᶠ alpha, E alpha) = -totalDerivative mu (leftEuler field P) :=
    eulerPredecessor_sum field mu P
  rw [hsum,esum,add_neg_cancel]

end YangMills.FullBV
