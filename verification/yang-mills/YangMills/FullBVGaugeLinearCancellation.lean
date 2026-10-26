import YangMills.FullBVJetProducts
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def totalDerivativeLinear (mu : Fin 4) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun := totalDerivative mu
  map_add' := totalDerivative_add mu
  map_smul' := totalDerivative_smul mu

theorem totalDerivative_sum {I : Type*} (s : Finset I) (P : I → JetAlgebra G)
    (mu : Fin 4) : totalDerivative mu (∑ i ∈ s, P i) =
      ∑ i ∈ s, totalDerivative mu (P i) := map_sum (totalDerivativeLinear mu) P s

/-- The derivative of the SAME quadratic ghost image has exactly the linear
coupling term needed to cancel the derivative-ghost term in s²A. -/
theorem totalDerivative_ghostQuadratic {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    totalDerivative mu (ghostQuadratic e g a) =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a b c : ℂ) * (g : ℂ)) •
          (jet ⟨.inl (.ghost b), Pi.single mu 1⟩ * ghostJet G c) := by
  have hs : (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        (ghostJet G b * jet ⟨.inl (.ghost c), Pi.single mu 1⟩)) =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          (jet ⟨.inl (.ghost b), Pi.single mu 1⟩ * ghostJet G c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro b hb
    rw [color_skew_complex e a b c, ghostJetDeriv_anticommute b c 0 (Pi.single mu 1)]
    simp only [mul_neg, neg_mul, smul_neg, neg_smul, neg_neg]
  simp only [ghostQuadratic, totalDerivative_sum, totalDerivative_smul,
    totalDerivative_ghost_pair, smul_add, Finset.sum_add_distrib]
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← add_smul]
  congr 1
  ring

end YangMills.FullBV
