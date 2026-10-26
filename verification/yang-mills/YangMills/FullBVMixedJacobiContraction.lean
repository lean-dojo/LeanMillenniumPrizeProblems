import YangMills.FullBVJetProducts
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def mixedGhostWord (G : CompactSimpleGaugeGroup) (mu : Fin 4)
    (b c d : Fin G.dimension) : JetAlgebra G :=
  (jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c) * ghostJet G d

theorem mixedGhostWord_skew (mu : Fin 4) (b c d : Fin G.dimension) :
    mixedGhostWord G mu b c d = -(mixedGhostWord G mu b d c) := by
  unfold mixedGhostWord
  rw [mul_assoc, ghostJetDeriv_anticommute c d 0 0]
  change jet (G := G) ⟨.inl (.gauge mu b), 0⟩ *
    (-(ghostJet G d * ghostJet G c)) =
    -((jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G d) * ghostJet G c)
  exact (mul_neg (jet ⟨.inl (.gauge mu b), 0⟩) (ghostJet G d * ghostJet G c)).trans
    (congrArg Neg.neg (mul_assoc (jet ⟨.inl (.gauge mu b), 0⟩) (ghostJet G d) (ghostJet G c)).symm)

theorem colorJacobiCoefficient_skew_last {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) :
    colorJacobiCoefficient e a b c d = -colorJacobiCoefficient e a b d c := by
  unfold colorJacobiCoefficient
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [color_skew_complex e r c d]
  ring

/-- Actual two-ghost Jacobi contraction: twice [[A,c],c] is [A,[c,c]].
The iterated-bracket coefficient is -J(a,d,b,c); all tensors and word signs
come from the same G and the same superjet algebra as the action. -/
theorem colorJacobi_mixed_contraction {B : InvariantForm G} (e : ColorFrame B)
    (mu : Fin 4) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
      colorJacobiCoefficient e a b c d • mixedGhostWord G mu b c d) =
    (2 : ℂ) • (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
      (-colorJacobiCoefficient e a d b c) • mixedGhostWord G mu b c d) := by
  let F (b c d : Fin G.dimension) :=
    colorJacobiCoefficient e a b c d • mixedGhostWord G mu b c d
  let H (b c d : Fin G.dimension) :=
    colorJacobiCoefficient e a c d b • mixedGhostWord G mu b c d
  let K (b c d : Fin G.dimension) :=
    colorJacobiCoefficient e a d b c • mixedGhostWord G mu b c d
  have hp (b c d : Fin G.dimension) : F b c d + H b c d + K b c d = 0 := by
    dsimp [F, H, K]
    rw [← add_smul, ← add_smul, colorJacobiCoefficient_cyclic, zero_smul]
  have hh : (∑ b, ∑ c, ∑ d, H b c d) = ∑ b, ∑ c, ∑ d, K b c d := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [H, K]
    rw [colorJacobiCoefficient_skew_last e a d c b, mixedGhostWord_skew mu b d c]
    exact neg_smul_neg _ _
  have ht : (∑ b, ∑ c, ∑ d, F b c d) +
      (∑ b, ∑ c, ∑ d, H b c d) + (∑ b, ∑ c, ∑ d, K b c d) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    simp only [hp, Finset.sum_const_zero]
  rw [hh] at ht
  have hn : (∑ b, ∑ c, ∑ d,
      (-colorJacobiCoefficient e a d b c) • mixedGhostWord G mu b c d) =
      -(∑ b, ∑ c, ∑ d, K b c d) := by
    simp only [K]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact neg_smul (colorJacobiCoefficient e a d b c) (mixedGhostWord G mu b c d)
  rw [hn]
  change (∑ b, ∑ c, ∑ d, F b c d) = _
  have ht' : (∑ b, ∑ c, ∑ d, F b c d) +
      ((∑ b, ∑ c, ∑ d, K b c d) + (∑ b, ∑ c, ∑ d, K b c d)) = 0 := by
    simpa only [add_assoc] using ht
  have he := eq_neg_of_add_eq_zero_left ht' 
  simpa only [two_smul, smul_neg, neg_add_rev] using he

end YangMills.FullBV
