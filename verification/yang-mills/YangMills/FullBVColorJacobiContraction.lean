import YangMills.FullBVInteractingNilpotency
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private theorem sum_cyclic {I M : Type*} [Fintype I] [AddCommMonoid M]
    (F : I → I → I → M) :
    (∑ i, ∑ j, ∑ k, F j k i) = ∑ i, ∑ j, ∑ k, F i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, F j k i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

def colorJacobiCoefficient {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) : ℂ :=
  ∑ r : Fin G.dimension,
    (structureConstant e a b r : ℂ) * (structureConstant e r c d : ℂ)

theorem colorJacobiCoefficient_cyclic {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) :
    colorJacobiCoefficient e a b c d + colorJacobiCoefficient e a c d b +
      colorJacobiCoefficient e a d b c = 0 := by
  unfold colorJacobiCoefficient
  exact_mod_cast structureConstant_jacobi e a b c d

/-- The actual color Jacobi tensor contracts to zero against the actual
three-ghost word. Only cyclic reindexing is needed, since a 3-cycle makes
two odd swaps. This is the cubic cancellation used by the BRST square. -/
theorem colorJacobi_ghost_contraction_zero {B : InvariantForm G}
    (e : ColorFrame B) (a : Fin G.dimension) :
    (∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
      colorJacobiCoefficient e a b c d •
        ((ghostJet G b * ghostJet G c) * ghostJet G d)) = 0 := by
  classical
  let F (b c d : Fin G.dimension) : JetAlgebra G :=
    colorJacobiCoefficient e a b c d •
      ((ghostJet G b * ghostJet G c) * ghostJet G d)
  have hp (b c d : Fin G.dimension) : F b c d + F c d b + F d b c = 0 := by
    dsimp [F]
    rw [← ghostJet_cyclic b c d, ghostJet_cyclic d b c]
    rw [← add_smul, ← add_smul, colorJacobiCoefficient_cyclic, zero_smul]
  have h1 : (∑ b, ∑ c, ∑ d, F c d b) = ∑ b, ∑ c, ∑ d, F b c d := sum_cyclic F
  have h2 : (∑ b, ∑ c, ∑ d, F d b c) = ∑ b, ∑ c, ∑ d, F b c d := by
    calc
      _ = ∑ b, ∑ c, ∑ d, F c d b := sum_cyclic (fun b c d => F c d b)
      _ = _ := h1
  have hh : (∑ b, ∑ c, ∑ d, F b c d) +
      (∑ b, ∑ c, ∑ d, F c d b) + (∑ b, ∑ c, ∑ d, F d b c) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    simp only [hp, Finset.sum_const_zero]
  rw [h1, h2] at hh
  change (∑ b, ∑ c, ∑ d, F b c d) = 0
  have h3 : (3 : ℂ) • (∑ b, ∑ c, ∑ d, F b c d) = 0 := by
    simpa only [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, one_smul] using hh
  rcases smul_eq_zero.mp h3 with hzero | hzero
  · norm_num at hzero
  · exact hzero

end YangMills.FullBV
