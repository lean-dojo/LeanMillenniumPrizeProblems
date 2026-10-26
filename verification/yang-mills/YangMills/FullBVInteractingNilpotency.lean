import YangMills.FullBVPointProduct
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

abbrev ghostJet (G : CompactSimpleGaugeGroup) (a : Fin G.dimension) : JetAlgebra G :=
  jet ⟨.inl (.ghost a), 0⟩

theorem ghostJet_anticommute (a b : Fin G.dimension) :
    ghostJet G a * ghostJet G b + ghostJet G b * ghostJet G a = 0 := by
  change oddJet _ * oddJet _ + oddJet _ * oddJet _ = 0
  simp only [oddJet, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.tmul_add]
  rw [ExteriorAlgebra.ι_add_mul_swap]
  simp

theorem ghostJet_cyclic (a b c : Fin G.dimension) :
    (ghostJet G a * ghostJet G b) * ghostJet G c =
      (ghostJet G b * ghostJet G c) * ghostJet G a := by
  have hab := ghostJet_anticommute (G := G) a b
  have hac := ghostJet_anticommute (G := G) a c
  have h1 := congrArg (fun X : JetAlgebra G => X * ghostJet G c) hab
  have h2 := congrArg (fun X : JetAlgebra G => ghostJet G b * X) hac
  simp only [add_mul, mul_zero, zero_mul, mul_add] at h1 h2
  have he1 : (ghostJet G a * ghostJet G b) * ghostJet G c =
      -((ghostJet G b * ghostJet G a) * ghostJet G c) := eq_neg_of_add_eq_zero_left h1
  have he2 : ghostJet G b * (ghostJet G a * ghostJet G c) =
      -(ghostJet G b * (ghostJet G c * ghostJet G a)) := eq_neg_of_add_eq_zero_left h2
  calc
    _ = -((ghostJet G b * ghostJet G a) * ghostJet G c) := he1
    _ = -(-(ghostJet G b * (ghostJet G c * ghostJet G a))) := by
      rw [mul_assoc, he2]
    _ = _ := by simp [mul_assoc]


def ghostQuadratic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) : JetAlgebra G :=
  ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
      (ghostJet G b * ghostJet G c)

/-- Exact second ST variation of the actual ghost coordinate. It reduces
nilpotency to a fixed cubic expression in actual G tensors, not an assumed
Chevalley--Eilenberg differential on another coefficient algebra. -/
theorem classicalLocalST_square_ghost_expansion {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (ghostJet G a)) =
    ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        (ghostQuadratic e g b * ghostJet G c - ghostQuadratic e g c * ghostJet G b) := by
  have hg (b : Fin G.dimension) :
      stCharacteristic (masterActionDensity e g) (.inl (.ghost b)) =
        -ghostQuadratic e g b := master_characteristic_ghost e g b
  simp only [classicalLocalSTDensity, ghostJet, localST_jet, hg, totalDerivatives_zero]
  change localST (masterActionDensity e g) (-ghostQuadratic e g a) = _
  rw [localST_neg, ghostQuadratic]
  simp only [localST_sum, localST_smul, localST_mul_jet, localST_jet,
    prolongedST, hg, totalDerivatives_zero, parity_jet, ExternalLeg.parity,
    BasicField.fermionic, if_true]
  simp only [neg_mul, mul_neg, neg_neg, sub_eq_add_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [smul_add, smul_neg, neg_add_rev, neg_neg, neg_mul, mul_neg]
  let r : ℂ := (1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)
  let Qb := ghostQuadratic e g b
  let Qc := ghostQuadratic e g c
  let cb := ghostJet G b
  let cc := ghostJet G c
  change -(r • ((-Qc) * (-cb))) + -(r • ((-Qb) * cc)) =
    r • (Qb * cc) + -(r • (Qc * cb))
  have hn1 : (-Qc) * (-cb) = Qc * cb := neg_mul_neg Qc cb
  have hn2 : (-Qb) * cc = -(Qb * cc) := neg_mul Qb cc
  rw [hn1, hn2, smul_neg, neg_neg]
  exact add_comm _ _

end YangMills.FullBV
