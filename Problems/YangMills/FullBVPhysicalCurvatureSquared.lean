import Problems.YangMills.FullBVPhysicalGluonExpansion

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private theorem sum_move_last_four {I J K L R M : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype R] [AddCommMonoid M]
    (f : I → J → K → L → R → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ r, f i j k l r) =
      ∑ r, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l r := by
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ r, ∑ l, f i j k l r := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ r, ∑ k, ∑ l, f i j k l r := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      exact Finset.sum_comm
    _ = ∑ i, ∑ r, ∑ j, ∑ k, ∑ l, f i j k l r := by
      apply Finset.sum_congr rfl; intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem gaugePotentialPair_commute (mu nu : Fin 4) (a b : Fin G.dimension)
    (P : JetAlgebra G) :
    (gaugePotentialJet G mu a * gaugePotentialJet G nu b) * P =
      P * (gaugePotentialJet G mu a * gaugePotentialJet G nu b) := by
  unfold gaugePotentialJet
  rw [mul_assoc, gaugeJet_commute nu b 0 P, ← mul_assoc,
    gaugeJet_commute mu a 0 P, mul_assoc]

/-- The same engine quartic interaction is precisely the square of the
actual Lie bracket in the actual invariant metric. -/
theorem physicalQuarticDensity_curvature {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (physicalQuarticVertices e) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ r : Fin G.dimension,
        ((1 / 4 : ℂ) * (g : ℂ)^2) •
          (gluonBracketJet e mu nu r * gluonBracketJet e mu nu r) := by
  rw [physicalQuarticDensity_expansion]
  simp only [fourColor_structure_contraction, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_smul]
  unfold gluonBracketJet
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul, mul_assoc]
  apply Finset.sum_congr rfl; intro mu hmu
  apply Finset.sum_congr rfl; intro nu hnu
  rw [sum_move_last_four]
  apply Finset.sum_congr rfl; intro r hr
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro d hd
  rw [← mul_assoc (gaugePotentialJet G mu c) (gaugePotentialJet G nu d)
      (gaugePotentialJet G mu a * gaugePotentialJet G nu b),
    gaugePotentialPair_commute mu nu c d, mul_assoc]
  module

/-- Each curvature's linear part and quadratic part commute because all
actual gauge jets are even; no commutative replacement algebra is used. -/
theorem abelianCurvature_gluonBracket_commute {B : InvariantForm G} (e : ColorFrame B)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    abelianCurvatureJet G mu nu a * gluonBracketJet e mu nu a =
      gluonBracketJet e mu nu a * abelianCurvatureJet G mu nu a := by
  unfold abelianCurvatureJet gluonBracketJet gaugeFirstJet gaugePotentialJet
  simp only [sub_mul, mul_sub, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b hb
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro c hc
  rw [gaugeJet_commute nu a (Pi.single mu 1)
      (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.gauge nu c), 0⟩),
    gaugeJet_commute mu a (Pi.single nu 1)
      (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.gauge nu c), 0⟩)]


/-- Exact curvature-square expansion using the SAME fixed cubic and
quartic vertices of the engine. -/
theorem nonabelianCurvature_square_expansion {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
      (1 / 4 : ℂ) •
        (nonabelianCurvatureJet e g mu nu a * nonabelianCurvatureJet e g mu nu a)) =
      (∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
        (1 / 4 : ℂ) • (abelianCurvatureJet G mu nu a * abelianCurvatureJet G mu nu a)) +
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) := by
  rw [physicalCubicDensity_curvature, physicalQuarticDensity_curvature]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro mu hmu
  apply Finset.sum_congr rfl; intro nu hnu
  apply Finset.sum_congr rfl; intro a ha
  unfold nonabelianCurvatureJet
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    ← abelianCurvature_gluonBracket_commute, smul_add, smul_smul]
  module

end YangMills.FullBV
