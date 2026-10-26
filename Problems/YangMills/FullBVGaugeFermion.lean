import Problems.YangMills.FullBVPartialParity

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def antighostJet (G : CompactSimpleGaugeGroup) (a : Fin G.dimension) : JetAlgebra G :=
  jet ⟨.inl (.antighost a), 0⟩
def auxiliaryJet (G : CompactSimpleGaugeGroup) (a : Fin G.dimension) : JetAlgebra G :=
  jet ⟨.inl (.auxiliary a), 0⟩
def gaugeDivergence (G : CompactSimpleGaugeGroup) (a : Fin G.dimension) : JetAlgebra G :=
  ∑ mu : Fin 4, jet ⟨.inl (.gauge mu a), Pi.single mu 1⟩
def ghostDivergence {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) : JetAlgebra G :=
  ∑ mu : Fin 4, totalDerivative mu
    (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))

/-- The source-compatible shifted-B gauge fermion, fixed with no adjustable
normalization: barc·(divA−iB)/2. Its ST variation supplies gauge fixing,
the auxiliary square and the physical ghost action modulo a fixed current. -/
def gaugeFermionDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension,
    ((∑ mu : Fin 4, (1 / 2 : ℂ) •
      (antighostJet G a * jet ⟨.inl (.gauge mu a), Pi.single mu 1⟩)) +
      (-Complex.I / 2) • (antighostJet G a * auxiliaryJet G a))

private theorem complex_shifted_coefficient : ((-Complex.I / 2 : ℂ) * Complex.I) = 1 / 2 := by
  calc
    _ = -(Complex.I * Complex.I) / 2 := by ring
    _ = _ := by rw [Complex.I_mul_I]; norm_num

theorem auxiliaryJet_commute (a : Fin G.dimension) (P : JetAlgebra G) :
    auxiliaryJet G a * P = P * auxiliaryJet G a := evenJet_commute _ P

private theorem shifted_auxiliary_square (a : Fin G.dimension) :
    (1 / 2 : ℂ) • ((gaugeDivergence G a + Complex.I • auxiliaryJet G a) * gaugeDivergence G a) +
      (-Complex.I / 2) • ((gaugeDivergence G a + Complex.I • auxiliaryJet G a) * auxiliaryJet G a) =
      (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a) +
        (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a) := by
  simp only [add_mul, smul_mul_assoc, smul_add, smul_smul]
  rw [auxiliaryJet_commute, complex_shifted_coefficient]
  module

/-- Actual full ST variation of the fixed gauge fermion. Every ghost term
comes from the SAME nonlinear master action; no gauge-fixing axiom is used. -/
theorem classicalLocalST_gaugeFermion {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    classicalLocalSTDensity e g (gaugeFermionDensity G) =
      ∑ a : Fin G.dimension,
        ((1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a) +
          (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a) +
          ghostDivergence e g a * antighostJet G a) := by
  unfold classicalLocalSTDensity gaugeFermionDensity
  simp only [antighostJet, auxiliaryJet, localST_sum, localST_add, localST_smul, localST_mul_jet,
    localST_jet, prolongedST, totalDerivatives_zero, totalDerivatives_single_one,
    master_characteristic_antighost, master_characteristic_auxiliary_divergence,
    ExternalLeg.parity, BasicField.fermionic, Bool.false_eq_true, if_false]
  apply Finset.sum_congr rfl
  intro a ha
  change (∑ mu : Fin 4, (1 / 2 : ℂ) •
      ((Complex.I • auxiliaryJet G a + gaugeDivergence G a) *
          jet ⟨.inl (.gauge mu a), Pi.single mu 1⟩ +
        totalDerivative mu (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) *
          antighostJet G a)) +
    (-Complex.I / 2) •
      ((Complex.I • auxiliaryJet G a + gaugeDivergence G a) * auxiliaryJet G a +
        (Complex.I • ghostDivergence e g a) * antighostJet G a) = _
  simp only [smul_add, Finset.sum_add_distrib, smul_mul_assoc, smul_smul,
    complex_shifted_coefficient]
  rw [← Finset.smul_sum, ← Finset.mul_sum]
  change (1 / 2 : ℂ) • ((Complex.I • auxiliaryJet G a + gaugeDivergence G a) * gaugeDivergence G a) +
      (∑ mu : Fin 4, (1 / 2 : ℂ) •
        (totalDerivative mu (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) * antighostJet G a)) +
      ((-Complex.I / 2) • ((Complex.I • auxiliaryJet G a + gaugeDivergence G a) * auxiliaryJet G a) +
        (1 / 2 : ℂ) • (ghostDivergence e g a * antighostJet G a)) = _
  rw [← Finset.smul_sum, ← Finset.sum_mul]
  rw [add_comm (Complex.I • auxiliaryJet G a) (gaugeDivergence G a)]
  change ((1 / 2 : ℂ) • ((gaugeDivergence G a + Complex.I • auxiliaryJet G a) * gaugeDivergence G a) +
      (1 / 2 : ℂ) • (ghostDivergence e g a * antighostJet G a)) +
      ((-Complex.I / 2) • ((gaugeDivergence G a + Complex.I • auxiliaryJet G a) * auxiliaryJet G a) +
        (1 / 2 : ℂ) • (ghostDivergence e g a * antighostJet G a)) =
      (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a) +
        (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a) +
        ghostDivergence e g a * antighostJet G a
  have hs := shifted_auxiliary_square (G := G) a
  convert congrArg (fun Z : JetAlgebra G => Z + ghostDivergence e g a * antighostJet G a) hs using 1; module

end YangMills.FullBV
