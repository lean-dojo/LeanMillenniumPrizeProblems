import Problems.YangMills.FullBVColorPolynomialBracket

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def gaugeColorFamily (G : CompactSimpleGaugeGroup) (mu : Fin 4) : ColorPolynomial G :=
  gaugePotentialJet G mu
def ghostColorFamily (G : CompactSimpleGaugeGroup) : ColorPolynomial G := ghostJet G
def ghostDerivativeFamily (G : CompactSimpleGaugeGroup) (mu : Fin 4) : ColorPolynomial G :=
  fun a => jet ⟨.inl (.ghost a), Pi.single mu 1⟩
def gaugeDerivativeFamily (G : CompactSimpleGaugeGroup) (mu nu : Fin 4) : ColorPolynomial G :=
  gaugeFirstJet G mu nu

theorem gaugeCharacteristic_colorFamily {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) :
    (fun a => stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) =
      ghostDerivativeFamily G mu + (g : ℂ) •
        colorPolynomialBracket e (gaugeColorFamily G mu) (ghostColorFamily G) := by
  funext a
  rw [master_characteristic_gauge]
  change jet ⟨.inl (.ghost a), Pi.single mu 1⟩ + gaugeQuadratic e g mu a = _
  simp only [Pi.add_apply, Pi.smul_apply, ghostDerivativeFamily, colorPolynomialBracket,
    gaugeQuadratic, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  change ((structureConstant e a b c : ℂ) * (g : ℂ)) •
    (gaugePotentialJet G mu b * ghostJet G c) =
      ((g : ℂ) * (structureConstant e a b c : ℂ)) •
        (gaugePotentialJet G mu b * ghostJet G c)
  rw [mul_comm]

theorem gaugeColorFamily_central (mu : Fin 4) (a : Fin G.dimension) (P : JetAlgebra G) :
    gaugeColorFamily G mu a * P = P * gaugeColorFamily G mu a := gaugeJet_commute _ _ _ _

theorem totalDerivative_gaugeColorFamily (mu nu : Fin 4) :
    (fun a => totalDerivative mu (gaugeColorFamily G nu a)) =
      gaugeDerivativeFamily G mu nu := by
  funext a
  simp only [gaugeColorFamily, gaugePotentialJet, totalDerivative_jet, Jet.shift, zero_add]
  rfl

theorem totalDerivative_ghostColorFamily (mu : Fin 4) :
    (fun a => totalDerivative mu (ghostColorFamily G a)) = ghostDerivativeFamily G mu := by
  funext a
  simp only [ghostColorFamily, ghostJet, totalDerivative_jet, Jet.shift, zero_add]
  rfl

theorem ghostDerivative_mixed (mu nu : Fin 4) (a : Fin G.dimension) :
    totalDerivative mu (ghostDerivativeFamily G nu a) =
      totalDerivative nu (ghostDerivativeFamily G mu a) := by
  simp only [ghostDerivativeFamily, totalDerivative_jet, Jet.shift, add_comm]

theorem colorPolynomialBracket_sub_left {B : InvariantForm G} (e : ColorFrame B)
    (X Y Z : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e (X-Y) Z a =
      colorPolynomialBracket e X Z a - colorPolynomialBracket e Y Z a := by
  simp only [colorPolynomialBracket, Pi.sub_apply, sub_mul, smul_sub, Finset.sum_sub_distrib]

/-- The curvature transforms covariantly under the actual master-derived
pointwise differential, with the same f, g and full descendant algebra. -/
theorem classicalLocalST_curvature_covariant {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g (nonabelianCurvatureJet e g mu nu a) =
      (g : ℂ) • colorPolynomialBracket e
        (fun b => nonabelianCurvatureJet e g mu nu b) (ghostColorFamily G) a := by
  have hmu := gaugeCharacteristic_colorFamily e g mu
  have hnu := gaugeCharacteristic_colorFamily e g nu
  have hcurl : (fun b => nonabelianCurvatureJet e g mu nu b) =
      (gaugeDerivativeFamily G mu nu - gaugeDerivativeFamily G nu mu) +
        (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G mu) (gaugeColorFamily G nu) := rfl
  have hj := colorPolynomialBracket_jacobi_central e
    (gaugeColorFamily G mu) (gaugeColorFamily G nu) (ghostColorFamily G)
    (gaugeColorFamily_central nu) a
  have hs := colorPolynomialBracket_skew_of_commute e
    (ghostDerivativeFamily G mu) (gaugeColorFamily G nu)
    (fun b c => (gaugeColorFamily_central nu c (ghostDerivativeFamily G mu b)).symm) a
  rw [classicalLocalST_curvature_expansion]
  simp only [smul_add, Finset.sum_add_distrib]
  change totalDerivative mu ((fun b => stCharacteristic (masterActionDensity e g)
      (.inl (.gauge nu b))) a) -
    totalDerivative nu ((fun b => stCharacteristic (masterActionDensity e g)
      (.inl (.gauge mu b))) a) +
    ((g : ℂ) • colorPolynomialBracket e
      (fun b => stCharacteristic (masterActionDensity e g) (.inl (.gauge mu b)))
      (gaugeColorFamily G nu) a +
      (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G mu)
        (fun b => stCharacteristic (masterActionDensity e g) (.inl (.gauge nu b))) a) = _
  rw [hmu, hnu, hcurl]
  simp only [Pi.add_apply, Pi.smul_apply, totalDerivative_add, totalDerivative_smul,
    totalDerivative_colorPolynomialBracket, totalDerivative_gaugeColorFamily,
    totalDerivative_ghostColorFamily, colorPolynomialBracket_add_left,
    colorPolynomialBracket_add_right, colorPolynomialBracket_smul_left,
    colorPolynomialBracket_smul_right, colorPolynomialBracket_sub_left,
    ghostDerivative_mixed mu nu a]
  rw [hs]
  rw [← hj]
  module

end YangMills.FullBV
