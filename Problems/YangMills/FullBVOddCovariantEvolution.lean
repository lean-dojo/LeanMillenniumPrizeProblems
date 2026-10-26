import Problems.YangMills.FullBVActualGaugeAntifieldNilpotency

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual shifted odd-source connection identity. It follows from
actual δA=Dc, actual odd-family symmetry, central gauge Jacobi and the given
proved source variation; no variational Hessian/CME nilpotency is assumed. -/
theorem localSTColor_covariantDerivative_odd {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X Y : ColorPolynomial G) (hX : ∀ a, parity (X a) = -(X a))
    (hdelta : localSTColor (masterActionDensity e g) X =
      Y + (-(g : ℂ)) • colorPolynomialBracket e X (ghostColorFamily G)) :
    localSTColor (masterActionDensity e g) (covariantColorDerivative e g mu X) =
      covariantColorDerivative e g mu Y + (-(g : ℂ)) •
        colorPolynomialBracket e (covariantColorDerivative e g mu X) (ghostColorFamily G) := by
  have hA (a : Fin G.dimension) : parity (gaugeColorFamily G mu a) = gaugeColorFamily G mu a := by
    simpa only [gaugeColorFamily, gaugePotentialJet, ExternalLeg.parity,
      BasicField.fermionic, Bool.false_eq_true, if_false] using
      parity_jet (G := G) ⟨.inl (.gauge mu a),0⟩
  have hc (a : Fin G.dimension) : parity (ghostDerivativeFamily G mu a) =
      -(ghostDerivativeFamily G mu a) := by exact parity_jet _
  have hdc : colorPolynomialBracket e (ghostDerivativeFamily G mu) X =
      colorPolynomialBracket e X (ghostDerivativeFamily G mu) := by
    funext a; exact colorPolynomialBracket_odd_symmetric e _ _ hc hX a
  have hXA : colorPolynomialBracket e X (gaugeColorFamily G mu) =
      -colorPolynomialBracket e (gaugeColorFamily G mu) X := by
    funext a
    exact colorPolynomialBracket_skew_of_commute e X (gaugeColorFamily G mu)
      (fun b c => (gaugeColorFamily_central mu c (X b)).symm) a
  have hNC : colorPolynomialBracket e (colorPolynomialBracket e X (ghostColorFamily G))
      (gaugeColorFamily G mu) =
      -colorPolynomialBracket e (gaugeColorFamily G mu)
        (colorPolynomialBracket e X (ghostColorFamily G)) := by
    funext a
    exact colorPolynomialBracket_skew_of_commute e _ (gaugeColorFamily G mu)
      (fun b c => (gaugeColorFamily_central mu c
        (colorPolynomialBracket e X (ghostColorFamily G) b)).symm) a
  have hXC : colorPolynomialBracket e X
      (colorPolynomialBracket e (gaugeColorFamily G mu) (ghostColorFamily G)) =
      colorPolynomialBracket e
        (colorPolynomialBracket e (gaugeColorFamily G mu) (ghostColorFamily G)) X := by
    funext a
    exact colorPolynomialBracket_odd_symmetric e _ _ hX
      (colorPolynomialBracket_parity_even_odd e _ _ hA parity_ghostColor) a
  have hj : colorPolynomialBracket e (colorPolynomialBracket e X (ghostColorFamily G))
      (gaugeColorFamily G mu) + colorPolynomialBracket e X
        (colorPolynomialBracket e (gaugeColorFamily G mu) (ghostColorFamily G)) =
      colorPolynomialBracket e (colorPolynomialBracket e X (gaugeColorFamily G mu))
        (ghostColorFamily G) := by
    funext a
    exact colorPolynomialBracket_jacobi_central e X (gaugeColorFamily G mu)
      (ghostColorFamily G) (gaugeColorFamily_central mu) a
  rw [hNC,hXC,hXA,colorPolynomialBracket_neg_left] at hj
  have hx : covariantColorDerivative e g mu X =
      (fun a => totalDerivative mu (X a)) +
        (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G mu) X := rfl
  rw [hx,localSTColor_add,localSTColor_smul,
    localSTColor_bracket_even e _ (parity_masterActionDensity e g) _ _ hA,
    localSTColor_totalDerivative,hdelta,localSTColor_gauge]
  funext a
  simp only [Pi.add_apply,Pi.smul_apply,totalDerivative_add,totalDerivative_smul,
    totalDerivative_colorPolynomialBracket,totalDerivative_ghostColorFamily,
    colorPolynomialBracket_add_left,colorPolynomialBracket_add_right,
    colorPolynomialBracket_smul_left,colorPolynomialBracket_smul_right,
    covariantColorDerivative]
  rw [hdc]
  have hja := congrFun hj a
  simp only [Pi.add_apply,Pi.neg_apply] at hja
  have hC := (congrArg (fun Z : JetAlgebra G => -Z) hja).symm
  simp only [neg_add,neg_neg] at hC
  rw [hC]
  module

end YangMills.FullBV
