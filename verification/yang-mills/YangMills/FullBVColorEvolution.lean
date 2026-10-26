import YangMills.FullBVCovariantColorDerivative
noncomputable section
set_option maxHeartbeats 2200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def localSTColor (S : JetAlgebra G) (X : ColorPolynomial G) : ColorPolynomial G :=
  fun a => localST S (X a)

theorem localSTColor_add (S : JetAlgebra G) (X Y : ColorPolynomial G) :
    localSTColor S (X+Y) = localSTColor S X + localSTColor S Y := by
  funext a; exact localST_add S (X a) (Y a)
theorem localSTColor_smul (S : JetAlgebra G) (r : ℂ) (X : ColorPolynomial G) :
    localSTColor S (r • X) = r • localSTColor S X := by
  funext a; exact localST_smul S (X a) r
theorem localSTColor_sub (S : JetAlgebra G) (X Y : ColorPolynomial G) :
    localSTColor S (X-Y) = localSTColor S X - localSTColor S Y := by
  funext a; exact map_sub (localSTLinear S) (X a) (Y a)

/-- The actual ST bracket rule when its first color family is even. -/
theorem localSTColor_bracket_even {B : InvariantForm G} (e : ColorFrame B)
    (S : JetAlgebra G) (hS : parity S = S) (X Y : ColorPolynomial G)
    (hX : ∀ a, parity (X a) = X a) :
    localSTColor S (colorPolynomialBracket e X Y) =
      colorPolynomialBracket e (localSTColor S X) Y +
        colorPolynomialBracket e X (localSTColor S Y) := by
  funext a
  simp only [localSTColor, colorPolynomialBracket, localST_sum, localST_smul,
    localST_mul_even S hS, hX, smul_add, Finset.sum_add_distrib, Pi.add_apply]

/-- The actual ST bracket rule when its first color family is odd. -/
theorem localSTColor_bracket_odd {B : InvariantForm G} (e : ColorFrame B)
    (S : JetAlgebra G) (hS : parity S = S) (X Y : ColorPolynomial G)
    (hX : ∀ a, parity (X a) = -(X a)) :
    localSTColor S (colorPolynomialBracket e X Y) =
      colorPolynomialBracket e (localSTColor S X) Y -
        colorPolynomialBracket e X (localSTColor S Y) := by
  have hn (P Q : JetAlgebra G) : (-P)*Q = -(P*Q) := neg_mul P Q
  funext a
  simp only [localSTColor, colorPolynomialBracket, localST_sum, localST_smul,
    localST_mul_even S hS, hX, hn, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply]

theorem colorPolynomialBracket_parity_even_odd {B : InvariantForm G} (e : ColorFrame B)
    (X Y : ColorPolynomial G) (hX : ∀ a, parity (X a) = X a)
    (hY : ∀ a, parity (Y a) = -(Y a)) (a : Fin G.dimension) :
    parity (colorPolynomialBracket e X Y a) = -(colorPolynomialBracket e X Y a) := by
  have hn (P Q : JetAlgebra G) : P*(-Q) = -(P*Q) := mul_neg P Q
  simp only [colorPolynomialBracket, map_sum, map_smul, parity_mul, hX,hY,hn,
    smul_neg, Finset.sum_neg_distrib]

theorem colorPolynomialBracket_odd_symmetric {B : InvariantForm G} (e : ColorFrame B)
    (X Y : ColorPolynomial G) (hX : ∀ a, parity (X a) = -(X a))
    (hY : ∀ a, parity (Y a) = -(Y a)) (a : Fin G.dimension) :
    colorPolynomialBracket e X Y a = colorPolynomialBracket e Y X a := by
  unfold colorPolynomialBracket
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  have hw : X b * Y c = -(Y c * X b) := by
    rw [oddPolynomial_commute (X b) (Y c) (hX b), hY c]
    exact neg_mul (Y c) (X b)
  rw [color_skew_complex e a c b, hw]
  module

/-- Actual parity of the shifted source combination K, including all source
and antighost descendants with their fixed coefficients. -/
theorem parity_shiftedGaugeAntifield (mu : Fin 4) (a : Fin G.dimension) :
    parity (shiftedGaugeAntifieldFamily G mu a) = -(shiftedGaugeAntifieldFamily G mu a) := by
  unfold shiftedGaugeAntifieldFamily gaugeAntifieldFamily antighostDerivativeFamily
    auxiliaryAntifieldDerivativeFamily
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, map_sub, map_add, map_smul,
    parity_jet, ExternalLeg.parity, BasicField.fermionic, Bool.not_false, if_true]
  module

theorem parity_ghostColor (a : Fin G.dimension) :
    parity (ghostColorFamily G a) = -(ghostColorFamily G a) := by
  exact parity_jet _

theorem localSTColor_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) (mu : Fin 4) :
    localSTColor (masterActionDensity e g) (gaugeColorFamily G mu) =
      ghostDerivativeFamily G mu + (g : ℂ) •
        colorPolynomialBracket e (gaugeColorFamily G mu) (ghostColorFamily G) := by
  have h := gaugeCharacteristic_colorFamily e g mu
  funext a
  exact (classicalLocalST_gaugePotential e g mu a).trans (congrFun h a)

/-- Same-master ghost characteristic as the fixed adjoint ghost square. -/
theorem localSTColor_ghost {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    localSTColor (masterActionDensity e g) (ghostColorFamily G) =
      (-(g : ℂ) / 2) • colorPolynomialBracket e (ghostColorFamily G) (ghostColorFamily G) := by
  funext a
  change localST (masterActionDensity e g) (ghostJet G a) = _
  rw [localST_jet, totalDerivatives_zero, master_characteristic_ghost]
  simp only [ghostQuadratic, colorPolynomialBracket, Pi.smul_apply,
    Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  change -(((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
    (ghostJet G b * ghostJet G c)) =
    (-(g : ℂ) / 2) • ((structureConstant e a b c : ℂ) •
      (ghostJet G b * ghostJet G c))
  simp only [smul_smul]
  module

end YangMills.FullBV
