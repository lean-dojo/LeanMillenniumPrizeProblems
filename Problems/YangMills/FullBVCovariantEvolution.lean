import Problems.YangMills.FullBVActualNoetherIdentity

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def localSTColorLinear (S : JetAlgebra G) : ColorPolynomial G →ₗ[ℂ] ColorPolynomial G where
  toFun := localSTColor S
  map_add' := localSTColor_add S
  map_smul' := localSTColor_smul S

theorem localSTColor_neg (S : JetAlgebra G) (X : ColorPolynomial G) :
    localSTColor S (-X) = -localSTColor S X := map_neg (localSTColorLinear S) X

theorem localSTColor_sum (S : JetAlgebra G) {I : Type*} (s : Finset I) (X : I → ColorPolynomial G) :
    localSTColor S (∑ i ∈ s, X i) = ∑ i ∈ s, localSTColor S (X i) :=
  map_sum (localSTColorLinear S) X s

def colorPolynomialBracketLinearLeft {B : InvariantForm G} (e : ColorFrame B)
    (Y : ColorPolynomial G) : ColorPolynomial G →ₗ[ℂ] ColorPolynomial G where
  toFun := fun X => colorPolynomialBracket e X Y
  map_add' := by intro X Z; funext a; exact colorPolynomialBracket_add_left e X Z Y a
  map_smul' := by intro r X; funext a; exact colorPolynomialBracket_smul_left e r X Y a

theorem colorPolynomialBracket_neg_left {B : InvariantForm G} (e : ColorFrame B)
    (X Y : ColorPolynomial G) :
    colorPolynomialBracket e (-X) Y = -colorPolynomialBracket e X Y :=
  map_neg (colorPolynomialBracketLinearLeft e Y) X

theorem colorPolynomialBracket_sum_left {B : InvariantForm G} (e : ColorFrame B)
    {I : Type*} (s : Finset I) (X : I → ColorPolynomial G) (Y : ColorPolynomial G) :
    colorPolynomialBracket e (∑ i ∈ s, X i) Y =
      ∑ i ∈ s, colorPolynomialBracket e (X i) Y :=
  map_sum (colorPolynomialBracketLinearLeft e Y) X s

/-- Actual ST and ordinary differentiation commute on the full color
family, with every jet descendant retained. -/
theorem localSTColor_totalDerivative (S : JetAlgebra G) (mu : Fin 4) (X : ColorPolynomial G) :
    localSTColor S (fun a => totalDerivative mu (X a)) =
      (fun a => totalDerivative mu (localSTColor S X a)) := by
  funext a
  exact (totalDerivative_localST S mu (X a)).symm

/-- Covariance of an even color polynomial is preserved by the SAME actual
connection derivative, using actual δA=Dc and actual Lie Jacobi. -/
theorem localSTColor_covariantDerivative_even {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X : ColorPolynomial G) (hX : ∀ a, parity (X a) = X a)
    (hcov : localSTColor (masterActionDensity e g) X =
      (g : ℂ) • colorPolynomialBracket e X (ghostColorFamily G)) :
    localSTColor (masterActionDensity e g) (covariantColorDerivative e g mu X) =
      (g : ℂ) • colorPolynomialBracket e (covariantColorDerivative e g mu X) (ghostColorFamily G) := by
  have hA (a : Fin G.dimension) : parity (gaugeColorFamily G mu a) = gaugeColorFamily G mu a := by
    simpa only [gaugeColorFamily, gaugePotentialJet, ExternalLeg.parity,
      BasicField.fermionic, Bool.false_eq_true, if_false] using
      parity_jet (G := G) ⟨.inl (.gauge mu a),0⟩
  have hj := colorPolynomialBracket_jacobi_central e (gaugeColorFamily G mu) X
    (ghostColorFamily G) (fun a P => evenPolynomial_commute (X a) P (hX a))
  have hs := colorPolynomialBracket_skew_of_commute e (ghostDerivativeFamily G mu) X
    (fun b c => (evenPolynomial_commute (X c) (ghostDerivativeFamily G mu b) (hX c)).symm)
  have hx : covariantColorDerivative e g mu X =
      (fun a => totalDerivative mu (X a)) +
        (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G mu) X := rfl
  rw [hx, localSTColor_add, localSTColor_smul,
    localSTColor_bracket_even e _ (parity_masterActionDensity e g) _ _ hA,
    localSTColor_totalDerivative, hcov, localSTColor_gauge]
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, totalDerivative_smul,
    totalDerivative_colorPolynomialBracket, totalDerivative_ghostColorFamily,
    colorPolynomialBracket_add_left, colorPolynomialBracket_smul_left,
    colorPolynomialBracket_add_right, colorPolynomialBracket_smul_right]
  rw [hs a, ← hj a]
  module

/-- Actual curvature Euler gradient covariance, derived from its proved
same-action E=−∇·F expression and the actual curvature transformation law. -/
theorem localSTColor_curvatureEuler {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) :
    localSTColor (masterActionDensity e g) (curvatureEulerFamily e g rho) =
      (g : ℂ) • colorPolynomialBracket e (curvatureEulerFamily e g rho) (ghostColorFamily G) := by
  have hf (mu : Fin 4) : localSTColor (masterActionDensity e g) (curvatureColorFamily e g mu rho) =
      (g : ℂ) • colorPolynomialBracket e (curvatureColorFamily e g mu rho) (ghostColorFamily G) := by
    funext a
    exact classicalLocalST_curvature_covariant e g mu rho a
  have hd (mu : Fin 4) := localSTColor_covariantDerivative_even e g mu
    (curvatureColorFamily e g mu rho) (parity_nonabelianCurvature e g mu rho) (hf mu)
  rw [curvatureEulerFamily_eq, localSTColor_neg, localSTColor_sum]
  simp only [hd, colorPolynomialBracket_neg_left, colorPolynomialBracket_sum_left,
    Finset.smul_sum, smul_neg]

end YangMills.FullBV
