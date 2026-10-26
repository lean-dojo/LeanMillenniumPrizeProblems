import Problems.YangMills.FullBVCovariantEvolution
import Problems.YangMills.FullBVTwoGhostPolynomialJacobi

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Same-master shifted-antifield image in exact family notation. -/
theorem localSTColor_shiftedGaugeAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) :
    localSTColor (masterActionDensity e g) (shiftedGaugeAntifieldFamily G mu) =
      curvatureEulerFamily e g mu + (-(g : ℂ)) • colorPolynomialBracket e
        (shiftedGaugeAntifieldFamily G mu) (ghostColorFamily G) := by
  funext a
  exact classicalLocalST_shiftedGaugeAntifield e g mu a

/-- Actual full interacting shifted-source nilpotency, derived from the
same curvature Euler covariance and actual two-ghost Jacobi identity. -/
theorem localSTColor_square_shiftedGaugeAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) :
    localSTColor (masterActionDensity e g)
      (localSTColor (masterActionDensity e g) (shiftedGaugeAntifieldFamily G mu)) = 0 := by
  rw [localSTColor_shiftedGaugeAntifield, localSTColor_add, localSTColor_smul,
    localSTColor_curvatureEuler, localSTColor_bracket_odd e _ (parity_masterActionDensity e g)
      _ _ (parity_shiftedGaugeAntifield mu), localSTColor_shiftedGaugeAntifield,
    localSTColor_ghost]
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, colorPolynomialBracket_add_left,
    colorPolynomialBracket_smul_left, colorPolynomialBracket_smul_right]
  rw [colorPolynomialBracket_twoGhost_Jacobi e (shiftedGaugeAntifieldFamily G mu)]
  simp only [Pi.smul_apply, Pi.zero_apply]
  module

/-- Nilpotency on the actual A† coordinate, including all nonabelian
interactions. The shifted coordinate was proved nilpotent and the actual
bar/B† descendant squares cancel; no full-CME nilpotency axiom is used. -/
theorem classicalLocalST_square_gaugeAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inr (.gauge mu a),0⟩)) = 0 := by
  have hs := congrFun (localSTColor_square_shiftedGaugeAntifield e g mu) a
  have hb : localST (masterActionDensity e g)
      (localST (masterActionDensity e g) (jet ⟨.inl (.antighost a),Pi.single mu 1⟩)) = 0 :=
    classicalLocalST_square_basic_jet e g (.antighost a) (Pi.single mu 1)
  have hB : localST (masterActionDensity e g)
      (localST (masterActionDensity e g) (jet ⟨.inr (.auxiliary a),Pi.single mu 1⟩)) = 0 :=
    localST_square_jet_of_coordinate _ _ (classicalLocalST_square_antiauxiliary e g a) _
  have hd (P Q : JetAlgebra G) : localST (masterActionDensity e g) (P-Q) =
      localST (masterActionDensity e g) P - localST (masterActionDensity e g) Q :=
    map_sub (localSTLinear _) P Q
  change localST (masterActionDensity e g) (localST (masterActionDensity e g)
    ((jet ⟨.inr (.gauge mu a),0⟩ + jet ⟨.inl (.antighost a),Pi.single mu 1⟩) -
      Complex.I • jet ⟨.inr (.auxiliary a),Pi.single mu 1⟩)) = 0 at hs
  simp only [hd, localST_add, localST_smul, hb, hB, add_zero, smul_zero, sub_zero] at hs
  exact hs

end YangMills.FullBV
