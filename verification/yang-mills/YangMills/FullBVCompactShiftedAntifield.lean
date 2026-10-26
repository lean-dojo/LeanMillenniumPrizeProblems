import YangMills.FullBVCompactGaugeAntifield
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem gluonActionDensity_curvature_current {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    gluonActionDensity e g + kineticCurrentDivergence G =
      gluonCurvatureDensity e g + gaugeFixingSquareDensity G := by
  have hc : gluonCurvatureDensity e g = abelianCurvatureDensity G +
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) := nonabelianCurvature_square_expansion e g
  have hk := kineticDensity_gaugeFixing (G := G)
  unfold gluonActionDensity
  rw [hc]
  calc
    _ = (freeGluonDensity G + kineticCurrentDivergence G) +
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) := by abel
    _ = _ := by rw [hk]; abel

/-- The fixed gauge-fixing square has exactly its usual gauge Euler gradient,
proved in the actual full polynomial/exterior algebra. -/
theorem rightEuler_gaugeFixing_gauge (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (gaugeFixingSquareDensity G) =
      -(totalDerivative rho (gaugeDivergence G d)) := by
  change leftEuler (.inl (.gauge rho d)) (gaugeFixingSquareDensity G) = _
  unfold gaugeFixingSquareDensity gaugeDivergence
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
    leftEuler_sum, leftEuler_smul,
    leftEuler_quadratic, ExternalLeg.parity, BasicField.fermionic,
    Bool.false_eq_true, if_false, one_smul, derivativeOrder_single,
    totalDerivatives_single_one, Sum.inl.injEq, BasicField.gauge.injEq, pow_one]
  simp only [ite_and, smul_add, smul_ite, smul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [complex_neg_one_smul, smul_neg, totalDerivative_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro mu hmu
  module

/-- The SAME gluon Euler equation differs from curvature's Euler equation
only by the proved fixed gauge-fixing gradient. -/
theorem gluonEuler_curvatureEuler {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (gluonActionDensity e g) =
      rightEuler (.inl (.gauge rho d)) (gluonCurvatureDensity e g) -
        totalDerivative rho (gaugeDivergence G d) := by
  have hs := congrArg (rightEuler (.inl (.gauge rho d)))
    (gluonActionDensity_curvature_current e g)
  simp only [rightEuler_add, kineticCurrentDivergence, rightEuler_sum,
    rightEuler_totalDerivative, Finset.sum_const_zero, add_zero,
    rightEuler_gaugeFixing_gauge] at hs
  simpa only [sub_eq_add_neg] using hs

/-- The actual shifted source combination has a covariant physical Euler
image. The physical Euler term is extracted from the SAME fixed F_g² density,
not supplied as an independent equation of motion. -/
theorem classicalLocalST_shiftedGaugeAntifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    classicalLocalSTDensity e g (shiftedGaugeAntifieldFamily G rho d) =
      rightEuler (.inl (.gauge rho d)) (gluonCurvatureDensity e g) +
        (-(g : ℂ)) • colorPolynomialBracket e
          (shiftedGaugeAntifieldFamily G rho) (ghostColorFamily G) d := by
  have hd (X Y : JetAlgebra G) : localST (masterActionDensity e g) (X-Y) =
      localST (masterActionDensity e g) X - localST (masterActionDensity e g) Y :=
    map_sub (localSTLinear _) X Y
  have hD (X Y : JetAlgebra G) : totalDerivative rho (X-Y) =
      totalDerivative rho X - totalDerivative rho Y := map_sub (totalDerivativeLinear rho) X Y
  change localST (masterActionDensity e g)
    ((jet ⟨.inr (.gauge rho d),0⟩ + jet ⟨.inl (.antighost d),Pi.single rho 1⟩) -
      Complex.I • jet ⟨.inr (.auxiliary d),Pi.single rho 1⟩) = _
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hd, localST_add, localST_smul,
    localST_jet, totalDerivatives_zero, totalDerivatives_single_one,
    master_characteristic_antighost, master_characteristic_antiauxiliary,
    totalDerivative_add, totalDerivative_smul, hD]
  rw [master_characteristic_gaugeAntifield_separated, gluonEuler_curvatureEuler]
  simp only [totalDerivative_jet, Jet.shift, zero_add, smul_sub, smul_add, smul_smul,
    Complex.I_mul_I, complex_neg_one_smul, sub_neg_eq_add]
  change (rightEuler (.inl (.gauge rho d)) (gluonCurvatureDensity e g) -
      totalDerivative rho (gaugeDivergence G d)) +
    jet ⟨.inr (.antighost d),Pi.single rho 1⟩ +
    (-(g : ℂ)) • colorPolynomialBracket e (shiftedGaugeAntifieldFamily G rho)
      (ghostColorFamily G) d +
    (Complex.I • jet ⟨.inl (.auxiliary d),Pi.single rho 1⟩ +
      totalDerivative rho (gaugeDivergence G d)) -
    (Complex.I • jet ⟨.inl (.auxiliary d),Pi.single rho 1⟩ +
      jet ⟨.inr (.antighost d),Pi.single rho 1⟩) = _
  abel

end YangMills.FullBV
