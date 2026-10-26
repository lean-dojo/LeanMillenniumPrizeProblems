import YangMills.FullBVCompactGhostAntifield
import YangMills.FullBVBosonicEulerFormula
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual gauge Euler derivative of the physical ghost word. -/
theorem rightEuler_gauge_physicalGhostWord (mu rho : Fin 4)
    (a b c d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d))
      ((jet ⟨.inl (.antighost a),Pi.single mu 1⟩ * gaugePotentialJet G mu b) * ghostJet G c) =
      if mu = rho ∧ b = d then
        jet ⟨.inl (.antighost a),Pi.single mu 1⟩ * ghostJet G c else 0 := by
  classical
  have hp (alpha : Multiindex) : rightPartialJet ⟨.inl (.gauge rho d),alpha⟩
      ((jet ⟨.inl (.antighost a),Pi.single mu 1⟩ * gaugePotentialJet G mu b) * ghostJet G c) =
      if mu = rho ∧ b = d ∧ alpha = 0 then
        jet ⟨.inl (.antighost a),Pi.single mu 1⟩ * ghostJet G c else 0 := by
    by_cases hm : mu = rho <;> by_cases hb : b = d <;> by_cases ha : alpha = 0
    all_goals simp_all [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
      leftPartialJet_mul, leftPartialJet_jet, Jet.mk.injEq, gaugePotentialJet, ghostJet, eq_comm]
  rw [rightEuler_zeroOrder _ _ (by intro alpha ha; simp [hp,ha]), hp]
  simp

/-- The actual gauge Euler derivative of an antifield source word. -/
theorem rightEuler_gauge_sourceWord (mu rho : Fin 4) (K : BasicField G) (beta : Multiindex)
    (b c d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d))
      ((gaugePotentialJet G mu b * ghostJet G c) * jet ⟨.inr K,beta⟩) =
      if mu = rho ∧ b = d then ghostJet G c * jet ⟨.inr K,beta⟩ else 0 := by
  classical
  have hp (alpha : Multiindex) : rightPartialJet ⟨.inl (.gauge rho d),alpha⟩
      ((gaugePotentialJet G mu b * ghostJet G c) * jet ⟨.inr K,beta⟩) =
      if mu = rho ∧ b = d ∧ alpha = 0 then ghostJet G c * jet ⟨.inr K,beta⟩ else 0 := by
    by_cases hm : mu = rho <;> by_cases hb : b = d <;> by_cases ha : alpha = 0
    all_goals simp_all [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
      leftPartialJet_mul, leftPartialJet_jet, Jet.mk.injEq, gaugePotentialJet, ghostJet, eq_comm]
  rw [rightEuler_zeroOrder _ _ (by intro alpha ha; simp [hp,ha]), hp]
  simp

theorem rightEuler_gauge_sourceWord_expanded (mu rho : Fin 4) (K : BasicField G) (beta : Multiindex)
    (b c d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d))
      ((jet ⟨.inl (.gauge mu b),0⟩ * jet ⟨.inl (.ghost c),0⟩) * jet ⟨.inr K,beta⟩) =
      if mu = rho ∧ b = d then jet ⟨.inl (.ghost c),0⟩ * jet ⟨.inr K,beta⟩ else 0 := by
  simpa only [gaugePotentialJet, ghostJet] using
    rightEuler_gauge_sourceWord (G := G) mu rho K beta b c d

/-- Same-action physical ghost contribution to the A† equation. -/
theorem rightEuler_physicalGhost_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (densityOfVertices g (physicalGhostVertices e)) =
      ∑ a : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a d c : ℂ) * (g : ℂ)) •
          (antighostDerivativeFamily G rho a * ghostJet G c) := by
  rw [physicalGhostDensity_expansion]
  change rightEuler (.inl (.gauge rho d))
    (∑ mu : Fin 4, ∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((jet ⟨.inl (.antighost a),Pi.single mu 1⟩ * gaugePotentialJet G mu b) * ghostJet G c)) = _
  simp only [rightEuler_sum, rightEuler_smul,
    rightEuler_gauge_physicalGhostWord]
  simp only [ite_and, smul_ite, smul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rfl

theorem rightEuler_gauge_ghostSourceWord (rho : Fin 4) (d a b c : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d))
      ((ghostJet G b * ghostJet G c) * jet ⟨.inr (.ghost a),0⟩) = 0 := by
  have hp (alpha : Multiindex) : rightPartialJet ⟨.inl (.gauge rho d),alpha⟩
      ((ghostJet G b * ghostJet G c) * jet ⟨.inr (.ghost a),0⟩) = 0 := by
    simp [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
      leftPartialJet_mul, leftPartialJet_jet, Jet.mk.injEq, ghostJet]
  simp [rightEuler, hp]

theorem rightEuler_antifieldAction_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (densityOfVertices g (antifieldActionVertices e)) =
      (∑ a : Fin G.dimension, ∑ c : Fin G.dimension,
        (-(structureConstant e a d c : ℂ) * (g : ℂ)) •
          (ghostJet G c * gaugeAntifieldFamily G rho a)) +
      (∑ a : Fin G.dimension, ∑ c : Fin G.dimension,
        (Complex.I * (structureConstant e a d c : ℂ) * (g : ℂ)) •
          (ghostJet G c * auxiliaryAntifieldDerivativeFamily G rho a)) := by
  rw [antifieldDensity_eq_nonlinearSource]
  simp only [nonlinearSourceDensity, rightEuler_sum, rightEuler_add, rightEuler_smul,
    rightEuler_gauge_ghostSourceWord, smul_zero, zero_add, rightEuler_gauge_sourceWord_expanded]
  simp only [ite_and, smul_ite, smul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_add_distrib]
  rfl

theorem rightEuler_freeGluon_gauge (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (freeGluonDensity G) =
      -(∑ mu : Fin 4, jet ⟨.inl (.gauge rho d),Pi.single mu 2⟩) := by
  unfold freeGluonDensity gaugeFirstJet
  simp only [rightEuler_sum, rightEuler_smul,
    rightEuler_even_quadratic _ _ _ (by rfl), leftEuler_quadratic,
    ExternalLeg.parity, BasicField.fermionic, Bool.false_eq_true, if_false, one_smul,
    derivativeOrder_single, totalDerivatives_jet, single_one_add_one,
    Sum.inl.injEq, BasicField.gauge.injEq, pow_one]
  simp only [ite_and, smul_add, smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [complex_neg_one_smul, smul_neg, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.smul_sum]
  apply Finset.sum_congr rfl; intro mu hmu
  module

theorem ghost_gaugeAntifield_anticommute (rho : Fin 4) (a c : Fin G.dimension) :
    ghostJet G c * gaugeAntifieldFamily G rho a =
      -(gaugeAntifieldFamily G rho a * ghostJet G c) := by
  apply eq_neg_of_add_eq_zero_left
  exact oddJet_anticommute _ _

theorem ghost_auxiliaryAntifieldDerivative_anticommute (rho : Fin 4) (a c : Fin G.dimension) :
    ghostJet G c * auxiliaryAntifieldDerivativeFamily G rho a =
      -(auxiliaryAntifieldDerivativeFamily G rho a * ghostJet G c) := by
  apply eq_neg_of_add_eq_zero_left
  exact oddJet_anticommute _ _

/-- The physical ghost and all actual source terms in the A† equation are
one fixed adjoint term in the SAME shifted antifield combination K. -/
theorem gaugeGhostSourceEuler_compact {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) (d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d)) (densityOfVertices g (physicalGhostVertices e)) +
      rightEuler (.inl (.gauge rho d)) (densityOfVertices g (antifieldActionVertices e)) =
      (-(g : ℂ)) • colorPolynomialBracket e
        (shiftedGaugeAntifieldFamily G rho) (ghostColorFamily G) d := by
  rw [rightEuler_physicalGhost_gauge, rightEuler_antifieldAction_gauge]
  simp only [← Finset.sum_add_distrib]
  unfold colorPolynomialBracket
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro c hc
  rw [color_skew_first_complex e a d c, ghost_gaugeAntifield_anticommute,
    ghost_auxiliaryAntifieldDerivative_anticommute]
  unfold shiftedGaugeAntifieldFamily ghostColorFamily
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, sub_mul, add_mul,
    smul_mul_assoc, smul_neg]
  module

/-- Actual pure-gluon density inherited from the same free, cubic and
quartic vertex lists; it excludes only ghost/B/source sectors. -/
def gluonActionDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  freeGluonDensity G + densityOfVertices g (physicalCubicVertices e) +
    densityOfVertices g (physicalQuarticVertices e)

/-- Compact actual A† equation with its fully fixed same-action gluon
Euler derivative and the covariant shifted source/antighost contribution. -/
theorem master_characteristic_gaugeAntifield_separated {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (rho : Fin 4) (d : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inr (.gauge rho d)) =
      rightEuler (.inl (.gauge rho d)) (gluonActionDensity e g) +
        jet ⟨.inr (.antighost d),Pi.single rho 1⟩ +
        (-(g : ℂ)) • colorPolynomialBracket e
          (shiftedGaugeAntifieldFamily G rho) (ghostColorFamily G) d := by
  change rightEuler (.inl (.gauge rho d)) (masterActionDensity e g) = _
  conv_lhs => rw [masterActionDensity, rightEuler_add, interactionDensity,
    densityOfVertices_append, rightEuler_add, physicalDensity_split,
    rightEuler_add, rightEuler_add]
  change stCharacteristic (freeActionDensity G) (.inr (.gauge rho d)) + _ = _
  rw [free_characteristic_antigauge]
  have hg := gaugeGhostSourceEuler_compact e g rho d
  unfold gluonActionDensity
  rw [rightEuler_add, rightEuler_add, rightEuler_freeGluon_gauge, ← hg]
  abel

end YangMills.FullBV
