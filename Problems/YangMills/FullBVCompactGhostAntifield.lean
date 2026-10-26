import Problems.YangMills.FullBVActualMasterEulerConsequences
import Problems.YangMills.FullBVGhostAntifield

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Cyclicity follows from the same actual invariant metric used by all
vertices, rather than a free invariant-tensor premise. -/
theorem color_cycle_complex {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) :
    (structureConstant e a b c : ℂ) = (structureConstant e c a b : ℂ) := by
  have h := B.invariant (e.basis b) (e.basis a) (e.basis c)
  rw [← lie_skew (e.basis b) (e.basis a), map_neg, LinearMap.neg_apply,
    B.symmetric ⁅e.basis a, e.basis b⁆ (e.basis c)] at h
  have hc : structureConstant e a b c = structureConstant e c a b := by
    dsimp [structureConstant, threeColor]
    linarith
  exact_mod_cast hc

def ghostAntifieldFamily (G : CompactSimpleGaugeGroup) : ColorPolynomial G :=
  fun a => jet ⟨.inr (.ghost a),0⟩
def antighostDerivativeFamily (G : CompactSimpleGaugeGroup) (mu : Fin 4) : ColorPolynomial G :=
  fun a => jet ⟨.inl (.antighost a),Pi.single mu 1⟩
def gaugeAntifieldFamily (G : CompactSimpleGaugeGroup) (mu : Fin 4) : ColorPolynomial G :=
  fun a => jet ⟨.inr (.gauge mu a),0⟩
def auxiliaryAntifieldDerivativeFamily (G : CompactSimpleGaugeGroup) (mu : Fin 4) : ColorPolynomial G :=
  fun a => jet ⟨.inr (.auxiliary a),Pi.single mu 1⟩

/-- The actual shifted source/antighost combination, with its fixed phase. -/
def shiftedGaugeAntifieldFamily (G : CompactSimpleGaugeGroup) (mu : Fin 4) : ColorPolynomial G :=
  gaugeAntifieldFamily G mu + antighostDerivativeFamily G mu -
    Complex.I • auxiliaryAntifieldDerivativeFamily G mu

theorem ghostSourceContribution_compact {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (d : Fin G.dimension) :
    (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((if b = d then -(ghostJet G c * jet ⟨.inr (.ghost a), 0⟩) else 0) +
          (if c = d then ghostJet G b * jet ⟨.inr (.ghost a), 0⟩ else 0))) =
      (g : ℂ) • colorPolynomialBracket e (ghostAntifieldFamily G) (ghostColorFamily G) d := by
  simp only [smul_add, smul_ite, smul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const_zero]
  unfold colorPolynomialBracket ghostAntifieldFamily ghostColorFamily
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c hc
  rw [color_skew_complex e a d c, color_cycle_complex e a c d]
  have he : ghostJet G c * jet ⟨.inr (.ghost a),0⟩ =
      jet ⟨.inr (.ghost a),0⟩ * ghostJet G c :=
    (evenJet_commute ⟨⟨.inr (.ghost a),0⟩, by rfl⟩ (ghostJet G c)).symm
  rw [he]
  module

/-- Fixed actual color rotation and the actual even gauge coordinate convert
all three antighost/source contributions to the same adjoint covariant term. -/
theorem rotatedGaugeColorContraction {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X : ColorPolynomial G) (d : Fin G.dimension) :
    (∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
      ((structureConstant e a b d : ℂ) * (g : ℂ)) •
        (X a * gaugeColorFamily G mu b)) =
      (-(g : ℂ)) • colorPolynomialBracket e (gaugeColorFamily G mu) X d := by
  unfold colorPolynomialBracket
  simp only [Finset.smul_sum, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [color_cycle_complex e a b d, color_skew_complex e d a b,
    ← gaugeColorFamily_central mu b (X a)]
  module

private theorem sum_last_first {I J K M : Type*} [Fintype I] [Fintype J]
    [Fintype K] [AddCommMonoid M] (f : I → J → K → M) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl; intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem rotatedGaugeSourceContraction {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (X : Fin 4 → ColorPolynomial G) (d : Fin G.dimension) :
    (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ mu : Fin 4,
      ((structureConstant e a b d : ℂ) * (g : ℂ)) •
        (gaugeColorFamily G mu b * X mu a)) =
      (-(g : ℂ)) • ∑ mu : Fin 4,
        colorPolynomialBracket e (gaugeColorFamily G mu) (X mu) d := by
  rw [sum_last_first]
  simp only [gaugeColorFamily_central]
  simp only [Finset.smul_sum, ← rotatedGaugeColorContraction e g]

theorem colorPolynomialBracket_sub_right {B : InvariantForm G} (e : ColorFrame B)
    (X Y Z : ColorPolynomial G) (a : Fin G.dimension) :
    colorPolynomialBracket e X (Y-Z) a =
      colorPolynomialBracket e X Y a - colorPolynomialBracket e X Z a := by
  simp only [colorPolynomialBracket, Pi.sub_apply, mul_sub, smul_sub, Finset.sum_sub_distrib]

/-- All the literal interaction corrections in the actual c† Euler image
combine into the covariant divergence of its shifted source combination and
the actual ghost-antifield adjoint term. -/
theorem ghostAntifieldCorrection_compact {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (d : Fin G.dimension) :
    ghostAntifieldCorrection e g d =
      (-(g : ℂ)) • (∑ mu : Fin 4,
        colorPolynomialBracket e (gaugeColorFamily G mu)
          (shiftedGaugeAntifieldFamily G mu) d) +
        (g : ℂ) • colorPolynomialBracket e (ghostAntifieldFamily G) (ghostColorFamily G) d := by
  have hp : (∑ mu : Fin 4, ∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
      ((structureConstant e a b d : ℂ) * (g : ℂ)) •
        (antighostDerivativeFamily G mu a * gaugeColorFamily G mu b)) =
      (-(g : ℂ)) • (∑ mu : Fin 4,
        colorPolynomialBracket e (gaugeColorFamily G mu) (antighostDerivativeFamily G mu) d) := by
    simp only [Finset.smul_sum, ← rotatedGaugeColorContraction e g]
  have hA := rotatedGaugeSourceContraction e g (gaugeAntifieldFamily G) d
  have hB := rotatedGaugeSourceContraction e g (auxiliaryAntifieldDerivativeFamily G) d
  unfold ghostAntifieldCorrection
  rw [ghostSourceContribution_compact]
  have hneg (r : ℂ) (P : JetAlgebra G) : ((-r) * (g : ℂ)) • (-P) =
      (r * (g : ℂ)) • P := by rw [neg_mul, neg_smul_neg]
  simp only [hneg]
  change ((∑ mu : Fin 4, ∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
      ((structureConstant e a b d : ℂ) * (g : ℂ)) •
        (antighostDerivativeFamily G mu a * gaugeColorFamily G mu b)) +
      (g : ℂ) • colorPolynomialBracket e (ghostAntifieldFamily G) (ghostColorFamily G) d) +
    (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ mu : Fin 4,
      ((structureConstant e a b d : ℂ) * (g : ℂ)) •
        (gaugeColorFamily G mu b * gaugeAntifieldFamily G mu a)) +
    (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ mu : Fin 4,
      (Complex.I * (structureConstant e a b d : ℂ) * (g : ℂ)) •
        (-(gaugeColorFamily G mu b * auxiliaryAntifieldDerivativeFamily G mu a))) = _
  rw [hp, hA]
  have hb : (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ mu : Fin 4,
      (Complex.I * (structureConstant e a b d : ℂ) * (g : ℂ)) •
        (-(gaugeColorFamily G mu b * auxiliaryAntifieldDerivativeFamily G mu a))) =
      (-Complex.I) • ((-(g : ℂ)) • (∑ mu : Fin 4,
        colorPolynomialBracket e (gaugeColorFamily G mu) (auxiliaryAntifieldDerivativeFamily G mu) d)) := by
    rw [← hB]
    simp only [Finset.smul_sum, smul_smul, smul_neg]
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro b hb
    apply Finset.sum_congr rfl; intro mu hmu
    module
  rw [hb]
  unfold shiftedGaugeAntifieldFamily
  simp only [colorPolynomialBracket_sub_right, colorPolynomialBracket_add_right,
    colorPolynomialBracket_smul_right, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.smul_sum]
  module

/-- The free divergence of the same shifted antifield combination matches
all three actual free c† Euler terms, with their fixed B phase. -/
theorem shiftedGaugeAntifield_divergence (d : Fin G.dimension) :
    -(∑ mu : Fin 4, totalDerivative mu (shiftedGaugeAntifieldFamily G mu d)) =
      -(∑ mu : Fin 4, jet ⟨.inl (.antighost d), Pi.single mu 2⟩) -
      (∑ mu : Fin 4, jet ⟨.inr (.gauge mu d), Pi.single mu 1⟩) +
      Complex.I • (∑ mu : Fin 4, jet ⟨.inr (.auxiliary d), Pi.single mu 2⟩) := by
  have hd (mu : Fin 4) (X Y : JetAlgebra G) :
      totalDerivative mu (X - Y) = totalDerivative mu X - totalDerivative mu Y :=
    map_sub (totalDerivativeLinear mu) X Y
  unfold shiftedGaugeAntifieldFamily gaugeAntifieldFamily antighostDerivativeFamily
    auxiliaryAntifieldDerivativeFamily
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hd, totalDerivative_add,
    totalDerivative_smul, totalDerivative_jet, Jet.shift, zero_add, single_one_add_one,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]
  module

/-- Compact actual ghost-antifield equation: the covariant divergence of
Kμ=A†μ+∂μbar−i∂μB† plus the actual adjoint ghost-source term. This is a
proved equation of the SAME full master action, not a chosen BV image. -/
theorem master_characteristic_ghostAntifield_covariant {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (d : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inr (.ghost d)) =
      -(∑ mu : Fin 4, totalDerivative mu (shiftedGaugeAntifieldFamily G mu d)) +
      (-(g : ℂ)) • (∑ mu : Fin 4, colorPolynomialBracket e
        (gaugeColorFamily G mu) (shiftedGaugeAntifieldFamily G mu) d) +
      (g : ℂ) • colorPolynomialBracket e (ghostAntifieldFamily G) (ghostColorFamily G) d := by
  rw [master_characteristic_antighostSource, ghostAntifieldCorrection_compact,
    shiftedGaugeAntifield_divergence]
  abel

end YangMills.FullBV
