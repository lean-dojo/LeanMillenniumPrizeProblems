import Problems.YangMills.FullBVCurvatureEulerEquation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The fixed connection derivative built from the same actual gauge
coordinates, actual Lie bracket/color frame and coupling. -/
def covariantColorDerivative {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X : ColorPolynomial G) : ColorPolynomial G :=
  fun a => totalDerivative mu (X a) + (g : ℂ) •
    colorPolynomialBracket e (gaugeColorFamily G mu) X a

theorem covariantColorDerivative_add {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X Y : ColorPolynomial G) :
    covariantColorDerivative e g mu (X+Y) =
      covariantColorDerivative e g mu X + covariantColorDerivative e g mu Y := by
  funext a
  simp only [covariantColorDerivative, Pi.add_apply, totalDerivative_add,
    colorPolynomialBracket_add_right, smul_add]
  abel

theorem covariantColorDerivative_smul {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (r : ℂ) (X : ColorPolynomial G) :
    covariantColorDerivative e g mu (r • X) = r • covariantColorDerivative e g mu X := by
  funext a
  simp only [covariantColorDerivative, Pi.smul_apply, totalDerivative_smul,
    colorPolynomialBracket_smul_right, smul_add, smul_comm (g : ℂ) r]

theorem covariantColorDerivative_sub {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X Y : ColorPolynomial G) :
    covariantColorDerivative e g mu (X-Y) =
      covariantColorDerivative e g mu X - covariantColorDerivative e g mu Y := by
  have hd (P Q : JetAlgebra G) : totalDerivative mu (P-Q) =
      totalDerivative mu P - totalDerivative mu Q := map_sub (totalDerivativeLinear mu) P Q
  funext a
  simp only [covariantColorDerivative, Pi.sub_apply, hd,
    colorPolynomialBracket_sub_right, smul_sub]
  abel

/-- The commutator of two actual connection derivatives is the adjoint
actual curvature, on every full color-polynomial family (even or odd). -/
theorem covariantColorDerivative_commutator {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (X : ColorPolynomial G) (a : Fin G.dimension) :
    covariantColorDerivative e g mu (covariantColorDerivative e g nu X) a -
      covariantColorDerivative e g nu (covariantColorDerivative e g mu X) a =
      (g : ℂ) • colorPolynomialBracket e
        (fun b => nonabelianCurvatureJet e g mu nu b) X a := by
  have hj := colorPolynomialBracket_jacobi_central e
    (gaugeColorFamily G mu) (gaugeColorFamily G nu) X (gaugeColorFamily_central nu) a
  have hs := colorPolynomialBracket_skew_of_commute e
    (colorPolynomialBracket e (gaugeColorFamily G mu) X) (gaugeColorFamily G nu)
    (fun b c => (gaugeColorFamily_central nu c
      (colorPolynomialBracket e (gaugeColorFamily G mu) X b)).symm) a
  rw [hs] at hj
  have hF : (fun b => nonabelianCurvatureJet e g mu nu b) =
      (gaugeDerivativeFamily G mu nu - gaugeDerivativeFamily G nu mu) +
        (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G mu) (gaugeColorFamily G nu) := rfl
  unfold covariantColorDerivative
  rw [hF]
  simp only [totalDerivative_add, totalDerivative_smul, totalDerivative_colorPolynomialBracket,
    totalDerivative_gaugeColorFamily, colorPolynomialBracket_add_right,
    colorPolynomialBracket_smul_right, colorPolynomialBracket_add_left,
    colorPolynomialBracket_sub_left, colorPolynomialBracket_smul_left]
  have hi (sigma : Fin 4) :
      (fun b => totalDerivative sigma (X b) + (g : ℂ) •
        colorPolynomialBracket e (gaugeColorFamily G sigma) X b) =
      (fun b => totalDerivative sigma (X b)) +
        (g : ℂ) • colorPolynomialBracket e (gaugeColorFamily G sigma) X := rfl
  rw [hi nu, hi mu]
  simp only [colorPolynomialBracket_add_right, colorPolynomialBracket_smul_right]
  rw [totalDerivative_comm mu nu (X a)]
  rw [← hj]
  module

end YangMills.FullBV
