import Problems.YangMills.FullBVColorEvolution

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def covariantColorDerivativeLinear {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) : ColorPolynomial G →ₗ[ℂ] ColorPolynomial G where
  toFun := covariantColorDerivative e g mu
  map_add' := covariantColorDerivative_add e g mu
  map_smul' := covariantColorDerivative_smul e g mu

theorem covariantColorDerivative_neg {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) (X : ColorPolynomial G) :
    covariantColorDerivative e g mu (-X) = -covariantColorDerivative e g mu X :=
  map_neg (covariantColorDerivativeLinear e g mu) X

theorem covariantColorDerivative_sum {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu : Fin 4) {I : Type*} (s : Finset I) (X : I → ColorPolynomial G) :
    covariantColorDerivative e g mu (∑ i ∈ s, X i) =
      ∑ i ∈ s, covariantColorDerivative e g mu (X i) :=
  map_sum (covariantColorDerivativeLinear e g mu) X s

def curvatureColorFamily {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) : ColorPolynomial G := fun a => nonabelianCurvatureJet e g mu nu a

def curvatureEulerFamily {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) : ColorPolynomial G :=
  fun d => rightEuler (.inl (.gauge rho d)) (gluonCurvatureDensity e g)

theorem curvatureColorFamily_skew {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) : curvatureColorFamily e g mu nu = -curvatureColorFamily e g nu mu := by
  funext a; exact nonabelianCurvature_skew e g mu nu a

theorem curvatureEulerFamily_eq {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (rho : Fin 4) :
    curvatureEulerFamily e g rho =
      -(∑ mu : Fin 4, covariantColorDerivative e g mu (curvatureColorFamily e g mu rho)) := by
  funext d
  simpa only [curvatureEulerFamily, Pi.neg_apply, Finset.sum_apply, covariantColorDerivative,
    curvatureColorFamily] using! rightEuler_curvature_gauge e g rho d

private theorem colorFamily_eq_neg_implies_zero (X : ColorPolynomial G) (h : X = -X) : X = 0 := by
  have ht : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    calc
      X + X = -X + X := congrArg (fun Y : ColorPolynomial G => Y+X) h
      _ = 0 := neg_add_cancel X
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

theorem colorPolynomialBracket_self_even {B : InvariantForm G} (e : ColorFrame B)
    (X : ColorPolynomial G) (hX : ∀ a, parity (X a) = X a) :
    colorPolynomialBracket e X X = 0 := by
  have h : colorPolynomialBracket e X X = -colorPolynomialBracket e X X := by
    funext a
    exact colorPolynomialBracket_skew_of_commute e X X
      (fun b c => evenPolynomial_commute (X b) (X c) (hX b)) a
  exact colorFamily_eq_neg_implies_zero _ h

theorem colorPolynomialBracket_neg_right {B : InvariantForm G} (e : ColorFrame B)
    (X Y : ColorPolynomial G) :
    colorPolynomialBracket e X (-Y) = -colorPolynomialBracket e X Y := by
  have hn (P Q : JetAlgebra G) : P*(-Q) = -(P*Q) := mul_neg P Q
  funext a
  simp only [colorPolynomialBracket, Pi.neg_apply, hn, smul_neg, Finset.sum_neg_distrib]

/-- Antisymmetry, the actual connection commutator and even [F,F]=0 give
vanishing covariant double divergence. This is an actual same-action
Noether identity, not an imposed field equation. -/
theorem curvature_covariant_double_divergence {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    (∑ mu : Fin 4, ∑ nu : Fin 4, covariantColorDerivative e g mu
      (covariantColorDerivative e g nu (curvatureColorFamily e g nu mu))) = 0 := by
  have hc (mu nu : Fin 4) :
      covariantColorDerivative e g mu
        (covariantColorDerivative e g nu (curvatureColorFamily e g nu mu)) =
      covariantColorDerivative e g nu
        (covariantColorDerivative e g mu (curvatureColorFamily e g nu mu)) := by
    funext a
    have h := covariantColorDerivative_commutator e g mu nu (curvatureColorFamily e g nu mu) a
    have hz : colorPolynomialBracket e (curvatureColorFamily e g mu nu)
        (curvatureColorFamily e g nu mu) = 0 := by
      rw [curvatureColorFamily_skew e g nu mu, colorPolynomialBracket_neg_right,
        colorPolynomialBracket_self_even e (curvatureColorFamily e g mu nu)
          (parity_nonabelianCurvature e g mu nu), neg_zero]
    change _ - _ = (g : ℂ) • colorPolynomialBracket e (curvatureColorFamily e g mu nu)
      (curvatureColorFamily e g nu mu) a at h
    rw [hz] at h
    simpa only [Pi.zero_apply, smul_zero, sub_eq_zero] using! h
  apply colorFamily_eq_neg_implies_zero
  calc
    _ = ∑ mu : Fin 4, ∑ nu : Fin 4, covariantColorDerivative e g nu
      (covariantColorDerivative e g mu (curvatureColorFamily e g nu mu)) := by
      apply Finset.sum_congr rfl; intro mu hmu
      apply Finset.sum_congr rfl; intro nu hnu
      exact hc mu nu
    _ = ∑ nu : Fin 4, ∑ mu : Fin 4, covariantColorDerivative e g nu
      (covariantColorDerivative e g mu (curvatureColorFamily e g nu mu)) := Finset.sum_comm
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro mu hmu
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro nu hnu
      rw [curvatureColorFamily_skew e g mu nu, covariantColorDerivative_neg,
        covariantColorDerivative_neg]

/-- Covariant conservation of the actual curvature Euler gradient. -/
theorem curvatureEuler_Noether {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    (∑ rho : Fin 4, covariantColorDerivative e g rho (curvatureEulerFamily e g rho)) = 0 := by
  simp only [curvatureEulerFamily_eq, covariantColorDerivative_neg,
    covariantColorDerivative_sum, Finset.sum_neg_distrib]
  rw [curvature_covariant_double_divergence, neg_zero]

end YangMills.FullBV
