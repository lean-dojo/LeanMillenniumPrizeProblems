import Problems.YangMills.FullBVCurvatureGaugePartials

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

private theorem finsum_three_channels {A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (u v w : A) (U V W : M) :
    (∑ᶠ a : A, ((if a = u then U else 0) + (if a = v then V else 0) +
      (if a = w then W else 0))) = U + V + W := by
  classical
  let S : Finset A := {u,v,w}
  have hs : Function.support (fun a : A => ((if a = u then U else 0) +
      (if a = v then V else 0) + (if a = w then W else 0))) ⊆ (S : Set A) := by
    intro a ha
    by_contra hn
    have hne : a ≠ u ∧ a ≠ v ∧ a ≠ w := by simpa [S] using hn
    exact ha (by simp [hne.1,hne.2.1,hne.2.2])
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq, S]

/-- A proved finite three-channel Euler evaluation, including coincident
jet labels. No disjointness or supplied jet support is assumed. -/
theorem rightEuler_three_channels (field : ExternalLeg G) (P : JetAlgebra G)
    (u v w : Multiindex) (U V W : JetAlgebra G)
    (hp : ∀ alpha, rightPartialJet ⟨field,alpha⟩ P =
      (if alpha = u then U else 0) + (if alpha = v then V else 0) +
      (if alpha = w then W else 0)) :
    rightEuler field P =
      ((-1 : ℂ)^derivativeOrder u) • totalDerivatives u U +
      ((-1 : ℂ)^derivativeOrder v) • totalDerivatives v V +
      ((-1 : ℂ)^derivativeOrder w) • totalDerivatives w W := by
  have hd (alpha beta : Multiindex) (X : JetAlgebra G) :
      ((-1 : ℂ)^derivativeOrder alpha) •
        totalDerivatives alpha (if alpha = beta then X else 0) =
      if alpha = beta then ((-1 : ℂ)^derivativeOrder beta) • totalDerivatives beta X else 0 := by
    by_cases h : alpha = beta
    · subst alpha; simp
    · simp only [h, if_false, totalDerivatives_zeroInput, smul_zero]
  simp only [rightEuler, hp, totalDerivatives_add, smul_add, hd]
  exact finsum_three_channels _ _ _ _ _ _

theorem leftPartial_evenSquare (j : Jet G) (hj : j.field.parity = false)
    (P : JetAlgebra G) (hP : parity P = P) :
    leftPartialJet j (P*P) = (2 : ℂ) • (P * leftPartialJet j P) := by
  rw [leftPartialJet_mul]
  simp only [hj, Bool.false_eq_true, if_false]
  rw [← evenPolynomial_commute P (leftPartialJet j P) hP]
  module

private theorem partial_three_channel_algebra (F Z : JetAlgebra G)
    (C D U V W : Prop) [Decidable C] [Decidable D] [Decidable U] [Decidable V] [Decidable W] :
    (2 : ℂ) • (F * ((if C ∧ U then 1 else 0) - (if D ∧ V then 1 else 0) +
      (if W then Z else 0))) =
      (if U then (if C then (2 : ℂ) • F else 0) else 0) +
      (if V then (if D then (-2 : ℂ) • F else 0) else 0) +
      (if W then (2 : ℂ) • (F * Z) else 0) := by
  have hm (X Y : JetAlgebra G) : X * (-Y) = -(X * Y) := mul_neg X Y
  by_cases hc : C <;> by_cases hd : D <;> by_cases hu : U <;>
    by_cases hv : V <;> by_cases hw : W
  all_goals simp only [hc,hd,hu,hv,hw,and_true,and_false,if_true,if_false,
    sub_zero,zero_sub,add_zero,zero_add,mul_add,mul_sub,mul_one,mul_zero,
    smul_add,smul_sub,smul_zero,hm]
  all_goals module

/-- The three non-free gauge-partial channels of the actual curvature
square. All factors and the zero-order interaction derivative are fixed. -/
theorem rightPartial_curvatureSquare_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu rho : Fin 4) (a d : Fin G.dimension) (alpha : Multiindex) :
    rightPartialJet ⟨.inl (.gauge rho d),alpha⟩
      (nonabelianCurvatureJet e g mu nu a * nonabelianCurvatureJet e g mu nu a) =
      (if alpha = Pi.single mu 1 then
        (if nu = rho ∧ a = d then (2 : ℂ) • nonabelianCurvatureJet e g mu nu a else 0) else 0) +
      (if alpha = Pi.single nu 1 then
        (if mu = rho ∧ a = d then (-2 : ℂ) • nonabelianCurvatureJet e g mu nu a else 0) else 0) +
      (if alpha = 0 then (2 : ℂ) • (nonabelianCurvatureJet e g mu nu a *
        curvatureGaugeZeroPartial e g mu nu rho a d) else 0) := by
  change leftPartialJet ⟨.inl (.gauge rho d),alpha⟩ _ = _
  rw [leftPartial_evenSquare _ (by rfl) _ (parity_nonabelianCurvature e g mu nu a),
    leftPartial_curvature_gauge]
  simpa only [and_assoc] using partial_three_channel_algebra
    (nonabelianCurvatureJet e g mu nu a) (curvatureGaugeZeroPartial e g mu nu rho a d)
    (nu = rho ∧ a = d) (mu = rho ∧ a = d)
    (alpha = Pi.single mu 1) (alpha = Pi.single nu 1) (alpha = 0)

/-- Exact Euler derivative of a single curvature-square component, with
all three actual derivative channels and their normalization factors. -/
theorem rightEuler_curvatureSquare_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu rho : Fin 4) (a d : Fin G.dimension) :
    rightEuler (.inl (.gauge rho d))
      (nonabelianCurvatureJet e g mu nu a * nonabelianCurvatureJet e g mu nu a) =
      (-2 : ℂ) • (if nu = rho ∧ a = d then
        totalDerivative mu (nonabelianCurvatureJet e g mu nu a) else 0) +
      (2 : ℂ) • (if mu = rho ∧ a = d then
        totalDerivative nu (nonabelianCurvatureJet e g mu nu a) else 0) +
      (2 : ℂ) • (nonabelianCurvatureJet e g mu nu a *
        curvatureGaugeZeroPartial e g mu nu rho a d) := by
  rw [rightEuler_three_channels _ _ (Pi.single mu 1) (Pi.single nu 1) 0 _ _ _
    (rightPartial_curvatureSquare_gauge e g mu nu rho a d)]
  simp only [derivativeOrder_single, derivativeOrder_zero, pow_one, pow_zero,
    totalDerivatives_single_one, totalDerivatives_zero, one_smul]
  have hdif (sigma : Fin 4) (p : Prop) [Decidable p] (r : ℂ) (P : JetAlgebra G) :
      totalDerivative sigma (if p then r • P else 0) =
        if p then r • totalDerivative sigma P else 0 := by
    by_cases hp : p <;> simp only [hp,if_true,if_false,totalDerivative_smul,totalDerivative_zero]
  simp only [hdif, smul_ite, smul_zero, smul_smul]
  have hn (X : JetAlgebra G) : -((2 : ℂ) • X) = (-2 : ℂ) • X :=
    (neg_smul (2 : ℂ) X).symm
  norm_num [hn]

end YangMills.FullBV
