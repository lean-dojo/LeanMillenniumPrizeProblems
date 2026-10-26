import YangMills.FullBVCompactShiftedAntifield
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Explicit algebraic part of the actual gauge-coordinate partial of F.
It is a fixed finite color contraction of actual gauge jets. -/
def curvatureGaugeZeroPartial {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu rho : Fin 4) (a d : Fin G.dimension) : JetAlgebra G :=
  (g : ℂ) • ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    (structureConstant e a b c : ℂ) •
      ((if mu = rho ∧ b = d then gaugePotentialJet G nu c else 0) +
        (if nu = rho ∧ c = d then gaugePotentialJet G mu b else 0))

theorem leftPartial_gluonBracket_gauge {B : InvariantForm G} (e : ColorFrame B)
    (mu nu rho : Fin 4) (a d : Fin G.dimension) (alpha : Multiindex) :
    leftPartialJet ⟨.inl (.gauge rho d),alpha⟩ (gluonBracketJet e mu nu a) =
      if alpha = 0 then
        ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
          (structureConstant e a b c : ℂ) •
            ((if mu = rho ∧ b = d then gaugePotentialJet G nu c else 0) +
              (if nu = rho ∧ c = d then gaugePotentialJet G mu b else 0)) else 0 := by
  by_cases ha : alpha = 0
  · subst alpha
    simp only [gluonBracketJet, map_sum, map_smul, if_true]
    apply Finset.sum_congr rfl; intro b hb
    apply Finset.sum_congr rfl; intro c hc
    congr 1
    unfold gaugePotentialJet
    simp only [leftPartialJet_mul, leftPartialJet_jet, ExternalLeg.parity,
      BasicField.fermionic, Bool.false_eq_true, if_false, Jet.mk.injEq,
      Sum.inl.injEq, BasicField.gauge.injEq, and_true]
    by_cases hm : mu = rho <;> by_cases hn : nu = rho <;>
      by_cases hb : b = d <;> by_cases hc : c = d
    all_goals simp_all [eq_comm]
  · have ha' : (0 : Multiindex) ≠ alpha := Ne.symm ha
    simp only [gluonBracketJet, map_sum, map_smul, ha, if_false]
    apply Finset.sum_eq_zero; intro b hb
    apply Finset.sum_eq_zero; intro c hc
    simp [gaugePotentialJet, leftPartialJet_mul, leftPartialJet_jet,
      ExternalLeg.parity, BasicField.fermionic, Jet.mk.injEq, ha, ha']

/-- Every actual curvature gauge partial is supported at order zero or one
of its two fixed derivative labels; no jet support is supplied by a witness. -/
theorem leftPartial_curvature_gauge {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu rho : Fin 4) (a d : Fin G.dimension) (alpha : Multiindex) :
    leftPartialJet ⟨.inl (.gauge rho d),alpha⟩ (nonabelianCurvatureJet e g mu nu a) =
      (if nu = rho ∧ a = d ∧ alpha = Pi.single mu 1 then 1 else 0) -
      (if mu = rho ∧ a = d ∧ alpha = Pi.single nu 1 then 1 else 0) +
      (if alpha = 0 then curvatureGaugeZeroPartial e g mu nu rho a d else 0) := by
  unfold nonabelianCurvatureJet abelianCurvatureJet gaugeFirstJet
  simp only [map_add, map_sub, map_smul, leftPartial_gluonBracket_gauge,
    leftPartialJet_jet, Jet.mk.injEq, Sum.inl.injEq, BasicField.gauge.injEq]
  congr 1
  · congr 1
    · congr 1
      apply propext
      constructor
      · rintro ⟨⟨hr,hd⟩,ha⟩; exact ⟨hr.symm,hd.symm,ha⟩
      · rintro ⟨hr,hd,ha⟩; exact ⟨⟨hr.symm,hd.symm⟩,ha⟩
    · congr 1
      apply propext
      constructor
      · rintro ⟨⟨hr,hd⟩,ha⟩; exact ⟨hr.symm,hd.symm,ha⟩
      · rintro ⟨hr,hd,ha⟩; exact ⟨⟨hr.symm,hd.symm⟩,ha⟩
  · by_cases ha : alpha = 0 <;> simp only [ha, if_true, if_false, smul_zero]
    rfl

/-- Antisymmetry is proved for the same actual nonabelian curvature. -/
theorem nonabelianCurvature_skew {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) :
    nonabelianCurvatureJet e g mu nu a = -(nonabelianCurvatureJet e g nu mu a) := by
  have h := colorPolynomialBracket_skew_of_commute e
    (gaugeColorFamily G mu) (gaugeColorFamily G nu)
    (fun b c => gaugeColorFamily_central mu b (gaugeColorFamily G nu c)) a
  change gluonBracketJet e mu nu a = -gluonBracketJet e nu mu a at h
  unfold nonabelianCurvatureJet abelianCurvatureJet
  rw [h]
  module

end YangMills.FullBV
