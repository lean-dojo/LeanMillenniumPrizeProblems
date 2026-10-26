import Problems.YangMills.FullBVAntighostAntifield

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem rightEuler_zeroOrder (field : ExternalLeg G) (P : JetAlgebra G)
    (h : ∀ alpha : Multiindex, alpha ≠ 0 → rightPartialJet ⟨field, alpha⟩ P = 0) :
    rightEuler field P = rightPartialJet ⟨field, 0⟩ P := by
  unfold rightEuler
  rw [finsum_eq_single _ 0 (by intro alpha ha; simp [h alpha ha])]
  simp [derivativeOrder_zero]

/-- Actual ghost Euler derivative of the physical ghost interaction word. -/
theorem rightEuler_ghost_physicalWord (mu : Fin 4) (a b c d : Fin G.dimension) :
    rightEuler (.inl (.ghost d))
      ((jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.gauge mu b), 0⟩) *
        ghostJet G c) =
      if c = d then jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
        jet ⟨.inl (.gauge mu b), 0⟩ else 0 := by
  classical
  have hp (alpha : Multiindex) : rightPartialJet ⟨.inl (.ghost d), alpha⟩
      ((jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.gauge mu b), 0⟩) *
        ghostJet G c) = if c = d ∧ alpha = 0 then
          jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.gauge mu b), 0⟩ else 0 := by
    by_cases hc : c = d <;> by_cases ha : alpha = 0
    all_goals simp_all [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
      LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet, parity_mul,
      parity_jet, Jet.mk.injEq, eq_comm]
  rw [rightEuler_zeroOrder _ _ (by intro alpha ha; simp [hp, ha]), hp]
  simp

/-- Actual right ghost variation of the gauge/B source cubic word. -/
theorem rightEuler_ghost_gaugeSourceWord (mu : Fin 4) (H : BasicField G)
    (hH : H.fermionic = false) (gamma : Multiindex) (b c d : Fin G.dimension) :
    rightEuler (.inl (.ghost d))
      ((jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c) * jet ⟨.inr H, gamma⟩) =
      if c = d then -(jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inr H, gamma⟩) else 0 := by
  classical
  have hp (alpha : Multiindex) : rightPartialJet ⟨.inl (.ghost d), alpha⟩
      ((jet ⟨.inl (.gauge mu b), 0⟩ * ghostJet G c) * jet ⟨.inr H, gamma⟩) =
      if c = d ∧ alpha = 0 then
        -(jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inr H, gamma⟩) else 0 := by
    by_cases hc : c = d <;> by_cases ha : alpha = 0
    all_goals simp_all [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
      LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet, parity_mul,
      parity_jet, Jet.mk.injEq, hH]
    all_goals first
      | exact mul_neg (jet ⟨.inl (.gauge mu b), 0⟩) (jet ⟨.inr H, gamma⟩)
      | have hcd : d ≠ c := Ne.symm hc
        simp [hcd]
  rw [rightEuler_zeroOrder _ _ (by intro alpha ha; simp [hp, ha]), hp]
  simp

/-- Both odd ghost positions of the actual ghost-antifield vertex, with
its canonical two crossing signs, before using color skew symmetry. -/
theorem rightEuler_ghost_ghostSourceWord (a b c d : Fin G.dimension) :
    rightEuler (.inl (.ghost d))
      ((ghostJet G b * ghostJet G c) * jet ⟨.inr (.ghost a), 0⟩) =
      (if b = d then -(ghostJet G c * jet ⟨.inr (.ghost a), 0⟩) else 0) +
      (if c = d then ghostJet G b * jet ⟨.inr (.ghost a), 0⟩ else 0) := by
  classical
  have hp (alpha : Multiindex) : rightPartialJet ⟨.inl (.ghost d), alpha⟩
      ((ghostJet G b * ghostJet G c) * jet ⟨.inr (.ghost a), 0⟩) =
      if alpha = 0 then
        ((if b = d then -(ghostJet G c * jet ⟨.inr (.ghost a), 0⟩) else 0) +
        (if c = d then ghostJet G b * jet ⟨.inr (.ghost a), 0⟩ else 0)) else 0 := by
    by_cases hb : b = d <;> by_cases hc : c = d <;> by_cases ha : alpha = 0
    all_goals simp_all [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
      LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet, parity_mul,
      parity_jet, Jet.mk.injEq, eq_comm, sub_eq_add_neg]
    all_goals exact neg_mul (ghostJet G c) (jet ⟨.inr (.ghost a), 0⟩)
  rw [rightEuler_zeroOrder _ _ (by intro alpha ha; simp [hp, ha]), hp]
  simp

theorem rightEuler_physicalAction_ghost {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (d : Fin G.dimension) :
    rightEuler (.inl (.ghost d)) (densityOfVertices g (physicalActionVertices e)) =
      rightEuler (.inl (.ghost d)) (densityOfVertices g (physicalGhostVertices e)) := by
  let liftVertex (m : InteractionMonomial G) : LocalVertex G :=
    { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
      legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) }
  have hd : physicalActionVertices e =
      ((cubicMonomials e ++ quarticMonomials e).map liftVertex) ++ physicalGhostVertices e := by
    simp only [physicalActionVertices, actionMonomials, physicalGhostVertices, List.map_append,
      liftVertex]
  have hz : rightEuler (.inl (.ghost d))
      (densityOfVertices g ((cubicMonomials e ++ quarticMonomials e).map liftVertex)) = 0 := by
    apply rightEuler_densityOfVertices_absent
    simp [cubicMonomials, quarticMonomials, List.bind_eq_flatMap, liftVertex]
    aesop
  rw [hd, densityOfVertices_append, rightEuler_add, hz, zero_add]

/-- Finite polynomial correction for the full ghost-antifield image. Every
coefficient and sign is retained from the same ordered physical/BV vertices;
there are no functional derivatives or freely chosen maps in this formula. -/
def ghostAntifieldCorrection {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (d : Fin G.dimension) : JetAlgebra G :=
  (∑ mu : Fin 4, ∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
    ((structureConstant e a b d : ℂ) * (g : ℂ)) •
      (jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.gauge mu b), 0⟩)) +
  (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
      ((if b = d then -(ghostJet G c * jet ⟨.inr (.ghost a), 0⟩) else 0) +
        (if c = d then ghostJet G b * jet ⟨.inr (.ghost a), 0⟩ else 0))) +
  (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ mu : Fin 4,
    (-(structureConstant e a b d : ℂ) * (g : ℂ)) •
      (-(jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inr (.gauge mu a), 0⟩))) +
  (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ mu : Fin 4,
    (Complex.I * (structureConstant e a b d : ℂ) * (g : ℂ)) •
      (-(jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩)))

theorem master_characteristic_antighostSource {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (d : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inr (.ghost d)) =
      -(∑ mu : Fin 4, jet ⟨.inl (.antighost d), Pi.single mu 2⟩) -
      (∑ mu : Fin 4, jet ⟨.inr (.gauge mu d), Pi.single mu 1⟩) +
      Complex.I • (∑ mu : Fin 4, jet ⟨.inr (.auxiliary d), Pi.single mu 2⟩) +
      ghostAntifieldCorrection e g d := by
  have hA (mu : Fin 4) (a b c : Fin G.dimension) :=
    rightEuler_ghost_gaugeSourceWord mu (.gauge mu a) (by rfl) 0 b c d
  have hB (mu : Fin 4) (a b c : Fin G.dimension) :=
    rightEuler_ghost_gaugeSourceWord mu (.auxiliary a) (by rfl) (Pi.single mu 1) b c d
  change rightEuler (.inl (.ghost d)) (masterActionDensity e g) = _
  conv_lhs => rw [masterActionDensity, rightEuler_add, interactionDensity,
    densityOfVertices_append, rightEuler_add, rightEuler_physicalAction_ghost,
    antifieldDensity_eq_nonlinearSource, physicalGhostDensity_expansion]
  change stCharacteristic (freeActionDensity G) (.inr (.ghost d)) + _ = _
  rw [free_characteristic_antighostSource]
  simp only [nonlinearSourceDensity, rightEuler_sum, rightEuler_add, rightEuler_smul,
    rightEuler_ghost_physicalWord, rightEuler_ghost_ghostSourceWord, hA, hB]
  simp [ghostAntifieldCorrection, Finset.sum_add_distrib, smul_add, smul_ite]
  all_goals abel

end YangMills.FullBV
