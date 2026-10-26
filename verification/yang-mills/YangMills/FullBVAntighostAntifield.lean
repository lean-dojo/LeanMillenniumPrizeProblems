import YangMills.FullBVActualAuxiliaryNilpotency
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem rightEuler_ghostInteraction_word (mu : Fin 4) (a b c d : Fin G.dimension) :
    rightEuler (.inl (.antighost a))
      ((jet ⟨.inl (.antighost b), Pi.single mu 1⟩ * jet ⟨.inl (.gauge mu c), 0⟩) *
        ghostJet G d) =
      if b = a then totalDerivative mu
        (jet ⟨.inl (.gauge mu c), 0⟩ * ghostJet G d) else 0 := by
  classical
  have hp (alpha : Multiindex) :
      rightPartialJet ⟨.inl (.antighost a), alpha⟩
        ((jet ⟨.inl (.antighost b), Pi.single mu 1⟩ * jet ⟨.inl (.gauge mu c), 0⟩) *
          ghostJet G d) =
        if b = a ∧ alpha = Pi.single mu 1 then
          -(jet ⟨.inl (.gauge mu c), 0⟩ * ghostJet G d) else 0 := by
    by_cases hb : b = a
    · subst b
      by_cases ha : alpha = Pi.single mu 1
      · subst alpha
        simp [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
          LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet, parity_mul,
          parity_jet, Jet.mk.injEq, mul_assoc]
        exact mul_neg (jet ⟨.inl (.gauge mu c), 0⟩) (ghostJet G d)
      · have ha' : Pi.single mu 1 ≠ alpha := Ne.symm ha
        simp [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
          LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet,
          Jet.mk.injEq, ha, ha']
    · have hb' : a ≠ b := Ne.symm hb
      simp [rightPartialJet, ExternalLeg.parity, BasicField.fermionic,
        LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet,
        Jet.mk.injEq, hb, hb']
  unfold rightEuler
  simp only [hp]
  rw [finsum_eq_single _ (Pi.single mu 1) (by intro alpha ha; simp [ha])]
  by_cases hb : b = a <;>
    simp [hb, derivativeOrder_single, totalDerivatives_neg, totalDerivatives_single_one]

def physicalGhostVertices {B : InvariantForm G} (e : ColorFrame B) : List (LocalVertex G) :=
  (ghostMonomials e).map (fun m =>
    { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
      legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) })

theorem physicalGhostDensity_expansion {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (physicalGhostVertices e) =
      ∑ mu : Fin 4, ∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a b c : ℂ) * (g : ℂ)) •
          ((jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
            jet ⟨.inl (.gauge mu b), 0⟩) * ghostJet G c) := by
  unfold densityOfVertices physicalGhostVertices ghostMonomials
  simp only [List.bind_eq_flatMap, List.map_map, Function.comp_def, List.map_flatMap,
    sum_list_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    List.map_cons, List.map_nil, densityOfVertex_triple, vertexJet_nil, vertexJet_single]

theorem rightEuler_physicalAction_antighost {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) :
    rightEuler (.inl (.antighost a)) (densityOfVertices g (physicalActionVertices e)) =
      rightEuler (.inl (.antighost a)) (densityOfVertices g (physicalGhostVertices e)) := by
  let liftVertex (m : InteractionMonomial G) : LocalVertex G :=
    { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
      legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) }
  have hd : physicalActionVertices e =
      ((cubicMonomials e ++ quarticMonomials e).map liftVertex) ++ physicalGhostVertices e := by
    simp only [physicalActionVertices, actionMonomials, physicalGhostVertices, List.map_append,
      liftVertex]
  have hz : rightEuler (.inl (.antighost a))
      (densityOfVertices g ((cubicMonomials e ++ quarticMonomials e).map liftVertex)) = 0 := by
    apply rightEuler_densityOfVertices_absent
    simp [cubicMonomials, quarticMonomials, List.bind_eq_flatMap, liftVertex]
    aesop
  rw [hd, densityOfVertices_append, rightEuler_add, hz, zero_add]

theorem rightEuler_antifieldAction_antighost {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) :
    rightEuler (.inl (.antighost a)) (densityOfVertices g (antifieldActionVertices e)) = 0 := by
  apply rightEuler_densityOfVertices_absent
  simp [antifieldActionVertices, List.bind_eq_flatMap]
  aesop

/-- The full antighost-antifield characteristic is exactly the nonlinear
covariant ghost divergence, extracted from the actual physical ghost action. -/
theorem master_characteristic_antiantighost_divergence {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inr (.antighost a)) =
      ∑ mu : Fin 4, totalDerivative mu
        (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) := by
  change rightEuler (.inl (.antighost a)) (masterActionDensity e g) = _
  conv_lhs => rw [masterActionDensity, rightEuler_add, interactionDensity, densityOfVertices_append,
    rightEuler_add, rightEuler_physicalAction_antighost, rightEuler_antifieldAction_antighost,
    add_zero]
  change stCharacteristic (freeActionDensity G) (.inr (.antighost a)) + _ = _
  rw [free_characteristic_antiantighost, physicalGhostDensity_expansion]
  simp only [rightEuler_sum, rightEuler_smul, rightEuler_ghostInteraction_word]
  simp [master_characteristic_gauge, totalDerivative_add, totalDerivative_sum,
    totalDerivative_smul, totalDerivative_jet, Jet.shift, single_one_add_one,
    Finset.sum_add_distrib]

/-- The full barc-antifield square vanishes by the SAME actual gauge square
and proved pointwise evolutionary commutation, including its ghost vertex. -/
theorem classicalLocalST_square_antiantighost {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inr (.antighost a), 0⟩)) = 0 := by
  simp only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero,
    master_characteristic_antiantighost_divergence, localST_sum,
    localST_totalDerivative_gaugeCharacteristic]
  have hA (mu : Fin 4) : localST (masterActionDensity e g)
      (stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) = 0 := by
    simpa only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero] using
      classicalLocalST_square_gauge e g mu a
  simp only [hA, totalDerivative_zero, Finset.sum_const_zero]

theorem classicalLocalST_square_antiauxiliary {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (a : Fin G.dimension) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inr (.auxiliary a), 0⟩)) = 0 := by
  simp only [classicalLocalSTDensity, localST_jet, totalDerivatives_zero,
    master_characteristic_antiauxiliary, sub_eq_add_neg, localST_add, localST_neg,
    localST_smul, master_characteristic_auxiliary_divergence,
    master_characteristic_antiantighost_divergence, totalDerivatives_single_one]
  abel

/-- All four basic coordinates: actual interacting nilpotency, proved. -/
theorem classicalLocalST_square_basic {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (K : BasicField G) :
    classicalLocalSTDensity e g
      (classicalLocalSTDensity e g (jet ⟨.inl K, 0⟩)) = 0 := by
  cases K with
  | gauge mu a => exact classicalLocalST_square_gauge e g mu a
  | ghost a => exact classicalLocalST_square_ghost e g a
  | antighost a => exact classicalLocalST_square_antighost e g a
  | auxiliary a => exact classicalLocalST_square_auxiliary e g a

end YangMills.FullBV
