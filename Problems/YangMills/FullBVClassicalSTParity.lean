import Problems.YangMills.FullBVPartialParity
import Problems.YangMills.FullBVTotalDerivativeParity
import Problems.YangMills.FullBVEvolutionaryDerivation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem rightPartialJet_parity (j : Jet G) (P : JetAlgebra G) :
    rightPartialJet j (parity P) =
      (if j.field.parity then (-1 : ℂ) else 1) • parity (rightPartialJet j P) := by
  by_cases hj : j.field.parity = true
  · simp only [rightPartialJet, hj, if_true, LinearMap.comp_apply, leftPartialJet_parity,
      map_smul, parity_parity]
  · simp only [rightPartialJet, hj, Bool.false_eq_true, if_false, leftPartialJet_parity]

theorem rightEuler_even_parity (S : JetAlgebra G) (hS : parity S = S)
    (field : ExternalLeg G) :
    parity (rightEuler field S) =
      (if field.parity then (-1 : ℂ) else 1) • rightEuler field S := by
  have hp (j : Jet G) : parity (rightPartialJet j S) =
      (if j.field.parity then (-1 : ℂ) else 1) • rightPartialJet j S := by
    have h := rightPartialJet_parity j S
    rw [hS] at h
    cases hj : j.field.parity <;>
      simp only [hj, Bool.false_eq_true, if_false, if_true, one_smul, complex_neg_one_smul] at h ⊢
    · exact h.symm
    · simpa only [neg_neg] using (congrArg (fun X : JetAlgebra G => -X) h).symm
  unfold rightEuler
  have hm := parity.toAddMonoidHom.map_finsum (rightEulerSummands_finite field S)
  change parity (∑ᶠ alpha : Multiindex, ((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ S)) = _ at hm
  rw [hm]
  change (∑ᶠ alpha : Multiindex, parity (((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ S))) = _
  simp only [map_smul, ← totalDerivatives_parity, hp, totalDerivatives_smul,
    smul_comm ((-1 : ℂ) ^ _)]
  exact (smul_finsum' (if field.parity then (-1 : ℂ) else 1)
    (rightEulerSummands_finite field S)).symm

/-- The actual Hamiltonian characteristics of every even action have the
opposite parity to their coordinates, including all antifields. -/
theorem stCharacteristic_even_parity (S : JetAlgebra G) (hS : parity S = S)
    (field : ExternalLeg G) :
    parity (stCharacteristic S field) =
      (if field.parity then (1 : ℂ) else -1) • stCharacteristic S field := by
  cases field with
  | inl K =>
    cases hK : K.fermionic <;>
      simp [stCharacteristic, map_neg, rightEuler_even_parity S hS,
        ExternalLeg.parity, hK, complex_neg_one_smul]
  | inr K =>
    cases hK : K.fermionic <;>
      simp [stCharacteristic, rightEuler_even_parity S hS,
        ExternalLeg.parity, hK, complex_neg_one_smul]

theorem prolongedST_even_parity (S : JetAlgebra G) (hS : parity S = S) (j : Jet G) :
    parity (prolongedST S j) =
      (if j.field.parity then (1 : ℂ) else -1) • prolongedST S j := by
  simp only [prolongedST, ← totalDerivatives_parity, stCharacteristic_even_parity S hS,
    totalDerivatives_smul]

/-- Actual pointwise ST reverses parity on the full polynomial/exterior
algebra. This follows from its fixed coordinate formula, not an oddness axiom. -/
theorem localST_even_parity (S : JetAlgebra G) (hS : parity S = S) (P : JetAlgebra G) :
    localST S (parity P) = -(parity (localST S P)) := by
  have hn (X Y : JetAlgebra G) : (-X) * Y = -(X * Y) := neg_mul X Y
  have hm (X Y : JetAlgebra G) : X * (-Y) = -(X * Y) := mul_neg X Y
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp only [parity_one, localST_one, map_zero, neg_zero]
  | add P Q hP hQ => simp only [map_add, localST_add, hP, hQ, neg_add]
  | smul c P hP => simp only [map_smul, localST_smul, hP, smul_neg]
  | mul P j hP =>
    cases hj : j.field.parity <;>
      simp only [parity_mul, parity_jet, hj, Bool.false_eq_true, if_false, if_true,
        mul_neg, localST_neg, localST_mul_jet, map_add, map_neg, hP,
        prolongedST_even_parity S hS, hj, Bool.false_eq_true, if_false, if_true,
        complex_neg_one_smul, one_smul, parity_parity, neg_mul, neg_neg, neg_add]
    all_goals
      simp only [hn, hm, localST_neg, localST_mul_jet, hP, hj, if_false, if_true,
        Bool.false_eq_true, parity_parity, neg_neg, neg_add]

theorem classicalLocalST_parity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) :
    classicalLocalSTDensity e g (parity P) = -(parity (classicalLocalSTDensity e g P)) :=
  localST_even_parity _ (parity_masterActionDensity e g) P

end YangMills.FullBV
