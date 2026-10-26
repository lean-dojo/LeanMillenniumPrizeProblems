import Problems.YangMills.FullBVLocalIntegration
import Problems.YangMills.EssentialCouplingHomogeneity

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.FieldParameter
variable {G : CompactSimpleGaugeGroup}

/-- Actual right variational derivatives, multiplied by an undifferentiated
coordinate on the right, equal the canonical left-coordinate expression.
The odd-generator involution and ordinary derivative parity are explicit. -/
theorem rightEuler_mul_zeroJet (field : ExternalLeg G) (P : JetAlgebra G) :
    rightEuler field P * jet ⟨field, 0⟩ = jet ⟨field, 0⟩ * leftEuler field P := by
  unfold rightEuler leftEuler
  rw [finsum_mul' _ _ (rightEulerSummands_finite field P),
    mul_finsum' _ _ (leftEulerSummands_finite field P)]
  apply finsum_congr
  intro alpha
  rw [smul_mul_assoc, mul_smul_comm]
  apply congrArg (fun R : JetAlgebra G => ((-1 : ℂ)^derivativeOrder alpha) • R)
  by_cases hp : field.parity = true
  · simpa only [rightPartialJet, hp, if_true, LinearMap.comp_apply,
      totalDerivatives_parity, jet, dif_pos] using!
      (oddJet_mul_polynomial ⟨⟨field, 0⟩, hp⟩
        (totalDerivatives alpha (leftPartialJet ⟨field, alpha⟩ P))).symm
  · simpa only [rightPartialJet, hp, if_false, jet, dif_neg] using!
      (evenJet_commute ⟨⟨field, 0⟩, by cases h : field.parity <;> simp_all⟩
        (totalDerivatives alpha (leftPartialJet ⟨field, alpha⟩ P))).symm

def canonicalEulerDensity (weights : BasicScales) (S : JetAlgebra G) : JetAlgebra G :=
  ∑ K : BasicField G, (basicScale weights K : ℂ) •
    (rightEuler (.inl K) S * jet ⟨.inl K, 0⟩ - rightEuler (.inr K) S * jet ⟨.inr K, 0⟩)

/-- Literal canonical pair computation, including odd basic fields and
opposite-parity antifields. No master equation or evenness premise is used. -/
theorem localST_canonicalPair (S : JetAlgebra G) (K : BasicField G) :
    localST S (jet ⟨.inl K, 0⟩ * jet ⟨.inr K, 0⟩) =
      rightEuler (.inl K) S * jet ⟨.inl K, 0⟩ - rightEuler (.inr K) S * jet ⟨.inr K, 0⟩ := by
  rw [localST_mul_jet, localST_jet]
  simp only [prolongedST, totalDerivatives_zero, stCharacteristic]
  cases K <;> simp [ExternalLeg.parity, BasicField.fermionic, parity_jet, sub_eq_add_neg, add_comm]
  all_goals rw [← complex_neg_one_smul, smul_mul_assoc, complex_neg_one_smul]

theorem localST_rescalingGenerator (S : JetAlgebra G) (weights : BasicScales) :
    localST S (rescalingGenerator (G := G) weights) = canonicalEulerDensity weights S := by
  unfold rescalingGenerator canonicalEulerDensity
  rw [localST_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [localST_smul, localST_canonicalPair]

/-- Canonical field/source Euler variation is an actual same-S exact
integrated functional, using the explicit finite basic-antifield generator. -/
theorem canonicalEuler_exact (S : JetAlgebra G) (weights : BasicScales) :
    localClass (canonicalEulerDensity weights S) =
      localSTFunctional S (localClass (rescalingGenerator weights)) := by
  rw [localSTFunctional_localClass, localST_rescalingGenerator]


def leftCanonicalEulerDensity (weights : BasicScales) (S : JetAlgebra G) : JetAlgebra G :=
  ∑ K : BasicField G, (basicScale weights K : ℂ) •
    (jet ⟨.inl K, 0⟩ * leftEuler (.inl K) S - jet ⟨.inr K, 0⟩ * leftEuler (.inr K) S)

theorem canonicalEuler_eq_left (S : JetAlgebra G) (weights : BasicScales) :
    canonicalEulerDensity weights S = leftCanonicalEulerDensity weights S := by
  unfold canonicalEulerDensity leftCanonicalEulerDensity
  simp_rw [rightEuler_mul_zeroJet]

theorem leftCanonicalEuler_exact (S : JetAlgebra G) (weights : BasicScales) :
    localClass (leftCanonicalEulerDensity weights S) =
      localSTFunctional S (localClass (rescalingGenerator weights)) := by
  rw [← canonicalEuler_eq_left, canonicalEuler_exact]

end YangMills.FullBV
