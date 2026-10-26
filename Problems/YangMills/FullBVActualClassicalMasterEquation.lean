import Problems.YangMills.FullBVActualMasterClassReduction
import Problems.YangMills.FullBVSelfBracketSplit
import Problems.YangMills.FullBVBracketDescent

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual full shifted-B Yang--Mills master action satisfies the
classical BV master equation. This is derived from the same fixed vertices,
actual G Jacobi/invariant metric, actual basic BRST nilpotency, physical
action invariance and explicit source-current identity. No CME or full
antifield-nilpotency hypothesis is supplied. -/
theorem masterAction_classicalMasterEquation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    localClass (densityBracket (masterActionDensity e g) (masterActionDensity e g)) = 0 := by
  let S := masterActionDensity e g
  let Q : JetAlgebra G := ∑ K : BasicField G,
    stCharacteristic S (.inl K) * leftEuler (.inl K) S
  have hS : parity S = S := parity_masterActionDensity e g
  have hr : localClass (localST S S) = localClass Q := by
    have h := classicalLocalST_master_class_basicEuler e g
    change localClass (localST S S) = localClass (∑ K : BasicField G,
      (if K.fermionic then (-1 : ℂ) else 1) •
        (stCharacteristic S (.inl K) * rightEuler (.inl K) S)) at h
    simp only [basicSourceVariation_even S hS] at h
    exact h
  have hb : localClass (localST S S) = localClass ((2 : ℂ) • Q) := by
    rw [localClass_localST_eq_densityBracket, densityBracket_self_split S hS]
  have he : localClass Q = (2 : ℂ) • localClass Q := by
    calc
      _ = localClass (localST S S) := hr.symm
      _ = localClass ((2 : ℂ) • Q) := hb
      _ = _ := map_smul (divergences G).mkQ (2 : ℂ) Q
  have hz : localClass Q = 0 := by
    rw [two_smul] at he
    have hc : localClass Q + 0 = localClass Q + localClass Q := by
      simpa only [add_zero] using he
    exact (add_left_cancel hc).symm
  change localClass (densityBracket S S) = 0
  rw [densityBracket_self_split S hS]
  change (divergences G).mkQ ((2 : ℂ) • Q) = 0
  rw [map_smul]
  change (2 : ℂ) • localClass Q = 0
  rw [hz, smul_zero]

/-- The fixed, proved representative-independent functional BV bracket
vanishes on the actual same-source Yang--Mills master functional. -/
theorem masterAction_functionalMasterEquation {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    functionalBracket (masterAction e g) (masterAction e g) = 0 :=
  masterAction_classicalMasterEquation e g

/-- The actual evolutionary ST image of the master density has zero
integrated class; the point insertion algebra itself is retained. -/
theorem masterAction_localST_self {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    localClass (classicalLocalSTDensity e g (masterActionDensity e g)) = 0 := by
  rw [classicalLocalSTDensity, localClass_localST_eq_densityBracket,
    masterAction_classicalMasterEquation]

end YangMills.FullBV
