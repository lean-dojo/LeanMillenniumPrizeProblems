import Problems.YangMills.FullBVPhysicalActionInvariance
import Problems.YangMills.FullBVBasicFieldSum

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def sourceShiftCurrent {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) (mu : Fin 4) : JetAlgebra G :=
  Complex.I • (gaugeQuadratic e g mu a * jet ⟨.inr (.auxiliary a), 0⟩)

/-- The exact shifted-B source integration by parts. The current uses only
the nonlinear part of the same actual gauge characteristic. -/
theorem auxiliarySource_characteristic_IBP {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) :
    -(stCharacteristic (masterActionDensity e g) (.inl (.auxiliary a)) *
      jet ⟨.inr (.auxiliary a), 0⟩) +
      (∑ mu : Fin 4, totalDerivative mu (sourceShiftCurrent e g a mu)) =
      (∑ mu : Fin 4,
        (-Complex.I) • (jet ⟨.inl (.ghost a), Pi.single mu 2⟩ * jet ⟨.inr (.auxiliary a), 0⟩)) +
      ∑ mu : Fin 4, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (Complex.I * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          ((gaugePotentialJet G mu b * ghostJet G c) *
            jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩) := by
  have hn (X : JetAlgebra G) : -(Complex.I • X) = (-Complex.I) • X :=
    (neg_smul Complex.I X).symm
  rw [master_characteristic_auxiliary_divergence]
  simp only [totalDerivatives_single_one, master_characteristic_gauge,
    totalDerivative_add, totalDerivative_jet, Jet.shift, single_one_add_one,
    Finset.sum_add_distrib, smul_add, smul_mul_assoc, Finset.sum_mul, neg_add,
    ← Finset.sum_neg_distrib, hn]
  unfold sourceShiftCurrent
  simp only [totalDerivative_smul, totalDerivative_mul_jet_ordinary,
    totalDerivative_jet, Jet.shift, zero_add, smul_add, Finset.sum_add_distrib]
  have hp : (∑ mu : Fin 4, Complex.I •
      (gaugeQuadratic e g mu a * jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩)) =
      ∑ mu : Fin 4, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        (Complex.I * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          ((gaugePotentialJet G mu b * ghostJet G c) *
            jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩) := by
    simp only [gaugeQuadratic, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul,
      mul_assoc, gaugePotentialJet]
  rw [← hp]
  simp only [← Finset.smul_sum]
  change -((Complex.I • (∑ mu : Fin 4, jet ⟨.inl (.ghost a), Pi.single mu 2⟩) +
      Complex.I • (∑ mu : Fin 4, totalDerivative mu (gaugeQuadratic e g mu a))) *
      jet ⟨.inr (.auxiliary a), 0⟩) +
    (Complex.I • (∑ mu : Fin 4, totalDerivative mu (gaugeQuadratic e g mu a) *
      jet ⟨.inr (.auxiliary a), 0⟩) +
      Complex.I • (∑ mu : Fin 4, gaugeQuadratic e g mu a *
        jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩)) = _
  simp only [add_mul, smul_mul_assoc, Finset.sum_mul]
  module

/-- Explicit component form of −Σ(sφ)φ†, using the same master-derived
characteristics for all four basic species. -/
def sourceCharacteristicDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  ∑ a : Fin G.dimension,
    (-(stCharacteristic (masterActionDensity e g) (.inl (.ghost a)) * jet ⟨.inr (.ghost a), 0⟩) +
    -(stCharacteristic (masterActionDensity e g) (.inl (.antighost a)) * jet ⟨.inr (.antighost a), 0⟩) +
    -(stCharacteristic (masterActionDensity e g) (.inl (.auxiliary a)) * jet ⟨.inr (.auxiliary a), 0⟩) +
    ∑ mu : Fin 4,
      -(stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) * jet ⟨.inr (.gauge mu a), 0⟩))

private theorem sum_first_last {I J K M : Type*} [Fintype I] [Fintype J]
    [Fintype K] [AddCommMonoid M] (f : I → J → K → M) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact Finset.sum_comm

/-- The full actual antifield density is exactly minus the actual BRST
characteristics coupled to the sources, with the fixed shifted-B current. -/
theorem fullAntifieldDensity_characteristic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    sourceCharacteristicDensity e g +
      (∑ a : Fin G.dimension, ∑ mu : Fin 4,
        totalDerivative mu (sourceShiftCurrent e g a mu)) = fullAntifieldDensity e g := by
  have hn (X Y : JetAlgebra G) : (-X) * Y = -(X * Y) := neg_mul X Y
  unfold sourceCharacteristicDensity fullAntifieldDensity freeAntifieldDensity nonlinearSourceDensity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a ha
  have haux := auxiliarySource_characteristic_IBP e g a
  have hr (P Q R T U : JetAlgebra G) : (P + Q + R + T) + U =
      P + Q + (R + U) + T := by abel
  rw [hr, haux]
  simp only [master_characteristic_ghost, master_characteristic_antighost,
    master_characteristic_gauge, hn, neg_neg, add_mul, smul_mul_assoc,
    Finset.sum_mul, neg_add, Finset.sum_add_distrib]
  simp only [ghostQuadratic, gaugeQuadratic, gaugePotentialJet, ghostJet,
    Finset.sum_mul, smul_mul_assoc, ← Finset.sum_neg_distrib]
  have hA : (∑ mu : Fin 4, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      -(((structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) *
          jet ⟨.inr (.gauge mu a), 0⟩))) =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ mu : Fin 4,
        -(((structureConstant e a b c : ℂ) * (g : ℂ)) •
          ((jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) *
            jet ⟨.inr (.gauge mu a), 0⟩)) := sum_first_last _
  have hB : (∑ mu : Fin 4, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      (Complex.I * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((gaugePotentialJet G mu b * ghostJet G c) *
          jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩)) =
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ mu : Fin 4,
        (Complex.I * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          ((gaugePotentialJet G mu b * ghostJet G c) *
            jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩) := sum_first_last _
  simp only [gaugePotentialJet, ghostJet] at hB
  rw [hA, hB]
  have hs (r : ℂ) (P : JetAlgebra G) : -(r • P) = (-r) • P := (neg_smul r P).symm
  simp only [hs, ← complex_neg_one_smul, neg_mul, smul_smul, neg_one_mul,
    auxiliaryJet, gaugeFirstJet, gaugePotentialJet, ghostJet, Finset.sum_add_distrib]
  abel

/-- The component presentation includes exactly every actual basic species. -/
theorem sourceCharacteristicDensity_eq_sum {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    sourceCharacteristicDensity e g =
      ∑ K : BasicField G,
        -(stCharacteristic (masterActionDensity e g) (.inl K) * jet ⟨.inr K,0⟩) := by
  rw [sum_basicField_components]
  unfold sourceCharacteristicDensity
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun mu a =>
    -(stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) *
      jet ⟨.inr (.gauge mu a), 0⟩))]
  abel

end YangMills.FullBV
