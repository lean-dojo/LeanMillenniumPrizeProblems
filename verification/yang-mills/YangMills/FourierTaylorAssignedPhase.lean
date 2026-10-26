import YangMills.FourierTaylorBuckets
import YangMills.FourierTaylorFieldSum

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- After the actual field sum, the assigned Fourier factors have the
inverse-permuted external momenta. The extraction phase cancels exactly,
leaving the literal scalar monomial used in multilinear Taylor expansion. -/
theorem assignedTaylorPhase (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (q : Fin legs.length → Spacetime) (π : Equiv.Perm (Fin legs.length)) :
    Complex.I^directions.length *
      assignedVertexTerm
        (fun j => ⟨legs.get (π.symm j), directionBucket directions j⟩)
        (fun i => (legs.get i, q i)) π =
      YangMills.LegendreInsertionBridge.parityExternalSign
          (fun j => (legs.get (π.symm j)).parity) π *
        (directions.map (fun d => (q (π.symm d.1) d.2 : ℂ))).prod := by
  classical
  unfold assignedVertexTerm
  simp only [assignedFourierFactor, π.symm_apply_apply, if_true]
  have hr : (∏ i : Fin legs.length,
      ((directionBucket directions (π i)).map (fun μ => -Complex.I * (q i μ : ℂ))).prod) =
      ∏ j : Fin legs.length,
        ((directionBucket directions j).map
          (fun μ => -Complex.I * (q (π.symm j) μ : ℂ))).prod := by
    simpa only [π.symm_apply_apply] using
      (Equiv.prod_comp π (fun j =>
        ((directionBucket directions j).map
          (fun μ => -Complex.I * (q (π.symm j) μ : ℂ))).prod))
  rw [hr, ← mul_assoc]
  rw [mul_comm (Complex.I^directions.length)]
  rw [mul_assoc, directionBucket_Fourier_phase_cancel]

end YangMills.IntegratedNormalization
