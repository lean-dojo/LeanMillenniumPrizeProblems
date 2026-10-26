import Problems.YangMills.FourierTaylorCoordinates
import Problems.YangMills.ReducedTaylorDensity

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The literal Fourier product of the actual derivative buckets is the
product over the original ordered directions. Only scalar coefficients
are reordered; odd jet variables stay in the superalgebra. -/
theorem directionBucket_Fourier_product (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (q : Fin legs.length → Fin 4 → ℂ) :
    (∏ i : Fin legs.length,
      ((directionBucket directions i).map (fun μ => -Complex.I * q i μ)).prod) =
      (-Complex.I)^directions.length * (directions.map (fun d => q d.1 d.2)).prod := by
  classical
  induction directions with
  | nil => simp [directionBucket]
  | cons d ds ih =>
    have hb (i : Fin legs.length) :
        ((directionBucket (d :: ds) i).map (fun μ => -Complex.I * q i μ)).prod =
          (if i = d.1 then -Complex.I * q d.1 d.2 else 1) *
            ((directionBucket ds i).map (fun μ => -Complex.I * q i μ)).prod := by
      by_cases hi : i = d.1
      · subst i
        simp [directionBucket]
      · simp [directionBucket, hi, Ne.symm hi]
    simp only [hb, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, ih,
      List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    ring

/-- Actual cancellation of the source extraction phase against every
Fourier derivative, with its exact multiplicity. -/
theorem directionBucket_Fourier_phase_cancel (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    (q : Fin legs.length → Fin 4 → ℂ) :
    Complex.I^directions.length *
      (∏ i : Fin legs.length,
        ((directionBucket directions i).map (fun μ => -Complex.I * q i μ)).prod) =
      (directions.map (fun d => q d.1 d.2)).prod := by
  rw [directionBucket_Fourier_product, ← mul_assoc, ← mul_pow]
  simp

end YangMills.IntegratedNormalization
