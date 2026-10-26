import YangMills.MomentumJetIdeal

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow

/-- The scalar coordinates used in rectangular PDE determinacy are the
actual pairs (external slot, spacetime coordinate) of the same momenta. -/
def flattenMomentumCoordinates (n : ℕ) :
    (Fin n → Spacetime) ≃L[ℝ] ((Fin n × Fin 4) → ℝ) where
  toFun q := fun p => q p.1 p.2
  invFun q := fun i mu => q (i,mu)
  left_inv := by intro q; rfl
  right_inv := by intro q; funext p; cases p; rfl
  map_add' := by intro q p; rfl
  map_smul' := by intro c q; rfl
  continuous_toFun := continuous_pi (fun p => (continuous_apply p.2).comp (continuous_apply p.1))
  continuous_invFun := continuous_pi (fun i => continuous_pi (fun mu => continuous_apply (i,mu)))

lemma unflattenMomentumCoordinates_single {n : ℕ} (p : Fin n × Fin 4) :
    (flattenMomentumCoordinates n).symm (Pi.single p 1) = (Pi.single p.1 (Pi.single p.2 1) : Fin n → Spacetime) := by
  rcases p with ⟨i,mu⟩
  ext j nu
  change (Pi.single (i,mu) (1 : ℝ) : (Fin n × Fin 4) → ℝ) (j,nu) = (Pi.single i (Pi.single mu (1 : ℝ)) : Fin n → Spacetime) j nu
  by_cases ji : j=i <;> by_cases same : nu=mu <;>
    simp_all [Pi.single_apply,Prod.mk.injEq]

/-- Exact transport from the scalar-coordinate directional words of the
analytic rectangle theorem to the SAME actual momentumJet. -/
theorem flattenedDirectionalWord_eq_momentumJet {G : CompactSimpleGaugeGroup}
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (q : (Fin legs.length × Fin 4) → ℝ) :
    directionalWord (directions.map (fun p => (Pi.single p 1 : (Fin legs.length × Fin 4) → ℝ)))
      (f ∘ (flattenMomentumCoordinates legs.length).symm) q =
      momentumJet directions f ((flattenMomentumCoordinates legs.length).symm q) := by
  rw [directionalWord_comp_linearEquiv _ _ smooth]
  simp only [List.map_map,Function.comp_def,unflattenMomentumCoordinates_single]
  rw [momentumJet_eq_directionalWord legs directions smooth]

end YangMills.PerturbativeFlow
