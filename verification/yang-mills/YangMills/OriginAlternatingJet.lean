import YangMills.CanonicalJetExtraction

noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Repeated odd jets vanish at the symmetric base point. The hypothesis
states the actual antisymmetry and direction permutation; no claim at an
arbitrary nonzero momentum is hidden in this result. -/
theorem momentumJet_origin_zero_of_antisymmetry (legs : List (ExternalLeg G))
    (pi : Equiv.Perm (Fin legs.length)) (directions : List (Fin legs.length × Fin 4))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (antisymmetric : f ∘ momentumCoordinateRelabel pi = fun q => -f q)
    (directions_preserved :
      (directions.map (fun d => (pi.symm d.1,d.2))).Perm directions) :
    momentumJet directions f 0 = 0 := by
  let basis : Fin legs.length × Fin 4 → (Fin legs.length → Spacetime) :=
    fun d => Pi.single d.1 (Pi.single d.2 1)
  have chain := directionalCoordinates_relabel pi directions smooth (0 : Fin legs.length → Spacetime)
  have zero : momentumCoordinateRelabel pi (0 : Fin legs.length → Spacetime) = 0 := map_zero _
  rw [zero,antisymmetric] at chain
  have negative : directionalWord (directions.map basis) (fun q => -f q) 0 =
      -directionalWord (directions.map basis) f 0 := by
    simpa only [neg_one_mul] using directionalWord_const_mul (directions.map basis) (-1) smooth 0
  have permuted := congrFun (directionalWord_perm (directions_preserved.map basis) smooth) 0
  simp only [List.map_map,Function.comp_def,basis] at permuted
  rw [permuted] at chain
  change directionalWord (directions.map basis) (fun q => -f q) 0 = directionalWord (directions.map basis) f 0 at chain
  rw [negative] at chain
  rw [momentumJet_eq_directionalWord legs directions smooth]
  exact CharZero.neg_eq_self_iff.mp chain

end YangMills.PerturbativeFlow
