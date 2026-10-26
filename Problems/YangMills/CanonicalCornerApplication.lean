import Problems.YangMills.MultiindexMomentumDirections
import Problems.YangMills.CanonicalCornerCombinatorics

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 2400000
open scoped ContDiff BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative YangMills.CanonicalUV
variable {G : CompactSimpleGaugeGroup}
local instance cornerDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

/-- The actual canonical ultraviolet PDE annihilates every nonempty anchored
corner, including corners with repeated odd jets. -/
theorem canonicalCorner_zero (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (high : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0)
    (legs : List (ExternalLeg G)) (S : Finset (Fin legs.length × Fin 4)) (nonempty : S.Nonempty)
    (a : Fin legs.length → Fin 4 → ℕ) (q : Fin legs.length → Spacetime)
    (anchored : ∀ i mu, (i,mu) ∉ S → q i mu = 0) :
    momentumJet (coordinateDirections (corner S (D+legs.length+1) a)) (A legs) q = 0 := by
  classical
  obtain collision | ⟨b,bounded,large,distinct⟩ := corner_dichotomy D S nonempty a
    (fun i j => legs.get i = legs.get j ∧ (legs.get i).parity = true)
  · obtain ⟨i,j,ne,fields,hi,hj,same⟩ := collision
    have inactive_i (mu : Fin 4) : (i,mu) ∉ S := fun h => hi ((mem_activeLegs S i).mpr ⟨mu,h⟩)
    have inactive_j (mu : Fin 4) : (j,mu) ∉ S := fun h => hj ((mem_activeLegs S j).mpr ⟨mu,h⟩)
    apply momentumJet_pairCoincidence_zero A smooth graded legs _ i j ne fields.1 fields.2
    · intro mu
      simp only [Multiset.coe_count,coordinateDirections_count,corner,if_neg (inactive_i mu),if_neg (inactive_j mu)]
      exact congrFun same mu
    · funext mu
      rw [anchored i mu (inactive_i mu),anchored j mu (inactive_j mu)]
  · have admissible : (directionMonomial legs (coordinateDirections b)).Admissible :=
      coordinateDirections_admissible legs b (fun i j ne eq odd => distinct i j ne ⟨eq,odd⟩)
    apply momentumJet_extension_zero legs _ (coordinateDirections b)
      (coordinateDirections (fun i mu => corner S (D+legs.length+1) a i mu - b i mu))
      (coordinateDirections_extension _ b bounded) (smooth legs)
    intro p
    apply admissibleHighProjectorAdequacy A smooth graded D high legs _ admissible
    rw [coordinateDirections_length]
    omega

end YangMills.PerturbativeFlow
