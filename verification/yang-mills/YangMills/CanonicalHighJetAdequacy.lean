import YangMills.CanonicalProjectorDeterminacy

/-!
Canonical high-projector equations imply ALL high coordinate equations.
The proof applies smooth anchored determinacy to the actual high derivative,
not to a Taylor-series sum. Repeated odd jets vanish only on the required
coincidence faces. No analyticity or additional ultraviolet axiom is used.
-/
noncomputable section
set_option maxHeartbeats 3200000
open scoped ContDiff BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative YangMills.CanonicalUV
variable {G : CompactSimpleGaugeGroup}
local instance highDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

lemma momentumJet_smooth (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (momentumJet directions f) := by
  have eq : momentumJet directions f = directionalWord
      (directions.map (fun d => (Pi.single d.1 (Pi.single d.2 1) : Fin legs.length → Spacetime))) f := by
    funext p
    exact momentumJet_eq_directionalWord legs directions smooth p
  rw [eq]
  exact directionalWord_smooth _ smooth

lemma momentumJet_append (legs : List (ExternalLeg G))
    (first last : List (Fin legs.length × Fin 4))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (q : Fin legs.length → Spacetime) :
    momentumJet first (momentumJet last f) q = momentumJet (first ++ last) f q := by
  rw [momentumJet_eq_directionalWord legs first (momentumJet_smooth legs last smooth),
    momentumJet_eq_directionalWord legs (first ++ last) smooth,List.map_append,directionalWord_append]
  congr 1
  funext p
  exact momentumJet_eq_directionalWord legs last smooth p

/-- High origin jets require no low-row normalization: inadmissible odd
squares vanish by the actual graded symmetry at the origin. -/
theorem canonicalHighOriginJet_zero (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (high : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (degree : D < totalDimension legs + directions.length) :
    momentumJet directions (A legs) 0 = 0 := by
  apply (canonicalJetExtraction_zero_iff A smooth graded legs directions 0).mp
  rw [map_zero]
  by_cases admissible : (directionMonomial legs directions).Admissible
  · exact high _ admissible (by rw [directionMonomial_dimension]; exact degree) _
  · exact extractCoefficient_nonadmissible_zero A smooth graded _ admissible

/-- A nonempty anchored face only needs its active coordinate orders to
DOMINATE the fixed rectangle size. This permits differentiation of an
already high jet, without incorrectly assuming it is graded itself. -/
theorem canonicalDominatingCorner_zero (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (high : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (S : Finset (Fin legs.length × Fin 4)) (nonempty : S.Nonempty)
    (dominates : ∀ z ∈ S, D+legs.length+1 ≤ directions.count z)
    (q : Fin legs.length → Spacetime)
    (anchored : ∀ i mu, (i,mu) ∉ S → q i mu = 0) :
    momentumJet directions (A legs) q = 0 := by
  classical
  let a : Fin legs.length → Fin 4 → ℕ := fun i mu => directions.count (i,mu)
  obtain collision | ⟨b,bounded,large,distinct⟩ := corner_dichotomy D S nonempty a
    (fun i j => legs.get i = legs.get j ∧ (legs.get i).parity = true)
  · obtain ⟨i,j,ne,fields,hi,hj,same⟩ := collision
    have inactive_i (mu : Fin 4) : (i,mu) ∉ S := fun h => hi ((mem_activeLegs S i).mpr ⟨mu,h⟩)
    have inactive_j (mu : Fin 4) : (j,mu) ∉ S := fun h => hj ((mem_activeLegs S j).mpr ⟨mu,h⟩)
    apply momentumJet_pairCoincidence_zero A smooth graded legs directions i j ne fields.1 fields.2
    · intro mu
      simpa only [Multiset.coe_count] using congrFun same mu
    · funext mu
      rw [anchored i mu (inactive_i mu),anchored j mu (inactive_j mu)]
  · have admissible : (directionMonomial legs (coordinateDirections b)).Admissible :=
      coordinateDirections_admissible legs b (fun i j ne eq odd => distinct i j ne ⟨eq,odd⟩)
    have divided : ∀ i mu, b i mu ≤ a i mu := by
      intro i mu
      apply (bounded i mu).trans
      unfold corner
      split_ifs with h
      · exact dominates (i,mu) h
      · exact le_rfl
    have permutation : directions.Perm (coordinateDirections a) := by
      apply List.perm_iff_count.mpr
      rintro ⟨i,mu⟩
      exact (coordinateDirections_count a i mu).symm
    apply momentumJet_extension_zero legs directions (coordinateDirections b)
      (coordinateDirections (fun i mu => a i mu - b i mu))
      (permutation.trans (coordinateDirections_extension a b divided)) (smooth legs)
    intro p
    apply admissibleHighProjectorAdequacy A smooth graded D high legs _ admissible
    rw [coordinateDirections_length]
    omega

/-- The original canonical admissible ultraviolet equations imply every
higher independent coordinate derivative vanishes at every momentum.
In particular the finite UV amplitude is a genuine finite polynomial; no
stronger boundary equations have been added to the prescription. -/
theorem canonicalHighProjectorAdequacy (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (D : ℕ)
    (high : ∀ m : LocalMonomial G, m.Admissible → D < m.dimension → ∀ p, extractCoefficient m A p = 0)
    (legs : List (ExternalLeg G)) (beta : List (Fin legs.length × Fin 4))
    (degree : D < totalDimension legs + beta.length) (q : Fin legs.length → Spacetime) :
    momentumJet beta (A legs) q = 0 := by
  classical
  let f : ((Fin legs.length × Fin 4) → ℝ) → ℂ :=
    (momentumJet beta (A legs)) ∘ (flattenMomentumCoordinates legs.length).symm
  have fsmooth : ContDiff ℝ ∞ f := (momentumJet_smooth legs beta (smooth legs)).comp
    (flattenMomentumCoordinates legs.length).symm.contDiff
  have zero : f = 0 := anchored_coordinate_determinacy (L := D+legs.length+1) fsmooth (by
    intro directions bounded p anchored
    change directionalWord _ f p = 0
    rw [flattenedDirectionalWord_eq_momentumJet legs directions (momentumJet_smooth legs beta (smooth legs)),
      momentumJet_append legs directions beta (smooth legs)]
    let S : Finset (Fin legs.length × Fin 4) := Finset.univ.filter (fun z => directions.count z = D+legs.length+1)
    by_cases nonempty : S.Nonempty
    · apply canonicalDominatingCorner_zero A smooth graded D high legs (directions ++ beta) S nonempty
      · intro z hz
        rw [List.count_append]
        have same := (Finset.mem_filter.mp hz).2
        omega
      · intro i mu inactive
        apply anchored (i,mu) (by simp)
        have not_equal : directions.count (i,mu) ≠ D+legs.length+1 := by
          intro equal
          exact inactive (Finset.mem_filter.mpr ⟨Finset.mem_univ _,equal⟩)
        exact lt_of_le_of_ne (bounded (i,mu)) not_equal
    · have origin : (flattenMomentumCoordinates legs.length).symm p = 0 := by
        funext i mu
        apply anchored (i,mu) (by simp)
        have not_equal : directions.count (i,mu) ≠ D+legs.length+1 := by
          intro equal
          exact nonempty ⟨(i,mu),Finset.mem_filter.mpr ⟨Finset.mem_univ _,equal⟩⟩
        exact lt_of_le_of_ne (bounded (i,mu)) not_equal
      rw [origin]
      apply canonicalHighOriginJet_zero A smooth graded D high legs (directions ++ beta)
      simp only [List.length_append]
      omega)
  have value := congrFun zero ((flattenMomentumCoordinates legs.length) q)
  simpa only [f,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply,Pi.zero_apply] using value

end YangMills.PerturbativeFlow
