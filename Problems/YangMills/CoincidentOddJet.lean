import Problems.YangMills.RepeatedOddProjector

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 2000000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative YangMills.LegendreInsertionBridge
variable {G : CompactSimpleGaugeGroup}
local instance coincidentOddDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

/-- Antisymmetric actual jets vanish at ANY permutation-fixed momentum,
not only at the origin. This includes anchored rectangular Taylor faces. -/
theorem momentumJet_fixedPoint_zero_of_antisymmetry (legs : List (ExternalLeg G))
    (pi : Equiv.Perm (Fin legs.length)) (directions : List (Fin legs.length × Fin 4))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (antisymmetric : f ∘ momentumCoordinateRelabel pi = fun q => -f q)
    (directions_preserved : (directions.map (fun d => (pi.symm d.1,d.2))).Perm directions)
    (q : Fin legs.length → Spacetime) (fixed : momentumCoordinateRelabel pi q = q) :
    momentumJet directions f q = 0 := by
  let basis : Fin legs.length × Fin 4 → (Fin legs.length → Spacetime) :=
    fun d => Pi.single d.1 (Pi.single d.2 1)
  have chain := directionalCoordinates_relabel pi directions smooth q
  rw [fixed,antisymmetric] at chain
  have negative : directionalWord (directions.map basis) (fun p => -f p) q =
      -directionalWord (directions.map basis) f q := by
    simpa only [neg_one_mul] using directionalWord_const_mul (directions.map basis) (-1) smooth q
  have permuted := congrFun (directionalWord_perm (directions_preserved.map basis) smooth) q
  simp only [List.map_map,Function.comp_def,basis] at permuted
  rw [permuted] at chain
  change directionalWord (directions.map basis) (fun p => -f p) q = directionalWord (directions.map basis) f q at chain
  rw [negative] at chain
  rw [momentumJet_eq_directionalWord legs directions smooth]
  exact CharZero.neg_eq_self_iff.mp chain

lemma directions_swap_perm_of_equal_counts {n : ℕ}
    (directions : List (Fin n × Fin 4)) (i j : Fin n)
    (counts : ∀ mu : Fin 4, (directions : Multiset _).count (i,mu) = (directions : Multiset _).count (j,mu)) :
    (directions.map (fun d => (Equiv.swap i j d.1,d.2))).Perm directions := by
  classical
  apply List.perm_iff_count.mpr
  rintro ⟨k,mu⟩
  have injective : Function.Injective (fun d : Fin n × Fin 4 => (Equiv.swap i j d.1,d.2)) :=
    (Equiv.prodCongr (Equiv.swap i j) (Equiv.refl (Fin 4))).injective
  have counted := List.count_map_of_injective directions
    (fun d : Fin n × Fin 4 => (Equiv.swap i j d.1,d.2)) injective (Equiv.swap i j k,mu)
  simp only [Equiv.swap_apply_self] at counted
  rw [counted,← Multiset.coe_count (Equiv.swap i j k,mu) directions,← Multiset.coe_count (k,mu) directions]
  by_cases ki : k=i
  · subst k
    simpa only [Equiv.swap_apply_left] using (counts mu).symm
  · by_cases kj : k=j
    · subst k
      simpa only [Equiv.swap_apply_right] using counts mu
    · rw [Equiv.swap_apply_of_ne_of_ne ki kj]

/-- Actual graded component derivatives with a repeated odd jet vanish
where the corresponding two full momenta coincide. All other momenta and
derivatives are unrestricted. This is the precise anchored-face identity
needed in the smooth graded PDE uniqueness argument. -/
theorem momentumJet_pairCoincidence_zero (A : OrderedAmplitude G)
    (smooth : ∀ legs, ContDiff ℝ ∞ (A legs))
    (graded : ∀ legs q (pi : Equiv.Perm (Fin legs.length)),
      A (permutedLegs legs pi) (permutedMomenta legs pi q) = permutationSign legs pi * A legs q)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4))
    (i j : Fin legs.length) (distinct : i ≠ j) (fields_equal : legs.get i = legs.get j)
    (odd_i : (legs.get i).parity = true)
    (counts : ∀ mu : Fin 4, (directions : Multiset _).count (i,mu) = (directions : Multiset _).count (j,mu))
    (q : Fin legs.length → Spacetime) (coincident : q i = q j) :
    momentumJet directions (A legs) q = 0 := by
  classical
  have odd_j : (legs.get j).parity = true := by rw [← fields_equal]; exact odd_i
  have fields : permutedLegs legs (Equiv.swap i j) = legs := by
    apply permutationFields_of_preserved
    intro k
    by_cases ki : k=i
    · subst k
      simpa only [Equiv.swap_apply_left] using fields_equal.symm
    · by_cases kj : k=j
      · subst k
        simpa only [Equiv.swap_apply_right] using fields_equal
      · rw [Equiv.swap_apply_of_ne_of_ne ki kj]
  have transport := orderedAmplitude_relabel_transport A graded legs (Equiv.swap i j) fields
  rw [permutationSign_swap_odd legs i j distinct odd_i odd_j] at transport
  simp only [neg_one_mul] at transport
  apply momentumJet_fixedPoint_zero_of_antisymmetry legs (Equiv.swap i j) directions (smooth legs) transport
  · simpa only [Equiv.symm_swap] using directions_swap_perm_of_equal_counts directions i j counts
  · funext k
    change q (Equiv.swap i j k) = q k
    by_cases ki : k=i
    · subst k
      simpa only [Equiv.swap_apply_left] using coincident.symm
    · by_cases kj : k=j
      · subst k
        simpa only [Equiv.swap_apply_right] using coincident
      · rw [Equiv.swap_apply_of_ne_of_ne ki kj]

end YangMills.PerturbativeFlow
