import Problems.YangMills.MomentumJetIdeal
import Problems.YangMills.CoincidentOddJet

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}
local instance multiindexDirectionBEq (n : ℕ) : BEq (Fin n × Fin 4) := instBEqOfDecidableEq

/-- Actual coordinate differentiation list associated to a rectangular
multiindex on every independent external momentum. -/
def coordinateDirections {n : ℕ} (a : Fin n → Fin 4 → ℕ) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap (fun i => (orderedMultiindex (a i)).map (fun mu => (i,mu)))

lemma coordinateDirections_count {n : ℕ} (a : Fin n → Fin 4 → ℕ) (i : Fin n) (mu : Fin 4) :
    (coordinateDirections a).count (i,mu) = a i mu := by
  unfold coordinateDirections
  simp only [List.count_flatMap,Function.comp_def,count_slotMap,orderedMultiindex_count]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp

lemma coordinateDirections_length {n : ℕ} (a : Fin n → Fin 4 → ℕ) :
    (coordinateDirections a).length = ∑ i : Fin n, ∑ mu : Fin 4, a i mu := by
  unfold coordinateDirections
  simp only [List.length_flatMap,List.length_map,orderedMultiindex_length]
  rw [← List.ofFn_eq_map,List.sum_ofFn]

lemma jetListOfDirections_coordinateDirections (legs : List (ExternalLeg G))
    (a : Fin legs.length → Fin 4 → ℕ) :
    jetListOfDirections legs (coordinateDirections a) = List.ofFn (fun i => (legs.get i,a i)) := by
  classical
  unfold jetListOfDirections
  congr 1
  funext i
  apply congrArg (fun b : Fin 4 → ℕ => (legs.get i,b))
  funext mu
  rw [Multiset.coe_count,coordinateDirections_count]

lemma monomialOfJetList_admissible_of_indices (jets : List (JetVariable G))
    (unique : ∀ i j : Fin jets.length, (jets.get i).1.parity = true → jets.get i = jets.get j → i=j) :
    (monomialOfJetList jets).Admissible := by
  classical
  intro v odd
  change (jets : Multiset (JetVariable G)).count v ≤ 1
  rw [← listGet_fiber_card]
  apply Fintype.card_le_one_iff_subsingleton.mpr
  constructor
  intro i j
  apply Subtype.ext
  apply unique i.val j.val
  · rw [i.property]
    exact odd
  · exact i.property.trans j.property.symm

/-- Distinct full derivative multiindices on repeated odd field slots give
an admissible actual normalized monomial, not merely a formal tuple. -/
theorem coordinateDirections_admissible (legs : List (ExternalLeg G))
    (a : Fin legs.length → Fin 4 → ℕ)
    (distinct : ∀ i j, i ≠ j → legs.get i = legs.get j → (legs.get i).parity = true → a i ≠ a j) :
    (directionMonomial legs (coordinateDirections a)).Admissible := by
  classical
  unfold directionMonomial
  rw [jetListOfDirections_coordinateDirections]
  apply monomialOfJetList_admissible_of_indices
  intro i j odd equal
  let index : ∀ k : Fin (List.ofFn (fun i : Fin legs.length => (legs.get i,a i))).length, Fin legs.length :=
    fun k => Fin.cast (by simp) k
  have equal' : (legs.get (index i),a (index i)) = (legs.get (index j),a (index j)) := by
    simpa only [List.get_ofFn,index] using equal
  have odd' : (legs.get (index i)).parity = true := by
    simpa only [List.get_ofFn,index] using odd
  by_contra different
  have index_ne : index i ≠ index j := by
    intro same
    apply different
    exact Fin.ext (congrArg (fun k : Fin legs.length => k.val) same)
  exact distinct (index i) (index j) index_ne (congrArg Prod.fst equal') odd' (congrArg Prod.snd equal')

/-- Coordinatewise divisibility is an exact list permutation after adding
the explicit nonnegative difference multiindex. -/
theorem coordinateDirections_extension {n : ℕ} (a b : Fin n → Fin 4 → ℕ)
    (bounded : ∀ i mu, b i mu ≤ a i mu) :
    (coordinateDirections a).Perm
      (coordinateDirections (fun i mu => a i mu - b i mu) ++ coordinateDirections b) := by
  classical
  apply List.perm_iff_count.mpr
  rintro ⟨i,mu⟩
  rw [List.count_append,coordinateDirections_count,coordinateDirections_count,coordinateDirections_count]
  exact (Nat.sub_add_cancel (bounded i mu)).symm

end YangMills.PerturbativeFlow
