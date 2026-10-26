import YangMills.FlowNormalizationDilation
import YangMills.CompositeExtraction

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

lemma sum_filter_partition {alpha : Type*} (items : List alpha) (p : alpha → Bool) (f : alpha → ℕ) :
    ((items.filter p).map f).sum + ((items.filter (fun a => !p a)).map f).sum = (items.map f).sum := by
  induction items with
  | nil => rfl
  | cons a items ih =>
    cases hp : p a <;> simp [hp] <;> omega

lemma sum_flatMap_eq {alpha : Type*} (items : List alpha) (f : alpha → List ℕ) :
    (items.flatMap f).sum = (items.map (fun a => (f a).sum)).sum := by
  induction items with
  | nil => rfl
  | cons a items ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

/-- Sorting and the basic/antifield partition preserve actual weighted
monomial multiplicities. This uses the implemented orderedJets, not an
independently selected list representation. -/
lemma LocalMonomial.orderedJets_sum (m : LocalMonomial G) (f : JetVariable G → ℕ) :
    (m.orderedJets.map f).sum = m.sum (fun v n => n*f v) := by
  classical
  unfold LocalMonomial.orderedJets
  rw [List.map_append,List.sum_append,sum_filter_partition]
  simp only [List.map_flatMap,sum_flatMap_eq,List.map_replicate,List.sum_replicate]
  have permutation := List.mergeSort_perm m.support.toList (fun a b => jetCode a ≤ jetCode b)
  have sums := (permutation.map (fun v => m v * f v)).sum_eq
  change ((m.support.toList.mergeSort _).map (fun v => m v * f v)).sum = _
  rw [sums]
  simpa only [Finset.toList_toFinset,Finsupp.sum] using
    (List.sum_toFinset (fun v => m v*f v) m.support.nodup_toList).symm

lemma orderedMultiindex_length (d : Fin 4 → ℕ) : (orderedMultiindex d).length = ∑ mu : Fin 4, d mu := by
  simp only [orderedMultiindex,List.length_flatMap,List.length_replicate,← List.ofFn_eq_map,List.sum_ofFn]

/-- The projector's actual external legs and momentum directions account
for exactly its existing engineering degree, including antifield weights. -/
theorem LocalMonomial.projector_dimension (m : LocalMonomial G) :
    totalDimension m.legs + m.momentumDirections.length = m.dimension := by
  classical
  have legs_sum : totalDimension m.legs = (m.orderedJets.map (fun v => v.1.dimension)).sum := by
    simp [totalDimension,LocalMonomial.legs,List.map_map,Function.comp_def]
  have directions_sum : m.momentumDirections.length =
      (m.orderedJets.map (fun v => ∑ mu : Fin 4, v.2 mu)).sum := by
    unfold LocalMonomial.momentumDirections
    simp only [List.length_flatMap,List.length_map,orderedMultiindex_length]
    rw [← List.ofFn_eq_map]
    have actualJets : List.ofFn (fun i : Fin m.legs.length => m.jetAt i) = m.orderedJets := by
      simpa only [LocalMonomial.jetAt,LocalMonomial.legs,List.length_map] using List.ofFn_get m.orderedJets
    change (List.ofFn ((fun v : JetVariable G => ∑ mu : Fin 4, v.2 mu) ∘ m.jetAt)).sum = _
    rw [← List.map_ofFn,actualJets]
  rw [legs_sum,directions_sum,← List.sum_map_add]
  exact m.orderedJets_sum JetVariable.dimension

/-- The exact implemented output projector has the correct dimension under
canonical amplitude rescaling; all multiindex factorials stay unchanged. -/
theorem extractCoefficient_rescaleFlow (a : ℝ) (positive : 0 < a)
    (L : FlowFamily G) (loop : ℕ) (Λ UV : ℝ) (m : LocalMonomial G)
    (q : Fin m.legs.length → Spacetime) :
    extractCoefficient m (rescaleFlow a L loop Λ UV) q =
      (a : ℂ)^((m.dimension : ℤ)-4) * extractCoefficient m (L loop (a*Λ) (a*UV)) (a • q) := by
  unfold extractCoefficient
  have jet := momentumJet_rescaleFlow a positive L loop Λ UV m.legs m.momentumDirections q
  unfold momentumJet at jet
  rw [jet]
  have weight : (totalDimension m.legs : ℤ)+m.momentumDirections.length-4 = (m.dimension : ℤ)-4 := by
    have actual := m.projector_dimension
    omega
  rw [weight]
  ring

end YangMills.PerturbativeFlow
