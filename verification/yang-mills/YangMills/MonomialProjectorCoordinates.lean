import YangMills.MomentumJetSymmetry
import Mathlib.Data.Finsupp.Multiset

noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

lemma count_eq_sumIndicator {α : Type*} [DecidableEq α] (items : List α) (v : α) :
    (items : Multiset α).count v = (items.map (fun w => if w = v then 1 else 0)).sum := by
  induction items with
  | nil => simp
  | cons w rest ih =>
    change Multiset.count v (w ::ₘ (rest : Multiset α)) = _
    rw [Multiset.count_cons,List.map_cons,List.sum_cons,ih]
    by_cases equal : v = w <;> simp [equal,eq_comm,Nat.add_comm]

lemma LocalMonomial.orderedJets_count (m : LocalMonomial G) (v : JetVariable G) :
    (m.orderedJets : Multiset (JetVariable G)).count v = m v := by
  classical
  rw [count_eq_sumIndicator,m.orderedJets_sum]
  simp [Finsupp.sum,mul_ite]
  intro zero
  exact zero.symm

/-- The canonical sorted/basic-first list has precisely the given jet
multiplicities; it does not impose a separate choice of polynomial. -/
theorem LocalMonomial.orderedJets_multiset (m : LocalMonomial G) :
    (m.orderedJets : Multiset (JetVariable G)).toFinsupp = m := by
  classical
  ext v
  simpa only [Multiset.toFinsupp_apply] using m.orderedJets_count v

/-- Recover an actual local monomial from an arbitrary finite jet list. -/
def monomialOfJetList (jets : List (JetVariable G)) : LocalMonomial G := by
  classical
  exact (jets : Multiset (JetVariable G)).toFinsupp

lemma orderedJets_perm_ofJetList (jets : List (JetVariable G)) :
    (monomialOfJetList jets).orderedJets.Perm jets := by
  classical
  apply Multiset.coe_eq_coe.mp
  apply Multiset.toFinsupp.injective
  rw [LocalMonomial.orderedJets_multiset]
  rfl

lemma monomialOfJetList_dimension (jets : List (JetVariable G)) :
    (monomialOfJetList jets).dimension = (jets.map JetVariable.dimension).sum := by
  have actual := (monomialOfJetList jets).orderedJets_sum JetVariable.dimension
  change ((monomialOfJetList jets).orderedJets.map JetVariable.dimension).sum =
    (monomialOfJetList jets).dimension at actual
  rw [← actual]
  exact ((orderedJets_perm_ofJetList jets).map JetVariable.dimension).sum_eq

/-- The monomial belonging to arbitrary ordered momentum directions records
how many derivatives strike each actual external slot and coordinate. -/
def jetListOfDirections (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : List (JetVariable G) := by
  classical
  exact List.ofFn (fun i : Fin legs.length =>
    (legs.get i,fun mu => (directions : Multiset (Fin legs.length × Fin 4)).count (i,mu)))

lemma jetListOfDirections_dimension (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    (monomialOfJetList (jetListOfDirections legs directions)).dimension =
      totalDimension legs + directions.length := by
  classical
  rw [monomialOfJetList_dimension]
  simp only [jetListOfDirections,List.map_ofFn,List.sum_ofFn,JetVariable.dimension,Function.comp_apply]
  rw [Finset.sum_add_distrib]
  have first : (∑ i : Fin legs.length, (legs.get i).dimension) = totalDimension legs := by
    unfold totalDimension
    rw [← List.sum_ofFn]
    have equality : List.ofFn (fun i : Fin legs.length => (legs.get i).dimension) =
        legs.map ExternalLeg.dimension := by
      simpa only [List.ofFn_get] using (List.ofFn_comp' legs.get ExternalLeg.dimension)
    rw [equality]
  rw [first]
  congr 1
  calc
    _ = ∑ p : Fin legs.length × Fin 4, (directions : Multiset _).count p :=
      (Fintype.sum_prod_type (fun p : Fin legs.length × Fin 4 => (directions : Multiset _).count p)).symm
    _ = _ := Multiset.sum_count_eq_card (by intro p _; exact Finset.mem_univ p)

end YangMills.PerturbativeFlow
