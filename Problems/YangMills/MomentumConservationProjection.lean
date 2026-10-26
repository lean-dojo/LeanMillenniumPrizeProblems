import Problems.YangMills.FlowScaleConstancy

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual conserving extension fixes every balanced momentum tuple. -/
theorem conservingMomenta_of_balanced (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (balanced : BalancedMomenta legs q) :
    conservingMomenta legs q = q := by
  classical
  funext i
  unfold conservingMomenta
  split_ifs with last
  · have filt : (Finset.univ : Finset (Fin legs.length)).filter
        (fun j => j.val+1 < legs.length) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · intro h equal
        subst j
        omega
      · intro h
        have neq : j.val ≠ i.val := by
          intro he
          exact h (Fin.ext he)
        have := j.isLt
        omega
    rw [filt, Finset.sum_erase_eq_sub (Finset.mem_univ i), balanced]
    simp
  · rfl

theorem conservingMomenta_idempotent (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    conservingMomenta legs (conservingMomenta legs q) = conservingMomenta legs q :=
  conservingMomenta_of_balanced legs _ (conservingMomenta_balanced G legs q)

end YangMills.PerturbativeFlow
