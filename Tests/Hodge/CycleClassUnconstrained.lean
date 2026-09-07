import Problems.Hodge.Millennium

/-!
# The Hodge sketch does not pin down the cycle-class map

Independent of the cardinality defect exhibited in PR #9: the "canonical" realization interface
does not pin down `hodge_subspace` or `cycle_class`.  Given any canonical realization `R`, replacing every Hodge
summand of the right degree by `⊤` and the cycle-class map by `0` yields another canonical
realization.  Hence `ClayHodge` forces every even-degree rational cohomology group of every
variety (in every canonical realization) to vanish.  So `ClayHodge` is either vacuous (no
varieties have points, as PR #9 shows) or false (as soon as any variety has a point).

This file is a regression test: it must stop compiling once the Hodge statement is rewritten with a
defined cycle-class map.
-/

open MillenniumHodge

namespace Tests.Hodge.CycleClassUnconstrained

open VarietyDefinition

universe u₁ u₂ u₃

/-- Same cohomology and cycle types as `d`, but all in-degree Hodge summands are `⊤` and the
cycle-class map is identically zero. -/
noncomputable def killCycles {X : SmoothProjectiveVariety ℂ} (d : HodgeData.{u₁, u₂, u₃} X) :
    HodgeData.{u₁, u₂, u₃} X :=
  { d with
    hodge_subspace := fun n p q => if p + q = n then ⊤ else ⊥
    cycle_class := fun _ _ => 0
    cycle_class_is_pp := by
      intro p Z
      show d.extension_of_scalars_qc (2 * p) 0 ∈ (if p + p = 2 * p then ⊤ else ⊥)
      rw [map_zero]
      exact Submodule.zero_mem _ }

variable {X : SmoothProjectiveVariety ℂ} (d : HodgeData.{u₁, u₂, u₃} X)

theorem killCycles_hodge_subspace (n p q : ℕ) :
    (killCycles d).hodge_subspace n p q = if p + q = n then ⊤ else ⊥ := rfl

theorem killCycles_cycle_class (p : ℕ) : (killCycles d).cycle_class p = fun _ => 0 := rfl

theorem killCycles_extension (n : ℕ) :
    (killCycles d).extension_of_scalars_qc n = d.extension_of_scalars_qc n := rfl

theorem killCycles_hodge_class_eq_top (p : ℕ) : (killCycles d).hodge_class p = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [HodgeData.mem_hodge_class_iff_complexified, killCycles_hodge_subspace,
    if_pos (two_mul p).symm]
  exact Submodule.mem_top

theorem killCycles_coherent : HodgeDataCoherence (killCycles d) := by
  constructor
  · intro n p q h
    rw [killCycles_hodge_subspace, if_neg h]
  · intro p
    apply le_antisymm
    · exact (killCycles d).hodge_class_le_hodge_class_filtration p
    · rw [killCycles_hodge_class_eq_top]
      exact le_top

theorem killCycles_spans (n : ℕ) :
    (⨆ p : ℕ, ⨆ q : ℕ, ⨆ (_hpq : p + q = n), (killCycles d).hodge_subspace n p q) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine Submodule.mem_iSup_of_mem n ?_
  refine Submodule.mem_iSup_of_mem 0 ?_
  refine Submodule.mem_iSup_of_mem (Nat.add_zero n) ?_
  rw [killCycles_hodge_subspace, if_pos (Nat.add_zero n)]
  exact Submodule.mem_top

/-- The modified realization: same cohomology, no cycle classes. -/
noncomputable def killCyclesRealization (R : HodgeTheoryRealization.{u₁, u₂, u₃}) :
    HodgeTheoryRealization.{u₁, u₂, u₃} where
  assignment :=
    { data := fun X => killCycles (R.assignment.data X)
      coherent := fun _ => killCycles_coherent _ }
  extension_injective := fun X n => R.extension_injective X n

  hodge_decomposition_spans := fun _ n => killCycles_spans _ n

/-- Killing the cycle classes preserves every "canonical" anchor. -/
theorem killCyclesRealization_isCanonical (R : HodgeTheoryRealization.{u₁, u₂, u₃})
    (h : R.IsCanonical) : (killCyclesRealization R).IsCanonical where
  rational_cohomology_is_betti := h.rational_cohomology_is_betti
  complex_cohomology_is_betti := h.complex_cohomology_is_betti
  algebraic_cycles_are_geometric := h.algebraic_cycles_are_geometric

theorem killCycles_cycle_class_combination (p : ℕ) (c : (killCycles d).algebraic_cycle p →₀ ℚ) :
    (killCycles d).cycle_class_combination p c = 0 := by
  unfold HodgeData.cycle_class_combination
  rw [killCycles_cycle_class]
  simp [Finsupp.linearCombination_apply]

theorem killCyclesRealization_hodge_class_eq_top (R : HodgeTheoryRealization.{u₁, u₂, u₃})
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    ((killCyclesRealization R).assignment.data X).hodge_class p = ⊤ :=
  killCycles_hodge_class_eq_top (R.assignment.data X) p

/-- `ClayHodge` implies that, for every canonical realization and every variety, all rational
cohomology in even degrees is zero. -/
theorem clayHodge_forces_zero (hC : ClayHodge.{u₁, u₂, u₃})
    (R : HodgeTheoryRealization.{u₁, u₂, u₃}) (hR : R.IsCanonical)
    (X : SmoothProjectiveVariety ℂ) (p : ℕ)
    (x : (R.assignment.data X).cohomology_q (2 * p)) : x = 0 := by
  have key := hC (killCyclesRealization R) (killCyclesRealization_isCanonical R hR) X p x
  obtain ⟨c, hc⟩ := key (by
    rw [killCyclesRealization_hodge_class_eq_top]
    exact Submodule.mem_top)
  exact hc.symm.trans (killCycles_cycle_class_combination (R.assignment.data X) p c)

/-- In particular `ClayHodge` implies `H^0(X, ℚ) = 0` for every variety, for any canonical
realization: no variety may have a point. -/
theorem clayHodge_forces_subsingleton (hC : ClayHodge.{u₁, u₂, u₃})
    (R : HodgeTheoryRealization.{u₁, u₂, u₃}) (hR : R.IsCanonical)
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    Subsingleton ((R.assignment.data X).cohomology_q (2 * p)) :=
  ⟨fun a b => by rw [clayHodge_forces_zero hC R hR X p a, clayHodge_forces_zero hC R hR X p b]⟩

end Tests.Hodge.CycleClassUnconstrained

