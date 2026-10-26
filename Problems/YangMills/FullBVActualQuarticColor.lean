import Problems.YangMills.FullBVPhysicalGhostDecomposition

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The fixed engine quartic tensor is the contraction of the actual
same-frame Lie structure constants, not an independent quartic coupling. -/
theorem fourColor_structure_contraction {B : InvariantForm G} (e : ColorFrame B)
    (a b c d : Fin G.dimension) :
    fourColor B (e.basis a) (e.basis b) (e.basis c) (e.basis d) =
      ∑ r : Fin G.dimension, structureConstant e r a b * structureConstant e r c d := by
  unfold fourColor
  conv_lhs => rw [← e.basis.sum_repr ⁅e.basis a, e.basis b⁆]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← color_coordinate]
  rfl

end YangMills.Perturbative
