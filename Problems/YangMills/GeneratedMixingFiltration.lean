import Problems.YangMills.IntrinsicFiltration
import Problems.YangMills.GeneratedGammaCohomology

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- A computed gamma entry can only lower the actual intrinsic engineering
filtration. Its finite classical coordinate resolution cannot undo the
same local mixing support bound. -/
theorem GeneratedScaleNormalization.gammaLoop_filtered
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (order loop : ℕ) (output input : basis.Index)
    (hne : N.euclideanGammaLoop basis mu order loop output input ≠ 0) :
    intrinsicEngineeringDimension (basis.label output) ≤
      intrinsicEngineeringDimension (basis.label input) := by
  have hc : output ∈ (basis.classicalCoordinates
      (N.mixingLabel mu order loop (basis.label input))).support := by
    apply Finsupp.mem_support_iff.mpr
    simpa only [N.gammaLoop_coordinates] using hne
  exact (basis.classicalCoordinates_degree _ output hc).trans
    (N.mixingLabel_dimension mu order loop (basis.label input))

theorem GeneratedScaleNormalization.gammaLoop_above_dimension
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (order loop : ℕ) (output input : basis.Index)
    (above : intrinsicEngineeringDimension (basis.label input) <
      intrinsicEngineeringDimension (basis.label output)) :
    N.euclideanGammaLoop basis mu order loop output input = 0 := by
  by_contra h
  exact (not_le_of_gt above) (N.gammaLoop_filtered basis mu order loop output input h)

/-- The finite physical loop assembly retains the very same filtration. -/
theorem GeneratedScaleNormalization.gammaSeries_above_dimension
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (order : ℕ) (output input : basis.Index)
    (above : intrinsicEngineeringDimension (basis.label input) <
      intrinsicEngineeringDimension (basis.label output)) :
    N.euclideanGammaSeries basis mu order output input = 0 := by
  simp [GeneratedScaleNormalization.euclideanGammaSeries,
    N.gammaLoop_above_dimension basis mu order _ output input above]

/-- The mixing class occupies the same input-degree slice automatically. -/
def GeneratedScaleNormalization.mixingClass
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (mu : RenormalizationScale) (g : ℝ) (order loop : ℕ) (p : InvariantInsertionLabel G) :
    FilteredQuantum.H0 (family.ward mu) g (intrinsicEngineeringDimension p) :=
  family.observableClass mu g (N.mixingLabel mu order loop p)
    (intrinsicEngineeringDimension p)
    ((N.mixingLabel_dimension mu order loop p).trans (Nat.le_succ _))

end YangMills.PerturbativeFlow
