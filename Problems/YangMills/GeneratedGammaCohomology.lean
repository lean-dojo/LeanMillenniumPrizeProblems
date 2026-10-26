import Problems.YangMills.QuantumLabelCohomology
import Problems.YangMills.GeneratedMixingMeaning

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Computed gamma columns are classes of the same local mixing insertions

This is the direct bridge from the computed same-engine CS normalization
to the actual all-hbar generated-Q quotient. The matrix resolves only the
invariant-label image; no basis of the entire quantum cohomology, quantum
injectivity, or nonperturbative ghost Hilbert-space quotient is assumed.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
open FilteredQuantum
variable {G : CompactSimpleGaugeGroup}

/-- The same Ward family's observable dictionary has a genuine class in its
own generated quantum complex at every positive normalization scale. -/
def LocalWardFlowFamily.observableClass {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S) (mu : RenormalizationScale)
    (g : ℝ) (p : InvariantInsertionLabel G) (d : ℕ)
    (bound : intrinsicEngineeringDimension p ≤ d+1) : H0 (family.ward mu) g d :=
  liftClass (family.full_ward mu).same_dictionary g p d bound

/-- Each coefficient of the generated gamma table resolves the quantum
class of the actual local mixing label. The SAME Q/lift belong to family,
and the SAME coordinates already act on its physical C fields. -/
theorem GeneratedScaleNormalization.gammaColumn_class
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale) (g : ℝ)
    (order loop : ℕ) (input : basis.Index) (d : ℕ)
    (bound : intrinsicEngineeringDimension (N.mixingLabel mu order loop (basis.label input)) ≤ d+1) :
    family.observableClass mu g (N.mixingLabel mu order loop (basis.label input)) d bound =
      ∑ i ∈ (basis.classicalCoordinates (N.mixingLabel mu order loop (basis.label input))).support.attach,
        PowerSeries.C (N.euclideanGammaLoop basis mu order loop i.val input : ℂ) •
          family.observableClass mu g (basis.label i.val) d
            ((basis.classicalCoordinates_degree _ i.val i.property).trans bound) := by
  have meaning := liftClass_coordinates (family.full_ward mu).same_dictionary basis
    (N.mixingLabel mu order loop (basis.label input)) g d bound
  simpa only [N.gammaLoop_coordinates] using! meaning

end YangMills.PerturbativeFlow
