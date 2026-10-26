import Problems.YangMills.GeneratedEuclideanCoefficients
import Problems.YangMills.MultiWardRestoration
import Problems.YangMills.DistributionalCumulants
import Problems.YangMills.LocalContactRenormalization
import Problems.YangMills.JointCollisionScaling
import Problems.YangMills.InvariantPhysicalWords

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# One coherent scale family of generated Ward/contact distributions

All normalization scales use the same actual action/flow prescription.
Connected and disconnected contact values, finite local extension maps,
quantum cocycles, invariant-state null tests and coefficient recovery cannot
be chosen on separate engines. This is a definition of the central Ward/OPE
part, not an assertion that the boundary/limit problem has a solution.
Physical C/H reconstruction and RG scale-insertion authorization are separate.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Change only the scale at which generated coefficients are read. The
fixed action and all scale-dependent flow/insertion equations remain shared. -/
def FixedFlowSystem.atReference {B : InvariantForm G} {e : ColorFrame B}
    (S : FixedFlowSystem e) (mu : RenormalizationScale) : FixedFlowSystem e :=
  { S with referenceScale := mu }

/-- Concrete simultaneous restoration/extension data at EVERY scale.
The local contact coefficients have no spectator arguments; one common
analytic mollifier only defines tensor products of existing distributions. -/
structure LocalWardFlowFamily {B : InvariantForm G} {e : ColorFrame B}
    (S : FixedFlowSystem e) where
  continuum : RenormalizationScale → WardContinuumData G
  connected : RenormalizationScale → ConnectedWardData G
  singleTransport : (mu : RenormalizationScale) →
    SameTheoryWardTransportData e (S.insertions mu.val)
  ward : RenormalizationScale → QuantumWardLimit G
  pairCoefficient : RenormalizationScale → ℝ → ContactAnomalyCoefficients G
  pairWard : RenormalizationScale → ℝ → ContactAnomalyLimit G
  lift : RenormalizationScale → QuantumObservableLift G
  contactCounterterms : LocalContactCounterterms G
  mollifier : CompactJointMollifier
  full_ward : ∀ mu, FullMultiWardRestoration e (S.insertions mu.val)
    (S.oversubtractions mu.val) (continuum mu) (connected mu) (singleTransport mu)
    (pairCoefficient mu) (ward mu) (pairWard mu) (lift mu)
  local_extension : ∀ mu, LocalContactExtensionCompatible contactCounterterms
    (S.insertions mu.val) (S.oversubtractions mu.val) mu (continuum mu)
  same_cumulants : ∀ mu, DistributionalCumulantCompatibility mollifier (connected mu) (continuum mu)
  connected_scaling : ∀ mu isWard order loop n (labels : Fin (n + 1) → LocalMonomial G) legs,
    (∀ i, (labels i).Admissible) →
    JointPartialScalingBounds ((connected mu).physical isWard order loop labels legs) labels
      (if isWard then 1 else 0)
  moment_scaling : ∀ mu order loop n (labels : Fin (n + 1) → LocalMonomial G) legs,
    (∀ i, (labels i).Admissible) →
    JointPartialScalingBounds
      ((continuum mu).physical (.disconnected 0) order loop labels legs) labels
  physical_word_null : ∀ mu, InvariantPhysicalNullIdentity (continuum mu) (ward mu) (lift mu)
  physical_word_graph : ∀ mu order loop n (labels : Fin n → InvariantInsertionLabel G),
    order < 2 * loop → physicalInvariantWord (continuum mu) (lift mu) labels order loop = 0

/-- Generated raw limits and physical recovery use this exact family's
same-scale dictionary, anomaly map and continuum fields at every degree. -/
structure LocalWardCoefficientFamily {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S) (basis : OPE.FilteredBasis G) where
  data : RenormalizationScale → GeneratedEuclideanData basis
  compatible : ∀ mu, (data mu).Compatible (S.atReference mu) (family.lift mu)
    (family.continuum mu) (family.ward mu) (family.singleTransport mu)

end YangMills.PerturbativeFlow
