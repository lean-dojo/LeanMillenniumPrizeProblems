import YangMills.GeneratedEuclideanCoefficients
import YangMills.MultiRenormalizationGroup

/-!
# Same-field matching to the generated Euclidean coefficients

This composition fixes the Euclidean series argument of every arity to the
actual lifted-extractor limits and physical recovery relation. The exact OPE,
Wick continuation, common RG transport and stress tensor all refer to the same
composite map on the same Wightman domain. Beta/gamma authorization and full
contact Ward restoration are still required before this fragment can enter a
complete YM target; this declaration does not conceal those obligations.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {QFT : WightmanData H}

/-- Concrete data-flow binding from the actual fixed group action through
corrected insertions and coefficient limits to the same physical OPE and
stress tensor. No separately chosen Euclidean perturbative series appears. -/
def GeneratedMultiSectorConditions {form : InvariantForm G} {e : ColorFrame form}
    (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (ward : QuantumWardLimit G)
    (transport : SameTheoryWardTransportData e (S.insertions S.referenceScale.val))
    {C : RenormalizedCompositeMap QFT G} (kernels : OPE.MultiKernels C)
    (basis : OPE.FilteredBasis G) (E : GeneratedEuclideanData basis)
    (betaSeries : ℕ → ℝ) (gammaSeries : ℕ → basis.Index → basis.Index → ℂ)
    (coeff : OPE.MultiCoefficients basis) (physical : ℕ → OPE.MultiCoefficients basis)
    (stress : StressTensorData QFT G C)
    (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  E.Compatible S lift W ward transport ∧
    RG.CoupledMultiSectorConditions kernels basis S.referenceScale form betaSeries gammaSeries
      coeff E.assembled physical stress curvatureSquare

end YangMills.PerturbativeFlow
