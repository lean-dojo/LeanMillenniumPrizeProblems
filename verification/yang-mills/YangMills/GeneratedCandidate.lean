import YangMills.GeneratedRenormalizedSector
import YangMills.Statement
import YangMills.WightmanVacuumKernels

/-!
# Closed proposed generated-sector specification, pending fidelity review

This outer assembly quantifies the actual required gauge groups and binds the
central generated sector to the SAME complete QFT and physical Hamiltonian.
It is a proposed mathematical statement, not the admitted Jaffe--Witten target:
the fixed auxiliary presentation's source adequacy and the outstanding cited-
standard/equivalence arguments are not proved. No existence proof is supplied
or required to review the meaning of this definition. Exact full admission
continues to reject the absent `YangMillsExistenceAndMassGap` declaration.

Nontriviality is not replaced by an extra Gaussianity test: the positive finite
physical spectral mass excludes a vacuum-only theory, while generated actual-G
short-distance correlations, same composite-only cyclicity and the generated
stress/charge equations do the Yang--Mills identification work.
-/
noncomputable section
namespace YangMills
universe u
open Perturbative PerturbativeFlow

/-- All witnesses of the proposed simultaneous prescription for ONE actual G.
Every relation is fixed by the imported concrete definitions. A witness cannot
supply a substitute meaning of Yang--Mills, prescribed OPE or physical mass. -/
structure GeneratedCandidate (G : CompactSimpleGaugeGroup) where
  theory : QuantumTheory
  qft_and_gap : GappedWightmanTheory theory.State theory.fields
  /-- Full tempered kernels of these very Q component words, fixed on a dense tensor span. -/
  vacuumKernels : WightmanVacuumKernels theory.fields
  form : InvariantForm G
  colorFrame : ColorFrame form
  engine : FixedFlowSystem colorFrame
  wardFamily : LocalWardFlowFamily engine
  basis : OPE.FilteredBasis G
  generated : LocalWardCoefficientFamily wardFamily basis
  normalization : GeneratedScaleNormalization wardFamily
  composites : RenormalizedCompositeMap theory.fields G
  kernels : OPE.MultiKernels composites
  coefficients : OPE.MultiCoefficients basis
  physicalCoefficients : ℕ → OPE.MultiCoefficients basis
  stress : StressTensorData theory.fields G composites
  curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G
  sector : GeneratedRenormalizedSector wardFamily basis generated normalization
    kernels coefficients physicalCoefficients stress curvatureSquare

/-- A closed PROPOSED statement; fidelity of its fixed auxiliary simultaneous
prescription remains unresolved. It is deliberately not an exact proof-
admission target and does not assert the existence of any candidate. -/
def ProposedGeneratedSpecification : Prop :=
  ∀ G : CompactSimpleGaugeGroup.{u}, Nonempty (GeneratedCandidate G)

/-- The mass belongs to the same quantum theory whose fields occur in every
matching, local OPE, stress charge and vacuum-word condition of this candidate. -/
theorem GeneratedCandidate.qft_exists {G : CompactSimpleGaugeGroup}
    (candidate : GeneratedCandidate G) : QFTExistenceAndMassGap :=
  ⟨candidate.theory, candidate.qft_and_gap⟩

/-- Composite-only cyclicity, actual-group generated matching and physical
charges are already required; no unused independent Hilbert sector is appended.
In particular the generated stress cannot be zero in a candidate. -/
theorem GeneratedCandidate.stress_nonzero {G : CompactSimpleGaugeGroup}
    (candidate : GeneratedCandidate G) :
    ¬ (∀ μ ν f v, candidate.stress.field μ ν f v = 0) :=
  candidate.stress.not_zero_tensor_of_massGap candidate.sector.same_stress.1
    candidate.qft_and_gap

end YangMills
