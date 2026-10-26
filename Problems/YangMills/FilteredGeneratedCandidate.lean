import Problems.YangMills.FilteredQuantumRG
import Problems.YangMills.Statement
import Problems.YangMills.WightmanVacuumKernels

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Closed proposed filtered generated-sector specification

This assembly quantifies the required actual gauge groups and binds the
specified physical QFT and Hamiltonian to the SAME generated action,
renormalization, observables, UV/OPE and stress properties. Its source interpretation, normalization conventions and
witness constraints still require independent mathematical review. The fixed proposition
is defined separately in YangMillsSpecification. No existence proof is
supplied or assumed; external acceptance remains a separate question.

Nontriviality is not replaced by an extra Gaussianity test: the positive finite
physical spectral mass excludes a vacuum-only theory, while generated actual-G
short-distance correlations, same composite-only cyclicity and the generated
stress/charge equations are intended to provide Yang--Mills identification.
Their presence is not a theorem excluding every massive free or generalized-free
model from this full candidate. No such general exclusion is claimed here.
-/
noncomputable section
namespace YangMills
universe u
open Perturbative PerturbativeFlow

/-- All witnesses of the proposed simultaneous prescription for ONE actual G.
Every relation is fixed by the imported concrete definitions. Witnesses still
choose objects satisfying them; fixed constraints do not by themselves prove
that the resulting proposition is neither too weak nor too strong. -/
structure FilteredGeneratedCandidate (G : CompactSimpleGaugeGroup) where
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
  sector : FilteredRG.GeneratedSector wardFamily basis generated normalization
    kernels coefficients physicalCoefficients stress curvatureSquare

/-- Compatibility name for the same all-group assembly. The primary target is the separately named YangMillsExistenceAndMassGap
constant, with the reviewed source interpretation and universe contract. -/
def ProposedFilteredGeneratedSpecification : Prop :=
  ∀ G : CompactSimpleGaugeGroup.{u}, Nonempty (FilteredGeneratedCandidate G)

/-- The mass belongs to the same quantum theory whose fields occur in every
matching, local OPE, stress charge and vacuum-word condition of this candidate. -/
theorem FilteredGeneratedCandidate.qft_exists {G : CompactSimpleGaugeGroup}
    (candidate : FilteredGeneratedCandidate G) : QFTExistenceAndMassGap :=
  ⟨candidate.theory, candidate.qft_and_gap⟩

/-- Composite-only cyclicity, actual-group generated matching and physical
charges are already required; no unused independent Hilbert sector is appended.
In particular the generated stress cannot be zero in a candidate. -/
theorem FilteredGeneratedCandidate.stress_nonzero {G : CompactSimpleGaugeGroup}
    (candidate : FilteredGeneratedCandidate G) :
    ¬ (∀ μ ν f v, candidate.stress.field μ ν f v = 0) :=
  candidate.stress.not_zero_tensor_of_massGap candidate.sector.same_stress.1
    candidate.qft_and_gap

/-- The anomaly scalar is computed from the SAME running coupling and its
actual beta completion at the SAME reference, never supplied independently. -/
def FilteredGeneratedCandidate.traceAnomalyCoefficient {G : CompactSimpleGaugeGroup}
    (candidate : FilteredGeneratedCandidate G) : ℂ :=
  ((candidate.sector.matching.running.beta (candidate.sector.matching.running.coupling 0) /
    (2*candidate.stress.coupling.val^3) : ℝ) : ℂ)

/-- The assembled proposal fixes its entire trace equation modulo the
actual SAME-vacuum scalar. No new subtraction witness occurs here. -/
theorem FilteredGeneratedCandidate.trace_anomaly_computed_scalar {G : CompactSimpleGaugeGroup}
    (candidate : FilteredGeneratedCandidate G) :
    candidate.stress.actualTraceField =
      candidate.traceAnomalyCoefficient • candidate.composites.field candidate.stress.scale
        candidate.curvatureSquare +
      scalarIdentityField (actualVacuumOnePoint candidate.stress.actualTraceField -
        candidate.traceAnomalyCoefficient • actualVacuumOnePoint
          (candidate.composites.field candidate.stress.scale candidate.curvatureSquare)) := by
  exact ((candidate.stress.hasCenteredTraceAnomaly_iff_computed_scalar _ _).mp
    candidate.sector.same_stress.2.2.2.2).2

end YangMills
