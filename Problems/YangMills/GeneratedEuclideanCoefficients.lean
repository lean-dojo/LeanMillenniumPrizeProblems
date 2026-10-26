import Problems.YangMills.PerturbativeCoefficientLimits
import Problems.YangMills.LiftedCompositeExtraction
import Problems.YangMills.QuantumOutputRecovery
import Problems.YangMills.CollisionScaling

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Generated physical Euclidean OPE coefficients

The raw output vectors below are fixed by weak UV limits of the SAME lifted
insertion extractor. Physical output recovery uses the same corrected local
dictionary, generated quantum Ward map and continuum insertion fields. This
closes a data-flow gap: an arbitrary physical coefficient family cannot be
called perturbative YM without satisfying those concrete limit/recovery
relations. Existence, full contact Ward restoration, physical null-state
identification and RG authorization remain additional obligations.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The final point is the relative-coordinate origin in every arity. -/
def relativeLiftedCluster {n : ℕ} (labels : Fin n → InvariantInsertionLabel G)
    (last : InvariantInsertionLabel G) (r : OPE.RelativeSpace n) :
    LiftedInsertionCluster G :=
  ⟨List.ofFn (fun i => (labels i, r i)), (last, 0)⟩

/-- Actual coefficient of the corrected incoming product; the output is
still an actual local monomial, rather than an invariant polynomial dual. -/
def FixedFlowSystem.liftedRegulatedCoefficient {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    {n : ℕ} (labels : Fin n → InvariantInsertionLabel G)
    (last : InvariantInsertionLabel G) (output : LocalMonomial G)
    (loop : ℕ) (g UV : ℝ) (r : OPE.RelativeSpace n) : ℂ :=
  liftedRegulatedOPECoefficient lift (S.insertions S.referenceScale.val g)
    (S.oversubtractions S.referenceScale.val g) g S.referenceScale.val UV
    (relativeLiftedCluster labels last r) loop output

def FixedFlowSystem.liftedCouplingCoefficient {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    {n : ℕ} (labels : Fin n → InvariantInsertionLabel G)
    (last : InvariantInsertionLabel G) (output : LocalMonomial G)
    (loop order : ℕ) (UV : ℝ) (r : OPE.RelativeSpace n) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => S.liftedRegulatedCoefficient lift labels last output loop g UV r) 0

/-- Regularity and graph grading constrain the actual regulated extractor,
not a separately supplied family of predictions. Graph grading accounts for
canonical A_can versus source A=g A_can normalization of every input. -/
structure FixedFlowSystem.LiftedCoefficientRegularity {B : InvariantForm G}
    {e : ColorFrame B} (S : FixedFlowSystem e) (lift : QuantumObservableLift G) : Prop where
  coupling_smooth : ∀ n labels last output loop UV (r : OPE.RelativeSpace n),
    S.referenceScale.val < UV → (∀ i, r i ≠ 0) →
      (∀ i j, i ≠ j → r i ≠ r j) →
    ContDiff ℝ ∞ (fun g : ℝ => S.liftedRegulatedCoefficient lift labels last output loop g UV r)
  graph_grading : ∀ n labels last output loop UV g (r : OPE.RelativeSpace n),
    S.referenceScale.val < UV → (∀ i, r i ≠ 0) →
      (∀ i j, i ≠ j → r i ≠ r j) →
    S.liftedRegulatedCoefficient lift labels last output loop g UV r =
      (g : ℂ) ^ (output.legs.length + 2 * loop) *
        S.liftedRegulatedCoefficient lift labels last output loop 1 UV r
  test_integrable : ∀ n labels last output loop order UV (f : OPE.RelativeTest n),
    S.referenceScale.val < UV → OPE.MultiOffDiagonal f →
    Integrable (fun r => S.liftedCouplingCoefficient lift labels last output loop order UV r * f r)

/-- These remain auxiliary Euclidean coefficient distributions. They become
physical coefficients only through the concrete relation below. -/
structure GeneratedEuclideanData (basis : OPE.FilteredBasis G) where
  raw : (order loop n : ℕ) → (Fin n → basis.Index) → basis.Index →
    LocalMonomial G → OPE.MultiDistribution n
  physical : (order loop : ℕ) → OPE.MultiCoefficients basis

/-- Input engineering dimensions at all relative points, including the
anchored final point. -/
def clusterInputDegrees {basis : OPE.FilteredBasis G} {n : ℕ}
    (inputs : Fin n → basis.Index) (last : basis.Index) : Fin (n + 1) → ℕ :=
  fun i => if h : i.val < n then OPE.dimension (basis.label (inputs ⟨i.val, h⟩))
    else OPE.dimension (basis.label last)

/-- Fixed raw limits, coherent physical recovery in every finite filtration,
and local power counting on all collision strata. Contact Ward equations are
separate: power counting alone does not authorize a contact prescription.
No injectivity of the physical field correspondence is assumed. -/
structure GeneratedEuclideanData.Compatible {basis : OPE.FilteredBasis G}
    {B : InvariantForm G} {e : ColorFrame B} (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (transport : SameTheoryWardTransportData e (S.insertions S.referenceScale.val))
    (E : GeneratedEuclideanData basis) : Prop where
  same_flow_continuum : W.BulkCompatible (S.insertions S.referenceScale.val)
    (S.oversubtractions S.referenceScale.val)
  regularity : S.LiftedCoefficientRegularity lift
  raw_local : ∀ order loop n inputs last output,
    OPE.IsLocalMultiDistribution (E.raw order loop n inputs last output)
  raw_limit : ∀ order loop n inputs last output (f : OPE.RelativeTest n),
    OPE.MultiOffDiagonal f →
    Tendsto (fun UV => ∫ r, S.liftedCouplingCoefficient lift
      (fun i => basis.label (inputs i)) (basis.label last) output loop order UV r * f r)
      atTop (nhds (E.raw order loop n inputs last output f))
  physical_local : ∀ order loop n inputs last output,
    OPE.IsLocalMultiDistribution (E.physical order loop n inputs last output)
  physical_graph_order : ∀ order loop n inputs last output,
    order < 2 * loop → E.physical order loop n inputs last output = 0
  physical_power_counting : ∀ order loop n inputs last output,
    OPE.PartialScalingBounds (E.physical order loop n inputs last output)
      (clusterInputDegrees inputs last) (OPE.dimension (basis.label output))
  physical_recovery : ∀ n inputs last D (f : OPE.RelativeTest n),
    OPE.MultiOffDiagonal f →
    ∃ count : ℕ, ∃ index : Fin count → basis.Index,
      Function.Injective index ∧ Finset.univ.image index = basis.active D ∧
      QuantumPhysicalOutputRecovery e (S.insertions S.referenceScale.val) transport lift W Q D
        (fun i => basis.label (index i))
        (fun order loop m => E.raw order loop n inputs last m f)
        (fun order loop i => E.physical order loop n inputs last (index i) f)

/-- Setting hbar=1 is coefficientwise FINITE: a physical coefficient at loop
l starts at g^(2l). No unproved infinite sum or analytic resummation appears. -/
def GeneratedEuclideanData.assembled {basis : OPE.FilteredBasis G}
    (E : GeneratedEuclideanData basis) (order : ℕ) : OPE.MultiCoefficients basis :=
  fun n inputs last output =>
    ∑ loop ∈ Finset.range (order / 2 + 1), E.physical order loop n inputs last output

/-- Excluded loop orders vanish in the same physical family used in recovery.
The graph-order condition is essential: arbitrary formal hbar corrections
could otherwise leave infinitely many loops at a fixed coupling order. -/
theorem GeneratedEuclideanData.Compatible.excluded_loop
    {basis : OPE.FilteredBasis G} {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} {lift : QuantumObservableLift G}
    {W : WardContinuumData G} {Q : QuantumWardLimit G}
    {transport : SameTheoryWardTransportData e (S.insertions S.referenceScale.val)}
    {E : GeneratedEuclideanData basis} (h : E.Compatible S lift W Q transport)
    (order loop n : ℕ) (inputs : Fin n → basis.Index) (last output : basis.Index)
    (hexcluded : order / 2 < loop) : E.physical order loop n inputs last output = 0 := by
  apply h.physical_graph_order
  omega

end YangMills.PerturbativeFlow
