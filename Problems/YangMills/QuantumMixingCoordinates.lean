import Problems.YangMills.InvariantBasisCoordinates
import Problems.YangMills.QuantumObservableLift

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Classical mixing coordinates represent the same generated quantum class

Reconstruction is in the actual classical basis modulo equality on smooth
connections. The quantum assertion uses exactly the existing same-generated-Q
relation; it does not assert quantum injectivity or erase exact directions.
Physical coefficient linearity is derived from the finite-cutoff linearity
and uniqueness of the actual coefficient limits.
-/
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open Filter
namespace YangMills.OPE
variable {G : CompactSimpleGaugeGroup}

def FilteredBasis.reconstructedLabel (B : FilteredBasis G)
    (p : CurvatureJetPolynomial.invariantAlgebra G) :
    CurvatureJetPolynomial.invariantAlgebra G :=
  (B.classicalCoordinates p).sum fun i c => c • B.label i

theorem FilteredBasis.reconstructedLabel_sameOnConnections (B : FilteredBasis G)
    (p : CurvatureJetPolynomial.invariantAlgebra G) :
    CurvatureJetPolynomial.sameOnConnections
      (B.reconstructedLabel p : CurvatureJetPolynomial G) (p : CurvatureJetPolynomial G) := by
  intro A x
  rw [← B.classicalCoordinates_meaning p A x]
  simp [reconstructedLabel, FilteredBasis.evaluateCoefficients_apply,
    Finsupp.sum, CurvatureJetPolynomial.onConnection, CurvatureJetPolynomial.evaluate,
    map_sum]

end YangMills.OPE
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem QuantumObservableLift.Compatible.reconstructedLabel_class
    {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (h : lift.Compatible e anomaly Q)
    (basis : OPE.FilteredBasis G) (p : InvariantInsertionLabel G) :
    SameQuantumLabelClass Q lift (basis.reconstructedLabel p) p :=
  h.relations _ _ (basis.reconstructedLabel_sameOnConnections p)

theorem QuantumObservableLift.Compatible.physicalCoefficient_add
    {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (h : lift.Compatible e anomaly Q)
    (g : ℝ) (p q : InvariantInsertionLabel G) (loop : ℕ) :
    lift.physicalCoefficient g (p + q) loop =
      lift.physicalCoefficient g p loop + lift.physicalCoefficient g q loop := by
  ext m
  apply tendsto_nhds_unique (h.coefficient_limit g (p+q) loop m)
  have limits := (h.coefficient_limit g p loop m).add (h.coefficient_limit g q loop m)
  simpa only [← Finsupp.add_apply, ← h.linear_add] using limits

theorem QuantumObservableLift.Compatible.physicalCoefficient_smul
    {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (h : lift.Compatible e anomaly Q)
    (g : ℝ) (c : ℝ) (p : InvariantInsertionLabel G) (loop : ℕ) :
    lift.physicalCoefficient g (c • p) loop = (c : ℂ) • lift.physicalCoefficient g p loop := by
  ext m
  apply tendsto_nhds_unique (h.coefficient_limit g (c • p) loop m)
  have limits := (h.coefficient_limit g p loop m).const_mul (c : ℂ)
  simpa only [← smul_eq_mul, ← Finsupp.smul_apply, ← h.linear_smul] using limits

theorem QuantumObservableLift.Compatible.physicalCoefficient_zero
    {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (h : lift.Compatible e anomaly Q)
    (g : ℝ) (loop : ℕ) : lift.physicalCoefficient g 0 loop = 0 := by
  simpa using h.physicalCoefficient_smul g 0 0 loop

/-- Finite classical linear combinations are represented by the actual
finite combination of physical lift coefficients, not chosen afresh. -/
theorem QuantumObservableLift.Compatible.physicalCoefficient_finset_sum
    {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (h : lift.Compatible e anomaly Q)
    {ι : Type*} (s : Finset ι) (p : ι → InvariantInsertionLabel G)
    (c : ι → ℝ) (g : ℝ) (loop : ℕ) :
    lift.physicalCoefficient g (∑ i ∈ s, c i • p i) loop =
      ∑ i ∈ s, (c i : ℂ) • lift.physicalCoefficient g (p i) loop := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.physicalCoefficient_zero g loop
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [h.physicalCoefficient_add, h.physicalCoefficient_smul, ih]

/-- Consequently the coordinates used in generated gamma reconstruct the
physical local representative modulo exactly the SAME generated Q relation. -/
theorem QuantumObservableLift.Compatible.reconstructedLabel_coefficient
    {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (h : lift.Compatible e anomaly Q)
    (basis : OPE.FilteredBasis G) (p : InvariantInsertionLabel G) (g : ℝ) (loop : ℕ) :
    lift.physicalCoefficient g (basis.reconstructedLabel p) loop =
      (basis.classicalCoordinates p).sum fun i c =>
        (c : ℂ) • lift.physicalCoefficient g (basis.label i) loop := by
  unfold OPE.FilteredBasis.reconstructedLabel Finsupp.sum
  exact h.physicalCoefficient_finset_sum _ basis.label (basis.classicalCoordinates p) g loop

end YangMills.PerturbativeFlow
