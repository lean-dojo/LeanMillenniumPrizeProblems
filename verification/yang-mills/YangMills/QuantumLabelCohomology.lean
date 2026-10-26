import YangMills.FilteredQuantumCohomology
import YangMills.GeneratedMixingMeaning

/-!
# Existing quantum label relations descend to the actual generated H0

The SAME finite primitive in SameQuantumLabelClass is assembled into a full
formal hbar vector in the ghost-minus-one odd engineering slice. Exact
coefficient convolution and the actual support bounds prove its incoming
image is the difference of the two physical lift vectors. The relation thus
becomes equality in the existing H0 quotient; it is not an added cohomology
axiom or a new notion of physical nullity.

Classical equality on smooth connections descends through Compatible.relations.
Actual basis reconstruction then has the same class, and the class is proved
equal to the finite coordinate-weighted sum of the basis classes. These are
the coordinates used by GeneratedMixingMeaning.gammaLoop_coordinates; no
classical/quantum injectivity, surjectivity, or CS-classification theorem is
inferred. Existing files remain unchanged.
-/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace YangMills.PerturbativeFlow
namespace FilteredQuantum
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

instance h0AddCommGroup (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) : AddCommGroup (H0 Q g d) :=
  inferInstanceAs (AddCommGroup ((cocycles Q g d) ⧸ exactInside Q g d))

instance h0Module (Q : QuantumWardLimit G) (g : ℝ) (d : ℕ) : Module Scalar (H0 Q g d) :=
  inferInstanceAs (Module Scalar ((cocycles Q g d) ⧸ exactInside Q g d))

lemma primitive_convolution (Q : QuantumWardLimit G) (g : ℝ)
    (primitive : ℕ → LocalMonomial G →₀ ℂ) (A C : LocalMonomial G) (loop : ℕ) :
    PowerSeries.coeff loop (PowerSeries.mk (fun l => primitive l A) * series Q g A C) =
      ∑ l : Fin (loop+1), primitive l.val A * Q.coefficient g (loop-l.val) A C := by
  rw [PowerSeries.coeff_mul]
  simp only [series, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- The SAME primitive in SameQuantumLabelClass gives an actual full-hbar
boundary of the difference, without inventing a cohomology relation. -/
theorem relation_boundary {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    {p q : InvariantInsertionLabel G} (related : SameQuantumLabelClass Q lift p q)
    (g : ℝ) (d : ℕ) (hp : intrinsicEngineeringDimension p ≤ d+1)
    (hq : intrinsicEngineeringDimension q ≤ d+1) :
    ∃ v : Vector G d (-1) true,
      incoming Q g d v = liftVector lift g p d - liftVector lift g q d := by
  classical
  obtain ⟨primitive, support, _smooth, _grading, equation⟩ := related
  let v : Vector G d (-1) true := fun A => PowerSeries.mk (fun l => primitive g l A.val)
  refine ⟨v, ?_⟩
  have full_equation (loop : ℕ) (C : LocalMonomial G) (hc : C.Admissible) :
      lift.physicalCoefficient g p loop C - lift.physicalCoefficient g q loop C =
        ∑ l : Fin (loop+1), (primitive g l.val).sum (fun A c =>
          c * Q.coefficient g (loop-l.val) A C) := by
    by_cases bound : C.dimension ≤ max (intrinsicEngineeringDimension p) (intrinsicEngineeringDimension q)
    · exact equation g loop C hc bound
    · have zp : lift.physicalCoefficient g p loop C = 0 := by
        by_contra hn
        have hs := compatible.physical_support g p loop C hn
        have hx := le_max_left (intrinsicEngineeringDimension p) (intrinsicEngineeringDimension q)
        omega
      have zq : lift.physicalCoefficient g q loop C = 0 := by
        by_contra hn
        have hs := compatible.physical_support g q loop C hn
        have hx := le_max_right (intrinsicEngineeringDimension p) (intrinsicEngineeringDimension q)
        omega
      have rhs_zero : (∑ l : Fin (loop+1), (primitive g l.val).sum (fun A c =>
          c * Q.coefficient g (loop-l.val) A C)) = 0 := by
        apply Finset.sum_eq_zero
        intro l _hl
        unfold Finsupp.sum
        apply Finset.sum_eq_zero
        intro A ha
        have hs := support g l.val A (Finsupp.mem_support_iff.mp ha)
        have hzero : Q.coefficient g (loop-l.val) A C = 0 := by
          by_contra hn
          have ht := compatible.ward_filtered g (loop-l.val) A C hs.1 hn
          omega
        simp [hzero]
      rw [zp, zq, rhs_zero, sub_self]
  funext C
  apply PowerSeries.ext
  intro loop
  change PowerSeries.coeff loop
      (∑ A : Row G d (-1) true, series Q g A.val C.val * PowerSeries.mk (fun l => primitive g l A.val)) =
    PowerSeries.coeff loop
      (PowerSeries.mk (fun l => lift.physicalCoefficient g p l C.val) -
        PowerSeries.mk (fun l => lift.physicalCoefficient g q l C.val))
  rw [map_sub]
  simp only [PowerSeries.coeff_mk]
  rw [map_sum]
  simp_rw [mul_comm (series Q g _ C.val), primitive_convolution]
  rw [sum_rows d (-1) true (fun A => ∑ l : Fin (loop+1),
    primitive g l.val A * Q.coefficient g (loop-l.val) A C.val), Finset.sum_comm]
  have sums (l : Fin (loop+1)) :
      (∑ A ∈ rows G d (-1) true, primitive g l.val A * Q.coefficient g (loop-l.val) A C.val) =
      (primitive g l.val).sum (fun A c => c * Q.coefficient g (loop-l.val) A C.val) := by
    symm
    apply Finset.sum_subset
    · intro A ha
      have hs := support g l.val A (Finsupp.mem_support_iff.mp ha)
      apply (mem_rows (G := G) d (-1) true A).mpr
      exact ⟨hs.1, by omega, hs.2.2⟩
    · intro A _ha outside
      simp only [Finsupp.notMem_support_iff.mp outside, zero_mul]
  simp_rw [sums]
  have hc := (mem_rows (G := G) (d+1) 0 false C.val).mp C.property
  exact (full_equation loop C.val hc.1).symm

/-- Existing label equivalence is equality in the concrete quantum quotient. -/
theorem liftClass_eq_of_relation {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    {p q : InvariantInsertionLabel G} (related : SameQuantumLabelClass Q lift p q)
    (g : ℝ) (d : ℕ) (hp : intrinsicEngineeringDimension p ≤ d+1)
    (hq : intrinsicEngineeringDimension q ≤ d+1) :
    liftClass compatible g p d hp = liftClass compatible g q d hq := by
  obtain ⟨v, hv⟩ := relation_boundary compatible related g d hp hq
  apply (Submodule.Quotient.eq (exactInside Q g d)).mpr
  exact ⟨v, hv⟩

/-- Classical connection identities descend via the existing generated-Q
relation; no quantum injectivity or classical/quantum bijection is used. -/
theorem liftClass_eq_of_sameOnConnections {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    {p q : InvariantInsertionLabel G}
    (same : CurvatureJetPolynomial.sameOnConnections
      (p : CurvatureJetPolynomial G) (q : CurvatureJetPolynomial G))
    (g : ℝ) (d : ℕ) (hp : intrinsicEngineeringDimension p ≤ d+1)
    (hq : intrinsicEngineeringDimension q ≤ d+1) :
    liftClass compatible g p d hp = liftClass compatible g q d hq :=
  liftClass_eq_of_relation compatible (compatible.relations p q same) g d hp hq

/-- The actual classical coordinate reconstruction is the same class in
H0 of the same generated quantum differential. -/
theorem liftClass_reconstructed {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (basis : OPE.FilteredBasis G) (p : InvariantInsertionLabel G) (g : ℝ) (d : ℕ)
    (hp : intrinsicEngineeringDimension p ≤ d+1) :
    liftClass compatible g (basis.reconstructedLabel p) d
      (by rw [basis.reconstructedLabel_dimension]; exact hp) = liftClass compatible g p d hp :=
  liftClass_eq_of_relation compatible (compatible.reconstructedLabel_class basis p) g d
    (by rw [basis.reconstructedLabel_dimension]; exact hp) hp

/-- Coordinate resolution is an exact finite linear combination of the
same physical representatives even before quotienting by generated Q. -/
theorem liftVector_reconstructed {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (basis : OPE.FilteredBasis G) (p : InvariantInsertionLabel G) (g : ℝ) (d : ℕ) :
    liftVector lift g (basis.reconstructedLabel p) d =
      (basis.classicalCoordinates p).sum fun i c =>
        PowerSeries.C (c : ℂ) • liftVector lift g (basis.label i) d := by
  classical
  funext A
  apply PowerSeries.ext
  intro loop
  have equality := congrArg (fun v : LocalMonomial G →₀ ℂ => v A.val)
    (compatible.reconstructedLabel_coefficient basis p g loop)
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at equality
  simpa only [liftVector, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] using equality

/-- The coordinates used to form gamma reconstruct the actual H0 class as
a finite sum of basis classes. This is not quantum injectivity/surjectivity. -/
theorem liftClass_coordinates {B : InvariantForm G} {e : ColorFrame B}
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
    {lift : QuantumObservableLift G} (compatible : lift.Compatible e anomaly Q)
    (basis : OPE.FilteredBasis G) (p : InvariantInsertionLabel G) (g : ℝ) (d : ℕ)
    (hp : intrinsicEngineeringDimension p ≤ d+1) :
    liftClass compatible g p d hp =
      ∑ i ∈ (basis.classicalCoordinates p).support.attach,
        PowerSeries.C ((basis.classicalCoordinates p i.val : ℝ) : ℂ) •
          liftClass compatible g (basis.label i.val) d
            ((basis.classicalCoordinates_degree p i.val i.property).trans hp) := by
  classical
  have bound : intrinsicEngineeringDimension (basis.reconstructedLabel p) ≤ d+1 := by
    rw [basis.reconstructedLabel_dimension]
    exact hp
  have sum_cocycles :
      (∑ i ∈ (basis.classicalCoordinates p).support.attach,
        PowerSeries.C ((basis.classicalCoordinates p i.val : ℝ) : ℂ) •
          liftCocycle compatible g (basis.label i.val) d
            ((basis.classicalCoordinates_degree p i.val i.property).trans hp)) =
        liftCocycle compatible g (basis.reconstructedLabel p) d bound := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ i ∈ (basis.classicalCoordinates p).support.attach,
      PowerSeries.C ((basis.classicalCoordinates p i.val : ℝ) : ℂ) •
        liftVector lift g (basis.label i.val) d) = liftVector lift g (basis.reconstructedLabel p) d
    rw [Finset.sum_attach _ (fun i => PowerSeries.C ((basis.classicalCoordinates p i : ℝ) : ℂ) •
      liftVector lift g (basis.label i) d)]
    exact (liftVector_reconstructed compatible basis p g d).symm
  have quotient_sum := congrArg (fun v : cocycles Q g d => (exactInside Q g d).mkQ v) sum_cocycles
  simp only [map_sum, map_smul] at quotient_sum
  change (∑ i ∈ (basis.classicalCoordinates p).support.attach,
      PowerSeries.C ((basis.classicalCoordinates p i.val : ℝ) : ℂ) •
        liftClass compatible g (basis.label i.val) d
          ((basis.classicalCoordinates_degree p i.val i.property).trans hp)) =
      liftClass compatible g (basis.reconstructedLabel p) d bound at quotient_sum
  rw [liftClass_reconstructed compatible basis p g d hp] at quotient_sum
  exact quotient_sum.symm

end FilteredQuantum
end YangMills.PerturbativeFlow
