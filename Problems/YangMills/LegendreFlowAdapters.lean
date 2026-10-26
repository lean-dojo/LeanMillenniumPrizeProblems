import Problems.YangMills.LegendreQuadraticGraded
import Problems.YangMills.PerturbativeCoefficientLimits

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

theorem finiteInsertion_graded (L : ℝ → InsertedFlowFamily G)
    (graded : ∀ g m x loop Λ UV legs q (e : Equiv.Perm (Fin legs.length)),
      L g [⟨m,x⟩] loop Λ UV (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * L g [⟨m,x⟩] loop Λ UV legs q)
    (lift : QuantumObservableLift G) (g : ℝ) (p : InvariantInsertionLabel G) (x : Spacetime)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    lift.finiteInsertion (L g) g p x loop Λ UV (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * lift.finiteInsertion (L g) g p x loop Λ UV legs q := by
  simp only [QuantumObservableLift.finiteInsertion, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [graded]
  ring

theorem quantumExactInsertion_graded {B : InvariantForm G} (frame : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (μ : ℝ)
    (graded : ∀ g m x loop Λ UV legs q (e : Equiv.Perm (Fin legs.length)),
      L μ g [⟨m,x⟩] loop Λ UV (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * L μ g [⟨m,x⟩] loop Λ UV legs q)
    {degree offset : ℕ} (primitive : LocalScalePrimitive G degree offset)
    (g : ℝ) (x : Spacetime) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    quantumExactInsertion frame anomaly L primitive μ g x loop Λ UV
      (permutedLegs legs e) (permutedMomenta legs e q) =
    permutationSign legs e * quantumExactInsertion frame anomaly L primitive μ g x loop Λ UV legs q := by
  simp only [quantumExactInsertion, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro input _
  apply Finset.sum_congr rfl
  intro output _
  rw [graded]
  ring

/-- Corrected observables from this very S have computed directional
Legendre fidelity. The only extra background premise is the actual free
normalization, not a separately supplied inverse equation. -/
theorem fixedFlow_lift_directional {B : InvariantForm G} {frame : ColorFrame B}
    (S : FixedFlowSystem frame) (μ : ℝ) (positive : 0 < μ) (s : CutoffScales)
    (free : ∀ loop legs q, S.background μ 0 loop s.infrared s.ultraviolet legs q = 0)
    (lift : QuantumObservableLift G) (p : InvariantInsertionLabel G) (x : Spacetime) :
    DirectionalLegendreCompatible (S.background μ)
      (fun g => lift.finiteInsertion (S.insertions μ g) g p x) s := by
  apply directionalLegendreCompatible_from_source _ _ s free
  · intro g loop legs q e balanced
    exact S.background_equations.graded_symmetry μ g loop s.infrared s.ultraviolet legs q e balanced
  · intro g loop legs q e
    apply finiteInsertion_graded
    intro g m x loop Λ UV legs q e
    exact ((S.insertion_equations μ positive).per_coupling g).single_graded_symmetry
      m x loop Λ UV legs q e

theorem fixedFlow_exact_directional {B : InvariantForm G} {frame : ColorFrame B}
    (S : FixedFlowSystem frame) (μ : ℝ) (positive : 0 < μ) (s : CutoffScales)
    (free : ∀ loop legs q, S.background μ 0 loop s.infrared s.ultraviolet legs q = 0)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    {degree offset : ℕ} (primitive : LocalScalePrimitive G degree offset) (x : Spacetime) :
    DirectionalLegendreCompatible (S.background μ)
      (fun g => quantumExactInsertion frame anomaly S.insertions primitive μ g x) s := by
  apply directionalLegendreCompatible_from_source _ _ s free
  · intro g loop legs q e balanced
    exact S.background_equations.graded_symmetry μ g loop s.infrared s.ultraviolet legs q e balanced
  · intro g loop legs q e
    apply quantumExactInsertion_graded
    intro g m x loop Λ UV legs q e
    exact ((S.insertion_equations μ positive).per_coupling g).single_graded_symmetry
      m x loop Λ UV legs q e


/-- The free normalization already present in the background equations is
literally the free value of the same real source family. -/
theorem background_free_of_legendre (A : ℝ → FlowFamily G) (s : CutoffScales)
    (equations : AmputatedLegendreEquations (flowJet A s) s) :
    ∀ loop legs q, A 0 loop s.infrared s.ultraviolet legs q = 0 := by
  intro loop legs q
  simpa only [flowJet, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero,
    one_mul] using equations.2.1 loop legs q

theorem fixedFlow_lift_directional_of_legendre {B : InvariantForm G} {frame : ColorFrame B}
    (S : FixedFlowSystem frame) (μ : ℝ) (positive : 0 < μ) (s : CutoffScales)
    (background : AmputatedLegendreEquations (flowJet (S.background μ) s) s)
    (lift : QuantumObservableLift G) (p : InvariantInsertionLabel G) (x : Spacetime) :
    DirectionalLegendreCompatible (S.background μ)
      (fun g => lift.finiteInsertion (S.insertions μ g) g p x) s :=
  fixedFlow_lift_directional S μ positive s
    (background_free_of_legendre _ s background) lift p x

theorem fixedFlow_exact_directional_of_legendre {B : InvariantForm G} {frame : ColorFrame B}
    (S : FixedFlowSystem frame) (μ : ℝ) (positive : 0 < μ) (s : CutoffScales)
    (background : AmputatedLegendreEquations (flowJet (S.background μ) s) s)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    {degree offset : ℕ} (primitive : LocalScalePrimitive G degree offset) (x : Spacetime) :
    DirectionalLegendreCompatible (S.background μ)
      (fun g => quantumExactInsertion frame anomaly S.insertions primitive μ g x) s :=
  fixedFlow_exact_directional S μ positive s
    (background_free_of_legendre _ s background) anomaly primitive x

end YangMills.LegendreInsertionBridge
