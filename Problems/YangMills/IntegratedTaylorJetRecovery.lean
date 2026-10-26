import Problems.YangMills.FilteredTaylorJets
import Problems.YangMills.FlowScaleConstancy
import Problems.YangMills.FlowNormalizationDilation

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem filteredTaylorPolynomial_complex_sum {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (D d : ℕ) (f : E → ℂ) (q : E) :
    filteredTaylorPolynomial D d f q =
      ∑ k ∈ Finset.range (D+1), if d+k ≤ D then
        (1 / (Nat.factorial k : ℂ)) * iteratedFDeriv ℝ k f 0 (fun _ => q) else 0 := by
  classical
  unfold filteredTaylorPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  unfold filteredTaylorSeries
  split_ifs
  · simp [ContinuousMultilinearMap.smul_apply, Complex.real_smul]
  · simp

/-- Conserving extension of the computed local density is the literal finite
Taylor polynomial of the SAME amplitude. No analytic regularity of F is used. -/
theorem reducedTaylorDensity_conserving_eq (D : ℕ) (F : OrderedAmplitude G)
    (smooth : ∀ labels, ContDiff ℝ ∞ (F labels))
    (extension : ∀ labels p, F labels p = F labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (hne : legs.length ≠ 0) (hD : legs.length ≤ D)
    (graded : ∀ π p, BalancedMomenta legs p →
      F (permutedLegs legs π) (permutedMomenta legs π p) =
        permutationSign legs π * F legs p) :
    (fun q => FullBV.densityAmplitude (reducedTaylorDensity D F) legs
      (conservingMomenta legs q)) = filteredTaylorPolynomial D (totalDimension legs) (F legs) := by
  funext q
  rw [reducedTaylorDensity_balanced_recovery D F smooth extension legs _ hne hD
    (conservingMomenta_balanced G legs q) graded, filteredTaylorPolynomial_complex_sum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · congr 1
    have ht := diagonalTaylor_of_radial (F legs) (F legs) (smooth _) (smooth _)
      (conservingMomenta legs q) q 1 k (by
        intro t
        have he := extension legs (t • q)
        rw [conservingMomenta_smul] at he
        simpa only [one_mul] using he.symm)
    simpa only [one_mul] using ht
  · rfl

theorem length_le_totalDimension (legs : List (ExternalLeg G)) :
    legs.length ≤ totalDimension legs := by
  induction legs with
  | nil => simp [totalDimension]
  | cons k rest ih =>
    have hk := external_dimension_pos k
    simp only [List.length_cons, totalDimension, List.map_cons, List.sum_cons] at *
    omega

/-- Actual subtraction-scale momentum jets of the computed density agree
with the SAME integrated amplitude through the prescribed weighted degree.
The density is first put on conserving momenta, as required by Eq94. -/
theorem reducedTaylorDensity_conserving_jets (D : ℕ) (F : OrderedAmplitude G)
    (smooth : ∀ labels, ContDiff ℝ ∞ (F labels))
    (extension : ∀ labels p, F labels p = F labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (hne : legs.length ≠ 0)
    (graded : ∀ π p, BalancedMomenta legs p →
      F (permutedLegs legs π) (permutedMomenta legs π p) =
        permutationSign legs π * F legs p)
    (directions : List (Fin legs.length × Fin 4))
    (degree : totalDimension legs + directions.length ≤ D) :
    momentumJet directions (fun q => FullBV.densityAmplitude (reducedTaylorDensity D F) legs
      (conservingMomenta legs q)) 0 = momentumJet directions (F legs) 0 := by
  have hD : legs.length ≤ D := (length_le_totalDimension legs).trans (by omega)
  rw [reducedTaylorDensity_conserving_eq D F smooth extension legs hne hD graded]
  unfold momentumJet
  rw [filteredTaylorPolynomial_jet D (totalDimension legs) (F legs) (smooth _)
    directions.length degree]

/-- Same integrated-family specialization at the actual subtraction scale,
valid for both dimension-four primitives and dimension-five Ward responses. -/
theorem integratedTaylorDensity_mu_jets (D : ℕ) (I : ScaleCouplingFamily G)
    (μ g : ℝ) (loop : ℕ) (UV : ℝ)
    (smooth : ∀ labels, ContDiff ℝ ∞ (I μ g loop μ UV labels))
    (extension : ∀ labels p, I μ g loop μ UV labels p =
      I μ g loop μ UV labels (conservingMomenta labels p))
    (legs : List (ExternalLeg G)) (hne : legs.length ≠ 0)
    (graded : ∀ π p, BalancedMomenta legs p →
      I μ g loop μ UV (permutedLegs legs π) (permutedMomenta legs π p) =
        permutationSign legs π * I μ g loop μ UV legs p)
    (directions : List (Fin legs.length × Fin 4))
    (degree : totalDimension legs + directions.length ≤ D) :
    momentumJet directions (fun q => FullBV.densityAmplitude
      (integratedTaylorDensity D I μ g loop UV) legs (conservingMomenta legs q)) 0 =
        momentumJet directions (I μ g loop μ UV legs) 0 := by
  exact reducedTaylorDensity_conserving_jets D (I μ g loop μ UV)
    smooth extension legs hne graded directions degree

end YangMills.IntegratedNormalization
