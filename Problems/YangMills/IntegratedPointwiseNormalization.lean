import Problems.YangMills.ReducedTaylorDensity

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! A finite triangular normalization algorithm with coefficients computed
from actual integrated Taylor jets and the actual pointwise insertion
matrix. It does not replace source123 by a false Kronecker identity. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- The actual full-independent-momentum pointwise normalization matrix.
Only its equal-or-lower-degree rows are Kronecker normalized by source4.2. -/
def pointwiseJetMatrix (L : InsertedFlowFamily G) (μ UV : ℝ) (loop : ℕ)
    (output input : LocalMonomial G) : ℂ :=
  extractCoefficient output (L [⟨input, 0⟩] loop μ UV) 0

/-- Finite superalgebraic Taylor target obtained from the integrated
response, rather than witness-chosen mixing coefficients. -/
def integratedTaylorJet (D : ℕ) (I : ScaleCouplingFamily G) (μ g UV : ℝ)
    (loop : ℕ) (m : LocalMonomial G) : ℂ :=
  extractCoefficient m
    (FullBV.densityAmplitude (integratedTaylorDensity D I μ g loop UV)) 0

/-- Solve by ascending engineering degree. Lower-degree pointwise
insertions may have nonzero irrelevant higher-degree jets; their actual
matrix entries are explicitly subtracted. Every loop sum is finite. -/
def normalizationCoefficient (L : InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (m : LocalMonomial G) : ℂ := by
  classical
  exact if ¬m.Admissible ∨ D < m.dimension then 0 else
    integratedTaylorJet D I μ g UV loop m -
      ∑ c ∈ (monomialsBelow G m.dimension).attach,
        ∑ r ∈ Finset.range (loop+1),
          normalizationCoefficient L I D μ g UV r c.val *
            pointwiseJetMatrix L μ UV (loop-r) m c.val
termination_by m.dimension
decreasing_by
  exact dimension_lt_of_mem_monomialsBelow c.property

/-- The constructed finite pointwise response is tied to the SAME local
insertion amplitudes; there is no additional renormalized kernel witness. -/
def pointwiseNormalizationResponse (L : ℝ → ℝ → InsertedFlowFamily G)
    (I : ScaleCouplingFamily G) (D : ℕ) : ScaleCouplingFamily G :=
  fun μ g loop Λ UV legs q => ∑ m ∈ monomialsBelow G (D+1),
    ∑ r ∈ Finset.range (loop+1),
      normalizationCoefficient (L μ g) I D μ g UV r m *
        L μ g [⟨m, 0⟩] (loop-r) Λ UV legs q

/-- The remaining comparison is an explicit computed balanced kernel.
Its vanishing requires the Fourier/Taylor reconstruction and actual
linear-flow uniqueness theorem, not an interpretation field. -/
def integratedPointwiseResidual (L : ℝ → ℝ → InsertedFlowFamily G)
    (I : ScaleCouplingFamily G) (D : ℕ) : ScaleCouplingFamily G :=
  fun μ g loop Λ UV legs q => I μ g loop Λ UV legs q -
    pointwiseNormalizationResponse L I D μ g loop Λ UV legs (conservingMomenta legs q)

theorem pointwiseJetMatrix_normalized (L : InsertedFlowFamily G) (μ UV : ℝ)
    (h : SingleInsertionBoundaryConditions L μ) (hUV : μ ≤ UV)
    (output input : LocalMonomial G) (ho : output.Admissible) (hi : input.Admissible)
    (hd : output.dimension ≤ input.dimension) (loop : ℕ) :
    pointwiseJetMatrix L μ UV loop output input =
      if input = output ∧ loop = 0 then 1 else 0 :=
  h.normalized input output hi ho hd loop UV hUV

theorem normalizationCoefficient_outside (L : InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (m : LocalMonomial G)
    (h : ¬m.Admissible ∨ D < m.dimension) :
    normalizationCoefficient L I D μ g UV loop m = 0 := by
  rw [normalizationCoefficient, if_pos h]

/-- Exact scalar equation solved by the finite recursion. A global
normalization identity additionally uses the proved source matrix rows
above and the Taylor reconstruction theorem. -/
theorem normalizationCoefficient_equation (L : InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (m : LocalMonomial G)
    (ha : m.Admissible) (hd : m.dimension ≤ D) :
    normalizationCoefficient L I D μ g UV loop m +
      (∑ c ∈ (monomialsBelow G m.dimension).attach,
        ∑ r ∈ Finset.range (loop+1),
          normalizationCoefficient L I D μ g UV r c.val *
            pointwiseJetMatrix L μ UV (loop-r) m c.val) =
        integratedTaylorJet D I μ g UV loop m := by
  classical
  rw [normalizationCoefficient, if_neg (by simp [ha, not_lt.mpr hd])]
  exact sub_add_cancel _ _

attribute [local irreducible] monomialsBelow integratedTaylorJet

/-- Unit-triangular part of the ACTUAL pointwise matrix. This is precisely
the part controlled by source4.2; irrelevant rows are not discarded. -/
theorem normalizationContribution_upper (L : InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (output input : LocalMonomial G)
    (h : SingleInsertionBoundaryConditions L μ) (hUV : μ ≤ UV)
    (ho : output.Admissible) (hi : input.Admissible)
    (hd : output.dimension ≤ input.dimension) :
    (∑ r ∈ Finset.range (loop+1),
      normalizationCoefficient L I D μ g UV r input *
        pointwiseJetMatrix L μ UV (loop-r) output input) =
      if input = output then normalizationCoefficient L I D μ g UV loop output else 0 := by
  classical
  by_cases he : input = output
  · subst input
    rw [if_pos rfl]
    calc
      _ = normalizationCoefficient L I D μ g UV loop output *
          pointwiseJetMatrix L μ UV (loop-loop) output output := by
        apply Finset.sum_eq_single loop
        · intro r hr hne
          have hr' := Finset.mem_range.mp hr
          have hn : loop-r ≠ 0 := by omega
          rw [pointwiseJetMatrix_normalized L μ UV h hUV output output ho ho le_rfl,
            if_neg (by simp [hn]), mul_zero]
        · intro hn
          exact False.elim (hn (Finset.mem_range.mpr (by omega)))
      _ = _ := by
        rw [pointwiseJetMatrix_normalized L μ UV h hUV output output ho ho le_rfl]
        simp
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro r hr
    rw [pointwiseJetMatrix_normalized L μ UV h hUV output input ho hi hd,
      if_neg (by simp [he]), mul_zero]

/-- The fixed scalar projector of the constructed finite response. -/
def normalizationMatrixValue (L : InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (output : LocalMonomial G) : ℂ :=
  ∑ input ∈ monomialsBelow G (D+1), ∑ r ∈ Finset.range (loop+1),
    normalizationCoefficient L I D μ g UV r input *
      pointwiseJetMatrix L μ UV (loop-r) output input

/-- The finite triangular algorithm solves ALL actual scalar jet rows
through degree D. This theorem uses only the source pointwise boundary
normalizations, not a separately supplied inverse matrix. -/
theorem normalizationMatrixValue_eq (L : InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (output : LocalMonomial G)
    (h : SingleInsertionBoundaryConditions L μ) (hUV : μ ≤ UV)
    (ho : output.Admissible) (hd : output.dimension ≤ D) :
    normalizationMatrixValue L I D μ g UV loop output =
      integratedTaylorJet D I μ g UV loop output := by
  classical
  let S := monomialsBelow G (D+1)
  let lower := monomialsBelow G output.dimension
  let T (input : LocalMonomial G) : ℂ :=
    ∑ r ∈ Finset.range (loop+1),
      normalizationCoefficient L I D μ g UV r input *
        pointwiseJetMatrix L μ UV (loop-r) output input
  let Z := normalizationCoefficient L I D μ g UV loop output
  have hsub : lower ⊆ S := by
    intro input hi
    obtain ⟨ha, hlt⟩ := (mem_monomialsBelow_iff output.dimension input).mp hi
    exact (mem_monomialsBelow_iff (D+1) input).mpr ⟨ha, by omega⟩
  have hout : output ∈ S := (mem_monomialsBelow_iff (D+1) output).mpr ⟨ho, by omega⟩
  have hp (input : LocalMonomial G) (hin : input ∈ S) :
      T input = (if input ∈ lower then T input else 0) + if input = output then Z else 0 := by
    by_cases hi : input ∈ lower
    · have hlt := ((mem_monomialsBelow_iff output.dimension input).mp hi).2
      have he : input ≠ output := by
        intro he
        exact (ne_of_lt hlt) (congrArg LocalMonomial.dimension he)
      simp only [if_pos hi, if_neg he, add_zero]
    · have hiA := (mem_monomialsBelow_iff (D+1) input).mp hin
      have hdim : output.dimension ≤ input.dimension := by
        by_contra hn
        exact hi ((mem_monomialsBelow_iff output.dimension input).mpr ⟨hiA.1, by omega⟩)
      have hu := normalizationContribution_upper L I D μ g UV loop output input h hUV ho hiA.1 hdim
      change T input = if input = output then Z else 0 at hu
      simpa only [hi, if_false, zero_add] using hu
  have hlow : (∑ input ∈ S, if input ∈ lower then T input else 0) = ∑ input ∈ lower, T input := by
    have hs : (∑ input ∈ lower, if input ∈ lower then T input else 0) =
        ∑ input ∈ S, if input ∈ lower then T input else 0 :=
      Finset.sum_subset hsub (by intro input hi hn; simp [hn])
    rw [← hs]
    apply Finset.sum_congr rfl
    intro input hi
    simp [hi]
  have hrec : Z + (∑ input ∈ lower, T input) = integratedTaylorJet D I μ g UV loop output := by
    have hr := normalizationCoefficient_equation L I D μ g UV loop output ho hd
    change Z + (∑ c ∈ lower.attach, T c.val) = _ at hr
    rw [Finset.sum_attach lower T] at hr
    exact hr
  change (∑ input ∈ S, T input) = _
  calc
    _ = ∑ input ∈ S,
        ((if input ∈ lower then T input else 0) + if input = output then Z else 0) := by
      apply Finset.sum_congr rfl
      exact hp
    _ = (∑ input ∈ lower, T input) + Z := by
      rw [Finset.sum_add_distrib, hlow]
      simp [hout]
    _ = _ := by rw [add_comm]; exact hrec

end YangMills.IntegratedNormalization
