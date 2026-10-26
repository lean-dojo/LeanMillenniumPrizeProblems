import YangMills.OperatorProductExpansion

/-!
# Actual classical coordinates for physical mixing coefficients

Output labels of a generated mixing map must be resolved in the SAME
coherent basis used by the physical OPE/RG frames. Coordinates are fixed by
equality on every smooth connection. This is only classical independence;
no injectivity of the quantum composite map or physical BRST quotient is
asserted. The finite support retains the intrinsic engineering filtration.
-/
noncomputable section
namespace YangMills.OPE
variable {G : CompactSimpleGaugeGroup}

/-- Evaluation of a finite actual classical label combination. -/
def FilteredBasis.evaluateCoefficients (B : FilteredBasis G) (A : Connection G) (x : Spacetime) :
    (B.Index →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun i => (B.label i : CurvatureJetPolynomial G).onConnection A x

@[simp] theorem FilteredBasis.evaluateCoefficients_apply (B : FilteredBasis G)
    (A : Connection G) (x : Spacetime) (a : B.Index →₀ ℝ) :
    B.evaluateCoefficients A x a =
      a.sum (fun i c => c * (B.label i : CurvatureJetPolynomial G).onConnection A x) := by
  simp [evaluateCoefficients, Finsupp.linearCombination_apply, smul_eq_mul]

/-- The spanning witness is unique by actual connection independence, so
this choice does not introduce physical prediction freedom. -/
def FilteredBasis.classicalCoordinates (B : FilteredBasis G)
    (p : CurvatureJetPolynomial.invariantAlgebra G) : B.Index →₀ ℝ :=
  Classical.choose (B.spans p)

theorem FilteredBasis.classicalCoordinates_degree (B : FilteredBasis G)
    (p : CurvatureJetPolynomial.invariantAlgebra G) (i : B.Index)
    (hi : i ∈ (B.classicalCoordinates p).support) :
    dimension (B.label i) ≤ dimension p :=
  (Classical.choose_spec (B.spans p)).1 i hi

theorem FilteredBasis.classicalCoordinates_meaning (B : FilteredBasis G)
    (p : CurvatureJetPolynomial.invariantAlgebra G) (A : Connection G) (x : Spacetime) :
    B.evaluateCoefficients A x (B.classicalCoordinates p) =
      (p : CurvatureJetPolynomial G).onConnection A x := by
  simpa only [FilteredBasis.evaluateCoefficients_apply, classicalCoordinates] using
    ((Classical.choose_spec (B.spans p)).2 A x).symm

/-- Classical coordinate uniqueness, with no statement about quantum fields. -/
theorem FilteredBasis.coefficients_unique (B : FilteredBasis G) (a b : B.Index →₀ ℝ)
    (h : ∀ (A : Connection G) x, B.evaluateCoefficients A x a = B.evaluateCoefficients A x b) :
    a = b := by
  apply sub_eq_zero.mp
  apply B.independent
  intro A x
  change B.evaluateCoefficients A x (a - b) = 0
  rw [map_sub, h, sub_self]

/-- Identities on actual connections cannot change a mixing coefficient's
classical basis coordinates. Physical exact/null directions are not removed. -/
theorem FilteredBasis.classicalCoordinates_relations (B : FilteredBasis G)
    (p q : CurvatureJetPolynomial.invariantAlgebra G)
    (h : CurvatureJetPolynomial.sameOnConnections (p : CurvatureJetPolynomial G)
      (q : CurvatureJetPolynomial G)) : B.classicalCoordinates p = B.classicalCoordinates q := by
  apply B.coefficients_unique
  intro A x
  rw [B.classicalCoordinates_meaning, B.classicalCoordinates_meaning, h A x]

end YangMills.OPE
