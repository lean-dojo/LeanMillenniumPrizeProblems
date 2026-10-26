import Problems.YangMills.GeneratedScaleNormalization
import Problems.YangMills.QuantumMixingCoordinates

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# The generated gamma column has the same quantum-label meaning

Finite classical coordinate resolution is linear by actual connection
independence. Therefore a computed mixing column is the coordinates of the
actual local mixing label, not an unrelated table. Reconstruction represents
the same generated quantum class; physical coefficient linearity comes from
the actual UV limits. This is not quantum injectivity or cohomological
uniqueness of the CS decomposition.
-/
noncomputable section
namespace YangMills.OPE
variable {G : CompactSimpleGaugeGroup}

def FilteredBasis.coordinatesLinearMap (B : FilteredBasis G) :
    CurvatureJetPolynomial.invariantAlgebra G →ₗ[ℝ] (B.Index →₀ ℝ) where
  toFun := B.classicalCoordinates
  map_add' p q := by
    apply B.coefficients_unique
    intro A x
    rw [B.classicalCoordinates_meaning, map_add,
      B.classicalCoordinates_meaning, B.classicalCoordinates_meaning]
    simp [CurvatureJetPolynomial.onConnection, CurvatureJetPolynomial.evaluate]
  map_smul' c p := by
    apply B.coefficients_unique
    intro A x
    rw [B.classicalCoordinates_meaning, map_smul, B.classicalCoordinates_meaning]
    simp [CurvatureJetPolynomial.onConnection, CurvatureJetPolynomial.evaluate]

/-- Coordinate reconstruction cannot loosen an intrinsic power-counting
bound merely by choosing a syntactically larger classical representative. -/
theorem FilteredBasis.reconstructedLabel_dimension (B : FilteredBasis G)
    (p : CurvatureJetPolynomial.invariantAlgebra G) :
    intrinsicEngineeringDimension (B.reconstructedLabel p) = intrinsicEngineeringDimension p := by
  classical
  have hq : Quotient.mk (CurvatureJetPolynomial.connectionSetoid G) (B.reconstructedLabel p) =
      Quotient.mk (CurvatureJetPolynomial.connectionSetoid G) p :=
    Quotient.sound (funext fun A => funext fun x => B.reconstructedLabel_sameOnConnections p A x)
  exact congrArg (fun o => Nat.find (CurvatureJetPolynomial.ConnectionObservable.finite_dimension o)) hq

end YangMills.OPE
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def GeneratedScaleNormalization.mixingLabel {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (mu : RenormalizationScale)
    (order loop : ℕ) (p : InvariantInsertionLabel G) : InvariantInsertionLabel G :=
  (N.mixing.coefficient mu.val order loop p).sum fun q c => c • q

/-- The matrix column is literally the coordinate vector of the actual
finite local mixing label, fixed by the same CS normalization. -/
theorem GeneratedScaleNormalization.gammaLoop_coordinates
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (order loop : ℕ) (output input : basis.Index) :
    basis.classicalCoordinates (N.mixingLabel mu order loop (basis.label input)) output =
      N.euclideanGammaLoop basis mu order loop output input := by
  classical
  change (basis.coordinatesLinearMap
    ((N.mixing.coefficient mu.val order loop (basis.label input)).sum fun q c => c • q)) output = _
  simp only [Finsupp.sum, map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, OPE.FilteredBasis.coordinatesLinearMap,
    GeneratedScaleNormalization.euclideanGammaLoop]
  rfl

/-- At every positive subtraction scale the reconstructed mixing column
represents the SAME generated-Q class of the actual local mixing label. -/
theorem GeneratedScaleNormalization.mixingLabel_quantum_class
    {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {family : LocalWardFlowFamily S} (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (order loop : ℕ) (p : InvariantInsertionLabel G) :
    SameQuantumLabelClass (family.ward mu) (family.lift mu)
      (basis.reconstructedLabel (N.mixingLabel mu order loop p))
      (N.mixingLabel mu order loop p) := by
  have compatible := N.same_scale_insertion.same_dictionary mu.val mu.property
  simp only [positiveScaleExtension, dif_pos mu.property] at compatible
  exact compatible.reconstructedLabel_class basis _

end YangMills.PerturbativeFlow
namespace YangMills
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G : CompactSimpleGaugeGroup} {Q : WightmanData H}

def RenormalizedCompositeMap.fieldLabelLinearMap (C : RenormalizedCompositeMap Q G)
    (mu : RenormalizationScale) : CurvatureJetPolynomial.invariantAlgebra G →ₗ[ℝ]
      (TestFunction →ₗ[ℂ] Q.domain →ₗ[ℂ] Q.domain) :=
  ((Finsupp.linearCombination ℂ Q.field).restrictScalars ℝ).comp (C.coefficients mu)

/-- Basis resolution acts on the actual SAME composite operators, not only
on classical labels or an unrelated formal state space. Quantum field
relations and redundant Q component vectors are allowed. -/
theorem RenormalizedCompositeMap.Compatible.coordinates_field
    {C : RenormalizedCompositeMap Q G} (hC : C.Compatible)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (p : CurvatureJetPolynomial.invariantAlgebra G) :
    C.field mu p = (basis.classicalCoordinates p).sum fun i c => c • C.field mu (basis.label i) := by
  classical
  rw [← hC.relations mu (basis.reconstructedLabel p) p
    (basis.reconstructedLabel_sameOnConnections p)]
  change C.fieldLabelLinearMap mu (basis.reconstructedLabel p) = _
  simp only [OPE.FilteredBasis.reconstructedLabel, Finsupp.sum, map_sum, map_smul]
  rfl

end YangMills
