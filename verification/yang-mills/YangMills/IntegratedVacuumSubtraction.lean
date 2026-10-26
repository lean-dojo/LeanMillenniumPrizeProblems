import YangMills.IntegratedNormalizationProjectors

noncomputable section
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Remove only the zero-external-leg sector. Source integrated CACs have
their independent I functional for this sector; all nonempty kernels stay
literal equalities. -/
def subtractVacuum (F : FlowFamily G) : FlowFamily G :=
  fun loop Λ UV legs q => if legs = [] then 0 else F loop Λ UV legs q

@[simp] theorem subtractVacuum_empty (F : FlowFamily G) (loop : ℕ) (Λ UV : ℝ)
    (q : Fin ([] : List (ExternalLeg G)).length → Spacetime) :
    subtractVacuum F loop Λ UV [] q = 0 := by simp [subtractVacuum]

theorem subtractVacuum_nonempty (F : FlowFamily G) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (h : legs ≠ []) :
    subtractVacuum F loop Λ UV legs q = F loop Λ UV legs q := by
  simp only [subtractVacuum, if_neg h]

theorem linearFlowIntegrand_subtractVacuum (F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    linearFlowIntegrand (subtractVacuum F) loop Λ UV legs q p =
      linearFlowIntegrand F loop Λ UV legs q p := by
  simp only [linearFlowIntegrand, subtractVacuum,
    List.cons_ne_nil, if_false]

theorem quadraticSplit_subtractVacuum (L F : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) :
    quadraticSplit L (subtractVacuum F) loop leftLoop Λ UV legs q s =
      quadraticSplit L F loop leftLoop Λ UV legs q s := by
  simp only [quadraticSplit, subtractVacuum, List.cons_ne_nil, if_false]

theorem insertionHomogeneousRHS_subtractVacuum (L F : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    insertionHomogeneousRHS L (subtractVacuum F) loop Λ UV legs q =
      insertionHomogeneousRHS L F loop Λ UV legs q := by
  simp only [insertionHomogeneousRHS, linearFlowRHS, linearFlowIntegrand_subtractVacuum,
    quadraticFlowRHS, quadraticSplit_subtractVacuum]

/-- Actual nonempty coefficient projectors are unchanged by vacuum
subtraction, at every cutoff, independently of any μ normalization. -/
theorem extractCoefficient_subtractVacuum (F : FlowFamily G) (m : LocalMonomial G)
    (loop : ℕ) (Λ UV : ℝ) (q : Fin m.legs.length → Spacetime) (hm : m.legs ≠ []) :
    extractCoefficient m (subtractVacuum F loop Λ UV) q =
      extractCoefficient m (F loop Λ UV) q := by
  have hf : subtractVacuum F loop Λ UV m.legs = F loop Λ UV m.legs := by
    funext p
    exact subtractVacuum_nonempty F loop Λ UV m.legs p hm
  unfold extractCoefficient
  rw [hf]

def reducedPointwiseNormalizationResponse (L : ℝ → ℝ → InsertedFlowFamily G)
    (I : ScaleCouplingFamily G) (D : ℕ) : ScaleCouplingFamily G :=
  fun μ g => subtractVacuum (pointwiseNormalizationResponse L I D μ g)

theorem reducedPointwiseNormalizationResponse_normalized
    (L : ℝ → ℝ → InsertedFlowFamily G) (I : ScaleCouplingFamily G)
    (D : ℕ) (μ g UV : ℝ) (loop : ℕ) (output : LocalMonomial G)
    (h : SingleInsertionBoundaryConditions (L μ g) μ) (hUV : μ ≤ UV)
    (ho : output.Admissible) (hd : output.dimension ≤ D) (hn : output.legs ≠ []) :
    extractCoefficient output (reducedPointwiseNormalizationResponse L I D μ g loop μ UV) 0 =
      integratedTaylorJet D I μ g UV loop output := by
  rw [reducedPointwiseNormalizationResponse, extractCoefficient_subtractVacuum _ _ _ _ _ _ hn]
  exact pointwiseNormalizationResponse_normalized L I D μ g UV loop output h hUV ho hd

end YangMills.IntegratedNormalization
