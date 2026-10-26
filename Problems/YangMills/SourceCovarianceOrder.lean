import Problems.YangMills.PerturbativeFlow
import Problems.YangMills.FullBV

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
The printed FHH (67) matrix is indexed (A,c,cbar,B). This module states
its entries without conflating that matrix index order with the order of
iterated LEFT differentiation. The transpose comparison below is finite
algebra only; it does not silently identify the whole source prescription.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- FHH (67) in the explicitly named basic species, at xi=1. -/
def printedSourceCovariance (s : CutoffScales) (K L : BasicField G) (p : Spacetime) : ℝ :=
  match K,L with
  | .gauge mu a,.gauge nu b => if a=b ∧ mu=nu then flowCovariance s p else 0
  | .ghost a,.antighost b => if a=b then -flowCovariance s p else 0
  | .antighost a,.ghost b => if a=b then flowCovariance s p else 0
  | .auxiliary a,.auxiliary b => if a=b then euclideanSquare p * flowCovariance s p else 0
  | _,_ => 0

/-- The apparent ghost-sign discrepancy is exactly matrix transposition;
there is no discrepancy in the gauge or shifted auxiliary sectors. -/
theorem printedSourceCovariance_eq_transpose (s : CutoffScales)
    (K L : BasicField G) (p : Spacetime) :
    printedSourceCovariance s K L p = basicCovariance s L K p := by
  cases K <;> cases L <;> simp [printedSourceCovariance,basicCovariance,eq_comm]

/-- Reversing the two derivative slots at the same time as transposing the
kernel preserves the COMPLETE finite contraction, including ghost species.
No commutation of odd derivatives is assumed in this change of dummy indices. -/
theorem printedSourceCovariance_ordered_contraction (s : CutoffScales)
    (p : Spacetime) (twoDerivatives : BasicField G → BasicField G → ℂ) :
    (∑ K : BasicField G, ∑ L : BasicField G,
      (printedSourceCovariance s K L p : ℂ) * twoDerivatives L K) =
    ∑ K : BasicField G, ∑ L : BasicField G,
      (basicCovariance s K L p : ℂ) * twoDerivatives K L := by
  simp_rw [printedSourceCovariance_eq_transpose]
  exact Finset.sum_comm

/-- The same source matrix orientation for the actual flow derivative. -/
def printedSourceDerivativeCovariance (scale : ℝ) (K L : BasicField G) (p : Spacetime) : ℝ :=
  match K,L with
  | .gauge mu a,.gauge nu b => if a=b ∧ mu=nu then flowDerivativeKernel scale p else 0
  | .ghost a,.antighost b => if a=b then -flowDerivativeKernel scale p else 0
  | .antighost a,.ghost b => if a=b then flowDerivativeKernel scale p else 0
  | .auxiliary a,.auxiliary b => if a=b then euclideanSquare p * flowDerivativeKernel scale p else 0
  | _,_ => 0

theorem printedSourceDerivativeCovariance_eq_transpose (scale : ℝ)
    (K L : BasicField G) (p : Spacetime) :
    printedSourceDerivativeCovariance scale K L p = basicDerivativeCovariance scale L K p := by
  cases K <;> cases L <;> simp [printedSourceDerivativeCovariance,basicDerivativeCovariance,eq_comm]

end YangMills.PerturbativeFlow

namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

/-- A displayed operator product D_j1 D_j2 ... acts on its argument
rightmost first, as in FHH (86). This differs from a list of successive
operations in their chronological order. -/
def printedLeftDerivativeWord : List (Jet G) → JetAlgebra G →ₗ[ℂ] JetAlgebra G
  | [] => LinearMap.id
  | j :: rest => (leftPartialJet j).comp (printedLeftDerivativeWord rest)

lemma externalJetDerivative_append (first last : List (Jet G)) :
    externalJetDerivative (first ++ last) =
      (externalJetDerivative last).comp (externalJetDerivative first) := by
  induction first with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.cons_append,externalJetDerivative,ih,LinearMap.comp_assoc]

/-- Exact conversion of the source's written product of left derivatives
to the actual implementation, at EVERY arity and for ALL antifields. -/
theorem printedLeftDerivativeWord_eq_reverse (jets : List (Jet G)) :
    printedLeftDerivativeWord jets = externalJetDerivative jets.reverse := by
  induction jets with
  | nil => rfl
  | cons j rest ih =>
    simp only [printedLeftDerivativeWord,List.reverse_cons,externalJetDerivative_append,ih]
    rfl

/-- The source covariance orientation and source derivative product
translate together. This proves equality of the actual superjet Gaussian
contraction operators, not only a scalar matrix transposition. -/
theorem printedGaussianContraction_eq (s : Perturbative.CutoffScales)
    (p : Spacetime) (P : JetAlgebra G) :
    (∑ K : Perturbative.BasicField G, ∑ L : Perturbative.BasicField G,
      ((PerturbativeFlow.printedSourceCovariance s K L p : ℝ) : ℂ) •
        printedLeftDerivativeWord [⟨.inl K,0⟩,⟨.inl L,0⟩] P) =
    ∑ K : Perturbative.BasicField G, ∑ L : Perturbative.BasicField G,
      ((Perturbative.basicCovariance s K L p : ℝ) : ℂ) •
        externalJetDerivative [⟨.inl K,0⟩,⟨.inl L,0⟩] P := by
  simp_rw [PerturbativeFlow.printedSourceCovariance_eq_transpose]
  rw [Finset.sum_comm]
  rfl

/-- The same complete contraction identity for the actual scale derivative
used in the finite flow equation (75). -/
theorem printedGaussianFlowContraction_eq (scale : ℝ)
    (p : Spacetime) (P : JetAlgebra G) :
    (∑ K : Perturbative.BasicField G, ∑ L : Perturbative.BasicField G,
      ((PerturbativeFlow.printedSourceDerivativeCovariance scale K L p : ℝ) : ℂ) •
        printedLeftDerivativeWord [⟨.inl K,0⟩,⟨.inl L,0⟩] P) =
    ∑ K : Perturbative.BasicField G, ∑ L : Perturbative.BasicField G,
      ((PerturbativeFlow.basicDerivativeCovariance scale K L p : ℝ) : ℂ) •
        externalJetDerivative [⟨.inl K,0⟩,⟨.inl L,0⟩] P := by
  simp_rw [PerturbativeFlow.printedSourceDerivativeCovariance_eq_transpose]
  rw [Finset.sum_comm]
  rfl

/-- Source (87) uses exp(+ipx); the implementation uses exp(-ipx).
Every ordinary jet phase is transported by the SAME p to -p substitution. -/
def printedJetMomentumPhase (j : Jet G) (p : Spacetime) : ℂ :=
  ∏ mu : Fin 4, (Complex.I * (p mu : ℂ)) ^ j.derivative mu

theorem printedJetMomentumPhase_eq (j : Jet G) (p : Spacetime) :
    printedJetMomentumPhase j p = jetMomentumPhase j (-p) := by
  unfold printedJetMomentumPhase jetMomentumPhase
  congr 1
  funext mu
  simp only [Pi.neg_apply,Complex.ofReal_neg,neg_mul_neg]

/-- Literal all-arity derivative/phase conversion on a coefficient term.
It applies to every SAME master-action polynomial and all antifield jets. -/
theorem printedCoefficientTerm_eq {n : ℕ} (jets : Fin n → Jet G)
    (q : Fin n → Spacetime) (P : JetAlgebra G) :
    augmentation (printedLeftDerivativeWord (List.ofFn jets) P) *
        (∏ i : Fin n, printedJetMomentumPhase (jets i) (q i)) =
      augmentation (externalJetDerivative (List.ofFn jets).reverse P) *
        (∏ i : Fin n, jetMomentumPhase (jets i) (-q i)) := by
  rw [printedLeftDerivativeWord_eq_reverse]
  simp_rw [printedJetMomentumPhase_eq]

end YangMills.FullBV
