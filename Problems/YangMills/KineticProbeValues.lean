import Problems.YangMills.WardActionCoordinates

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace YangMills.WardAction
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}
@[simp] private theorem sum_flatMap' {α : Type*} (l : List α) (f : α → List ℂ) :
    (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]
@[simp] private theorem sum_map_flatMap' {α β : Type*} (l : List α) (f : α → List β) (g : β → ℂ) :
    ((l.flatMap f).map g).sum = (l.map (fun x => ((f x).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]
@[simp] private theorem sum_map_finRange' (n : ℕ) (f : Fin n → ℂ) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  simpa [List.finRange, List.map_ofFn] using! (List.sum_ofFn (f := f))

theorem ghostKinetic_amplitude {B : InvariantForm G} (e : ColorFrame B)
    (a : Fin G.dimension) (q : Fin 2 → Spacetime) :
    basisAmplitude e .ghostKinetic [.inl (.antighost a), .inl (.ghost a)] q =
      -∑ μ : Fin 4, (q 0 μ : ℂ) * (q 1 μ : ℂ) := by
  unfold basisAmplitude basisVertices ghostKineticVertices localPolynomialAmplitude
  simp [localVertexAmplitude, localMonomialDerivative, List.ofFn_succ,
    ExternalLeg.parity, BasicField.fermionic, Fin.sum_univ_succ,
    Finset.sum_neg_distrib]
  ring_nf
  simp
  ring

theorem gluonKinetic_amplitude {B : InvariantForm G} (e : ColorFrame B)
    (a : Fin G.dimension) (q : Fin 2 → Spacetime) :
    basisAmplitude e .gluonKinetic [.inl (.gauge 1 a), .inl (.gauge 1 a)] q =
      -(∑ μ : Fin 4, (q 0 μ : ℂ) * (q 1 μ : ℂ)) +
        (q 0 1 : ℂ) * (q 1 1 : ℂ) := by
  unfold basisAmplitude basisVertices gluonKineticVertices localPolynomialAmplitude
  simp [localVertexAmplitude, localMonomialDerivative, List.ofFn_succ,
    ExternalLeg.parity, BasicField.fermionic, Fin.sum_univ_succ]
  ring_nf
  simp
  ring
end YangMills.WardAction
