import YangMills.WardActionCoordinates
set_option maxHeartbeats 20000000
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
  simpa [List.finRange, List.map_ofFn] using (List.sum_ofFn (f := f))

theorem quartic_amplitude {B : InvariantForm G} (e : ColorFrame B)
    (a b : Fin G.dimension) (q : Fin 4 → Spacetime) :
    basisAmplitude e .quartic
      [.inl (.gauge 0 a), .inl (.gauge 1 b), .inl (.gauge 0 a), .inl (.gauge 1 b)] q =
      2 * (fourColor B (e.basis a) (e.basis b) (e.basis a) (e.basis b) : ℂ) := by
  unfold basisAmplitude basisVertices liftPhysical quarticMonomials localPolynomialAmplitude
  simp only [List.map_map, Function.comp_def]
  simp (config := { maxSteps := 2000000 }) [localVertexAmplitude,
    localMonomialDerivative, List.ofFn_succ,
    ExternalLeg.parity, BasicField.fermionic, Fin.sum_univ_succ]
  simp_rw [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  simp
  simp_rw [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  simp
  simp only [fourColor]
  have hb : ⁅e.basis b, e.basis a⁆ = -⁅e.basis a, e.basis b⁆ :=
    (lie_skew (e.basis b) (e.basis a)).symm
  simp only [hb, map_neg, LinearMap.neg_apply, neg_neg]
  ring

end YangMills.WardAction
