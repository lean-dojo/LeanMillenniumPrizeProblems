import Problems.YangMills.ActionProbeSupport

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
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

theorem ghostVertex_amplitude {B : InvariantForm G} (e : ColorFrame B) (a b c : Fin G.dimension)
    (q : Fin 3 → Spacetime) :
    basisAmplitude e .ghostVertex [.inl (.antighost a), .inl (.gauge 0 b), .inl (.ghost c)] q =
      (structureConstant e a b c : ℂ) * (-Complex.I * (q 0 0 : ℂ)) := by
  unfold basisAmplitude basisVertices liftPhysical ghostMonomials localPolynomialAmplitude

  simp (maxSteps := 1000000) [localVertexAmplitude, localMonomialDerivative, List.ofFn_succ,
    ExternalLeg.parity, BasicField.fermionic, Fin.sum_univ_succ]



end YangMills.WardAction
