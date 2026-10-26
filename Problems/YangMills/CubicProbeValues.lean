import Problems.YangMills.WardActionCoordinates

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxHeartbeats 12000000
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

theorem structureConstant_cycle {B : InvariantForm G} (e : ColorFrame B) (a b c : Fin G.dimension) :
    structureConstant e a b c = structureConstant e c a b := by
  have h := B.invariant (e.basis b) (e.basis a) (e.basis c)
  rw [← lie_skew (e.basis b) (e.basis a), map_neg, LinearMap.neg_apply] at h
  rw [B.symmetric ⁅e.basis a, e.basis b⁆ (e.basis c)] at h
  dsimp [structureConstant, threeColor]
  linarith

theorem structureConstant_skew {B : InvariantForm G} (e : ColorFrame B) (a b c : Fin G.dimension) :
    structureConstant e a b c = -structureConstant e a c b :=
  threeColor_antisymmetric B _ _ _

theorem cubic_amplitude {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) (q : Fin 3 → Spacetime) :
    basisAmplitude e .cubic
      [.inl (.gauge 0 a), .inl (.gauge 1 b), .inl (.gauge 1 c)] q =
      Complex.I * (structureConstant e a b c : ℂ) * ((q 1 0 : ℂ) - (q 2 0 : ℂ)) := by
  unfold basisAmplitude basisVertices liftPhysical cubicMonomials localPolynomialAmplitude
  simp only [List.map_map, Function.comp_def]
  simp (config := { maxSteps := 1000000 }) [localVertexAmplitude, localMonomialDerivative, List.ofFn_succ,
    ExternalLeg.parity, BasicField.fermionic, Fin.sum_univ_succ]
  simp_rw [mul_add, mul_ite, mul_neg, mul_zero, Finset.sum_add_distrib]
  simp
  rw [structureConstant_skew e b a c, structureConstant_cycle e b c a,
    structureConstant_cycle e c a b, structureConstant_skew e c b a,
    structureConstant_cycle e c a b]
  rw [structureConstant_cycle e b c a]
  push_cast
  ring
end YangMills.WardAction
