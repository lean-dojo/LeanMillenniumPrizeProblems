import YangMills.InsertionProjectorWeights
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace YangMills.PerturbativeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual iterated directional derivatives, retaining the entire smooth
function between steps. This is not a freely supplied Taylor tensor. -/
def directionalWord : List E → (E → ℂ) → E → ℂ
  | [], f => f
  | v::rest, f => fun x => fderiv ℝ (directionalWord rest f) x v

lemma directionalWord_smooth (directions : List E) {f : E → ℂ} (smooth : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalWord directions f) := by
  induction directions with
  | nil => exact smooth
  | cons v rest ih =>
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma directionalWord_swap (v w : E) (rest : List E) {f : E → ℂ}
    (smooth : ContDiff ℝ ∞ f) :
    directionalWord (v::w::rest) f = directionalWord (w::v::rest) f := by
  have h := directionalWord_smooth rest smooth
  have hd : ContDiff ℝ ∞ (fderiv ℝ (directionalWord rest f)) :=
    h.fderiv_right (m := ∞) (by simp)
  funext x
  simp only [directionalWord]
  rw [fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const w),
    fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const v)]
  simp only [ContinuousLinearMap.add_apply,fderiv_const_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact second_derivative_symmetric
    (fun y => (h.differentiable (by simp) y).hasFDerivAt)
    (hd.differentiable (by simp) x).hasFDerivAt v w

/-- Smooth actual directional derivatives depend only on the multiset of
directions. All orders follow from the real second-derivative theorem. -/
theorem directionalWord_perm {directions other : List E} (permutation : directions.Perm other)
    {f : E → ℂ} (smooth : ContDiff ℝ ∞ f) :
    directionalWord directions f = directionalWord other f := by
  induction permutation with
  | nil => rfl
  | cons v _ ih => simp only [directionalWord,ih]
  | swap v w rest => exact directionalWord_swap w v rest smooth
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma directionalWord_eq_iteratedFDeriv (directions : List E) {f : E → ℂ}
    (smooth : ContDiff ℝ ∞ f) (x : E) :
    directionalWord directions f x =
      iteratedFDeriv ℝ directions.length f x directions.get := by
  induction directions generalizing x with
  | nil => simp [directionalWord,iteratedFDeriv_zero_apply]
  | cons v rest ih =>
    have equal : directionalWord rest f = fun y => iteratedFDeriv ℝ rest.length f y rest.get := funext ih
    have regular := (smooth.iteratedFDeriv_right (m := 1) (i := rest.length)
      (by exact_mod_cast (show (1 : ℕ∞) + rest.length ≤ ⊤ from le_top))).differentiable (by norm_num)
    simp only [directionalWord,List.length_cons,iteratedFDeriv_succ_apply_left,List.get_cons_zero]
    rw [equal,fderiv_continuousMultilinear_apply_const_apply (regular x)]
    rfl

variable {G : CompactSimpleGaugeGroup}

lemma momentumJet_eq_directionalWord (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4))
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (q : Fin legs.length → Spacetime) :
    momentumJet directions f q = directionalWord
      (directions.map (fun d => (Pi.single d.1 (Pi.single d.2 1) : Fin legs.length → Spacetime))) f q := by
  induction directions generalizing q with
  | nil => simp [momentumJet,directionalWord,iteratedFDeriv_zero_apply]
  | cons d rest ih =>
    have equal : directionalWord
        (rest.map (fun d => (Pi.single d.1 (Pi.single d.2 1) : Fin legs.length → Spacetime))) f =
        fun p => momentumJet rest f p := funext (fun p => (ih p).symm)
    simp only [List.map_cons,directionalWord]
    rw [equal]
    unfold momentumJet
    have regular := (smooth.iteratedFDeriv_right (m := 1) (i := rest.length)
      (by exact_mod_cast (show (1 : ℕ∞) + rest.length ≤ ⊤ from le_top))).differentiable (by norm_num)
    rw [fderiv_continuousMultilinear_apply_const_apply (regular q)]
    simp only [List.length_cons]
    rw [iteratedFDeriv_succ_apply_left]
    rfl

/-- The fixed actual momentum derivative is invariant under permutation
of its coordinate directions, at every momentum and every finite order. -/
theorem momentumJet_perm (legs : List (ExternalLeg G))
    {directions other : List (Fin legs.length × Fin 4)} (permutation : directions.Perm other)
    {f : (Fin legs.length → Spacetime) → ℂ} (smooth : ContDiff ℝ ∞ f)
    (q : Fin legs.length → Spacetime) : momentumJet directions f q = momentumJet other f q := by
  rw [momentumJet_eq_directionalWord legs directions smooth,
    momentumJet_eq_directionalWord legs other smooth,
    directionalWord_perm (permutation.map _) smooth]

end YangMills.PerturbativeFlow
