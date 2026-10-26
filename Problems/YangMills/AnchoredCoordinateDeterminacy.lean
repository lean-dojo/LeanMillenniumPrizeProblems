import Problems.YangMills.MomentumJetSymmetry
import Problems.YangMills.FiniteJetDeterminacy
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2400000
open scoped ContDiff
namespace YangMills.CanonicalUV
open YangMills.PerturbativeFlow

/-- Ordinary smooth one-dimensional finite-jet determinacy. -/
theorem scalar_finiteJet_zero {f : ℝ → ℂ} (smooth : ContDiff ℝ ∞ f) (L : ℕ)
    (positive : 0 < L) (highest : ∀ t, iteratedDeriv L f t = 0)
    (lower : ∀ k < L, iteratedDeriv k f 0 = 0) : f = 0 := by
  apply finiteJet_determinacy smooth (L-1)
  · intro t
    apply (norm_eq_zero (a := iteratedFDeriv ℝ ((L-1)+1) f t)).mp
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,show L-1+1=L by omega,highest t,norm_zero]
  · intro k hk
    apply (norm_eq_zero (a := iteratedFDeriv ℝ k f 0)).mp
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,lower k (by omega),norm_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual coordinate derivatives as a function, between every derivative. -/
def coordinateJet (directions : List ι) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  directionalWord (directions.map (fun i => (Pi.single i 1 : ι → ℝ))) f

theorem coordinateJet_smooth (directions : List ι) {f : (ι → ℝ) → ℂ}
    (smooth : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordinateJet directions f) :=
  directionalWord_smooth _ smooth

omit [Fintype ι] in
lemma coordinateLine_hasDerivAt (q : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Function.update q i r) (Pi.single i 1) t := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self,Pi.single_eq_same] using! hasDerivAt_id t
  · simpa only [Function.update_of_ne hji,Pi.single_eq_of_ne hji] using! hasDerivAt_const t (q j)

/-- Repeated scalar differentiation of an anchored coordinate line is
exactly the corresponding extended actual coordinate jet. -/
theorem iteratedDeriv_coordinateLine (directions : List ι) {f : (ι → ℝ) → ℂ}
    (smooth : ContDiff ℝ ∞ f) (q : ι → ℝ) (i : ι) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun r : ℝ => coordinateJet directions f (Function.update q i r)) t =
      coordinateJet (List.replicate k i ++ directions) f (Function.update q i t) := by
  induction k generalizing t with
  | zero => simp only [iteratedDeriv_zero,List.replicate_zero,List.nil_append]
  | succ k ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv k
      (fun r : ℝ => coordinateJet directions f (Function.update q i r)) =
      (fun r : ℝ => coordinateJet (List.replicate k i ++ directions) f (Function.update q i r)) from funext ih]
    have hs := coordinateJet_smooth (List.replicate k i ++ directions) smooth
    have hd := (hs.differentiable (by simp) (Function.update q i t)).hasFDerivAt.comp_hasDerivAt
      t (coordinateLine_hasDerivAt q i t)
    simpa only [Function.comp_def,coordinateJet,List.replicate_succ,List.cons_append,
      List.map_cons,directionalWord] using! hd.deriv

/-- Rectangular corner condition on anchored coordinate faces. Coordinates
whose derivative count has not reached L are anchored at0. -/
def AnchoredFaces (L : ℕ) (f : (ι → ℝ) → ℂ) (free : Finset ι) : Prop :=
  ∀ directions : List ι, (∀ i, directions.count i ≤ L) → ∀ q : ι → ℝ,
    (∀ i, i ∉ free → directions.count i < L → q i = 0) → coordinateJet directions f q = 0

/-- Free one more coordinate using only finite one-dimensional smooth jet
uniqueness. No infinite Taylor expansion or analyticity is used. -/
theorem AnchoredFaces.free_insert {L : ℕ} {f : (ι → ℝ) → ℂ}
    (smooth : ContDiff ℝ ∞ f) {free : Finset ι} (h : AnchoredFaces L f free) (i : ι) :
    AnchoredFaces L f (insert i free) := by
  intro directions bounded q face
  by_cases high : directions.count i = L
  · apply h directions bounded q
    intro j hj hlow
    by_cases hji : j = i
    · subst j; omega
    · exact face j (by simp only [Finset.mem_insert,not_or]; exact ⟨hji,hj⟩) hlow
  · have gap : 0 < L-directions.count i := by have := bounded i; omega
    have counts (k : ℕ) (j : ι) :
        (List.replicate k i ++ directions).count j =
          (if j = i then k else 0) + directions.count j := by
      simp only [List.count_append,List.count_replicate]
      split_ifs <;> simp_all
    have boundk (k : ℕ) (hk : k ≤ L-directions.count i) :
        ∀ j, (List.replicate k i ++ directions).count j ≤ L := by
      intro j
      rw [counts]
      split_ifs with hji
      · subst j; omega
      · simpa only [zero_add] using! bounded j
    have hs : ContDiff ℝ ∞ (fun t : ℝ => coordinateJet directions f (Function.update q i t)) := by
      apply (coordinateJet_smooth directions smooth).comp
      apply contDiff_pi.mpr
      intro j
      by_cases hji : j = i
      · subst j; simpa only [Function.update_self] using! (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
      · simpa only [Function.update_of_ne hji] using! (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => q j))
    have hz := scalar_finiteJet_zero hs (L-directions.count i) gap
      (by
        intro t
        rw [iteratedDeriv_coordinateLine directions smooth]
        apply h _ (boundk _ le_rfl) (Function.update q i t)
        intro j hj hlow
        by_cases hji : j = i
        · subst j
          rw [counts,if_pos rfl] at hlow
          have := bounded i
          omega
        · rw [Function.update_of_ne hji]
          apply face j (by simp only [Finset.mem_insert,not_or]; exact ⟨hji,hj⟩)
          simpa only [counts,if_neg hji,zero_add] using! hlow)
      (by
        intro k hk
        rw [iteratedDeriv_coordinateLine directions smooth]
        apply h _ (boundk k (by omega)) (Function.update q i 0)
        intro j hj hlow
        by_cases hji : j = i
        · subst j; exact Function.update_self _ _ _
        · rw [Function.update_of_ne hji]
          apply face j (by simp only [Finset.mem_insert,not_or]; exact ⟨hji,hj⟩)
          simpa only [counts,if_neg hji,zero_add] using! hlow)
    have hx := congrFun hz (q i)
    simpa only [Function.update_eq_self,Pi.zero_apply] using! hx

/-- Exact anchored rectangular C∞ determinacy from its actual finite jets. -/
theorem anchored_coordinate_determinacy {L : ℕ} {f : (ι → ℝ) → ℂ}
    (smooth : ContDiff ℝ ∞ f) (corners : AnchoredFaces L f ∅) : f = 0 := by
  have allFaces (S : Finset ι) : AnchoredFaces L f S := by
    induction S using Finset.induction_on with
    | empty => exact corners
    | insert i S _ ih => exact ih.free_insert smooth i
  funext q
  have hz := allFaces Finset.univ [] (by intro i; simp) q (by simp)
  exact hz

end YangMills.CanonicalUV
