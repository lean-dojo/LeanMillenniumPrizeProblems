import Problems.YangMills.FourierTaylorUniformEnumeration
import Problems.YangMills.MomentumJetSymmetry
import Mathlib.Analysis.Analytic.IteratedFDeriv

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.PerturbativeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- C-infinity symmetry of the actual derivative tensor, using actual
Schwarz commutation of directional words rather than analytic regularity. -/
theorem smooth_iteratedFDeriv_perm (f : E → ℂ) (smooth : ContDiff ℝ ∞ f)
    (x : E) (n : ℕ) (v : Fin n → E) (π : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (fun i => v (π i)) = iteratedFDeriv ℝ n f x v := by
  have hp := directionalWord_perm (π.ofFn_comp_perm v) smooth
  have he := congrArg (fun h : E → ℂ => h x) hp
  rw [directionalWord_eq_iteratedFDeriv _ smooth x,
    directionalWord_eq_iteratedFDeriv _ smooth x] at he
  have ht (w : Fin n → E) :
      iteratedFDeriv ℝ (List.ofFn w).length f x (List.ofFn w).get =
        iteratedFDeriv ℝ n f x w := by
    have transport (a b : ℕ) (h : a = b) (u : Fin a → E) :
        iteratedFDeriv ℝ a f x u =
          iteratedFDeriv ℝ b f x (fun i => u (Fin.cast h.symm i)) := by
      subst b
      rfl
    rw [transport _ _ List.length_ofFn]
    congr 1
    funext i
    simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_refl, id_eq]
  rw [ht, ht] at he
  exact he

def filteredTaylorSeries (D d : ℕ) (f : E → ℂ) : FormalMultilinearSeries ℝ E ℂ :=
  fun n => if d+n ≤ D then (1 / (Nat.factorial n : ℝ)) • iteratedFDeriv ℝ n f 0 else 0

def filteredTaylorPolynomial (D d : ℕ) (f : E → ℂ) (x : E) : ℂ :=
  ∑ n ∈ Finset.range (D+1), filteredTaylorSeries D d f n (fun _ => x)

theorem filteredTaylorPolynomial_powerSeries (D d : ℕ) (f : E → ℂ) :
    HasFiniteFPowerSeriesOnBall (filteredTaylorPolynomial D d f)
      (filteredTaylorSeries D d f) 0 (D+1) 1 := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro n hn
    exact if_neg (by omega)
  · norm_num
  · intro y hy
    simp only [zero_add, filteredTaylorPolynomial]

theorem filteredTaylorPolynomial_jet (D d : ℕ) (f : E → ℂ)
    (smooth : ContDiff ℝ ∞ f) (n : ℕ) (hn : d+n ≤ D) :
    iteratedFDeriv ℝ n (filteredTaylorPolynomial D d f) 0 = iteratedFDeriv ℝ n f 0 := by
  ext v
  have hs := (filteredTaylorPolynomial_powerSeries D d f).toHasFPowerSeriesOnBall
  rw [hs.iteratedFDeriv_eq_sum_of_completeSpace v]
  simp only [filteredTaylorSeries, if_pos hn, ContinuousMultilinearMap.smul_apply]
  simp_rw [smooth_iteratedFDeriv_perm f smooth 0 n v]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hn0 : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  field_simp
  simp only [one_smul]

end YangMills.IntegratedNormalization
