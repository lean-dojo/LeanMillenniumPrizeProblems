import Problems.YangMills.LegendreInsertionBridge

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
/-!
# Exact two-leg graded identity-root normalization

This evaluates the actual partition sum, including its odd crossing sign and
1/2!, before using graded symmetry. It applies to every external field/source
species of the actual group; no commuting replacement of ghost legs is used.
-/
noncomputable section
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
open YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}
theorem sum_roots_pair (f : ExternalLeg G → ExternalLeg G → ℂ) (K H : ExternalLeg G) :
    (∑ R, ∑ S, f R S * identityRoot R [K] * identityRoot S [H]) = f K H := by
  simp [identityRoot, mul_ite]

theorem sign_pair (K H : ExternalLeg G) (a b : Fin 2) :
    partitionSign [K,H] ![a,b] =
      (-1 : ℂ) ^ (if b<a ∧ K.parity=true ∧ H.parity=true then 1 else 0) := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  simp [partitionSign, hu, Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> simp_all

theorem sum_fun_two {X : Type*} [Fintype X] (f : (Fin 2 → X) → ℂ) :
    ∑ v, f v = ∑ x : X, ∑ y : X, f ![x,y] := by
  calc
    _ = ∑ p : X × X, f ![p.1,p.2] := by
      apply Fintype.sum_equiv (finTwoArrowEquiv X)
      intro v
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = _ := Fintype.sum_prod_type _

theorem block_two (a b c : Fin 2) :
    partitionBlock ![a,b] c =
      (if a=c then {0} else ∅) ∪ (if b=c then {1} else ∅) := by
  ext i
  fin_cases i <;> split_ifs <;> simp_all [partitionBlock]


theorem roots_pair_momenta (K H : ExternalLeg G)
    (q : Fin ([K,H] : List (ExternalLeg G)).length → Spacetime) :
    rootMomenta [K,H] q ![0,1] ![K,H] = q := by
  funext i
  fin_cases i <;> simp [rootMomenta, block_two, selectedMomentum]

theorem roots_swap_momenta (K H : ExternalLeg G)
    (q : Fin ([K,H] : List (ExternalLeg G)).length → Spacetime) :
    rootMomenta [K,H] q ![1,0] ![H,K] =
      (fun i => q ⟨1-i.val, by have hi := i.isLt; simp [rootLegs] at hi ⊢⟩) := by
  funext i
  fin_cases i <;> simp [rootMomenta, block_two, selectedMomentum]

theorem meanFieldCompose_zero_pair (F A : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (K H : ExternalLeg G) (q : Fin ([K,H] : List (ExternalLeg G)).length → Spacetime) :
    meanFieldCompose A F s 0 0 [K,H] q =
      (1/2 : ℂ) * (A 0 0 [K,H] q +
        (-1 : ℂ) ^ (if K.parity = true ∧ H.parity = true then 1 else 0) *
          A 0 0 [H,K] (fun i => q ⟨1-i.val, by have hi := i.isLt; simp at hi ⊢⟩)) := by
  simp only [meanFieldCompose, List.length_cons, List.length_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have hu : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  have hb : partitionBlock (fun _ : Fin 2 => (0 : Fin 1)) 0 = {0,1} := by
    ext i
    fin_cases i <;> simp [partitionBlock]
  have hsort : ({0,1} : Finset (Fin 2)).sort (· ≤ ·) = [0,1] := by
    rw [Finset.sort_insert (r := (· ≤ ·)) (by simp) (by decide), Finset.sort_singleton]
  simp [-Fintype.sum_sum_type, substitutionSummand, meanFieldRoot_at_free F s hF,
    sum_fun_two, block_two, sign_pair, hb, hu, hsort, selectedLegs, selectedIndices, identityRoot,
    mul_ite, rootLegs]
  simp only [roots_pair_momenta, roots_swap_momenta]
  change (2:ℂ)⁻¹ * A 0 0 [K,H] q +
    (if K.parity=true ∧ H.parity=true then -((2:ℂ)⁻¹ * A 0 0 [H,K] _)
      else (2:ℂ)⁻¹ * A 0 0 [H,K] _) = _
  split_ifs <;> ring_nf <;> rfl

/-- The first odd-sensitive inverse-composition coefficient is proved for
the actual computed insertion recursion under its actual graded swap law. -/
theorem insertion_inverse_leading_pair (F I : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (K H : ExternalLeg G) (q : Fin ([K,H] : List (ExternalLeg G)).length → Spacetime)
    (graded : I 0 0 [H,K]
      (fun i => q ⟨1-i.val, by have hi := i.isLt; simp at hi ⊢⟩) =
      (-1 : ℂ) ^ (if K.parity=true ∧ H.parity=true then 1 else 0) * I 0 0 [K,H] q) :
    meanFieldCompose (insertionGammaCoeff F I s) F s 0 0 [K,H] q = I 0 0 [K,H] q := by
  rw [meanFieldCompose_zero_pair _ _ _ hF]
  simp only [insertionGammaCoeff_zero]
  rw [graded]
  by_cases h : K.parity=true ∧ H.parity=true <;> simp [h] <;> ring

end YangMills.LegendreInsertionBridge
