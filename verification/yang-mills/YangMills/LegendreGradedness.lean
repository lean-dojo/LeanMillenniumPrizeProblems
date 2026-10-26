import YangMills.LegendreIdentityNormalization

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre
open YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

/-- Extend an external permutation while retaining the differentiated
background root in the first slot. -/
def prependPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem prependPermutation_zero {n : ℕ} (e : Equiv.Perm (Fin n)) :
    prependPermutation e 0 = 0 := rfl
@[simp] theorem prependPermutation_succ {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    prependPermutation e i.succ = (e i).succ := rfl

theorem permutationSign_prepend (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) :
    permutationSign (root::legs) (prependPermutation e) = permutationSign legs e := by
  simp only [permutationSign, List.length_cons, Fin.sum_univ_succ,
    prependPermutation_zero, prependPermutation_succ]
  simp

theorem permutedLegs_prepend (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) :
    permutedLegs (root::legs) (prependPermutation e) = root :: permutedLegs legs e := by
  simp [permutedLegs, List.ofFn_succ]

theorem sum_permutedMomenta (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) (q : Fin legs.length → Spacetime) :
    (∑ i : Fin (permutedLegs legs e).length, permutedMomenta legs e q i) = ∑ i, q i := by
  have hl : (permutedLegs legs e).length = legs.length := by simp [permutedLegs]
  simpa [permutedMomenta] using ((finCongr hl).trans e).sum_comp q


theorem balancedMomenta_prepend (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    BalancedMomenta (root::legs) (prependMomenta root (-(∑ i, q i)) q) := by
  simp [BalancedMomenta, prependMomenta, Fin.sum_univ_succ]


theorem identityRoot_graded (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (e : Equiv.Perm (Fin legs.length)) :
    identityRoot root (permutedLegs legs e) = permutationSign legs e * identityRoot root legs := by
  by_cases hn : legs.length = 1
  · obtain ⟨K, rfl⟩ := List.length_eq_one_iff.mp hn
    have he : e = Equiv.refl _ := by
      ext i
      have h1 := (e i).isLt
      have h2 := i.isLt
      simp only [List.length_cons, List.length_nil] at h1 h2
      change (e i).val = i.val
      omega
    subst e
    simp [permutedLegs, List.ofFn_succ, permutationSign]
  · have hbase : legs ≠ [root] := by
      intro h
      exact hn (by simp [h])
    have hpermuted : permutedLegs legs e ≠ [root] := by
      intro h
      have hl := congrArg List.length h
      exact hn (by simpa [permutedLegs] using hl)
    simp [identityRoot, hbase, hpermuted]


theorem amplitude_congr_legs (A : OrderedAmplitude G)
    {legs other : List (ExternalLeg G)} (hlegs : legs = other)
    {q : Fin legs.length → Spacetime} {p : Fin other.length → Spacetime}
    (hmomenta : HEq q p) : A legs q = A other p := by
  subst hlegs
  exact congrArg (A legs) (eq_of_heq hmomenta)

/-- Gradedness of the fixed background derivative entering each mean root.
The background hypothesis is used only at balanced momenta, as in the
source flow conditions. The insertion's external momenta stay independent. -/
theorem rootedCoefficient_graded (F : FormalAmplitude G)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (e : Equiv.Perm (Fin legs.length)) :
    F order loop (root :: permutedLegs legs e)
      (prependMomenta root (-(∑ i, permutedMomenta legs e q i)) (permutedMomenta legs e q)) =
      permutationSign legs e * F order loop (root::legs)
        (prependMomenta root (-(∑ i, q i)) q) := by
  have h := graded order loop (root::legs)
    (prependMomenta root (-(∑ i, q i)) q) (prependPermutation e)
    (balancedMomenta_prepend root legs q)
  rw [permutationSign_prepend] at h
  rw [sum_permutedMomenta]
  convert h using 1
  apply amplitude_congr_legs (F order loop) (permutedLegs_prepend root legs e).symm
  apply (Fin.heq_fun_iff (congrArg List.length (permutedLegs_prepend root legs e).symm)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [permutedMomenta, prependMomenta, prependPermutation]

/-- Every actual mean-field root has the required external graded law,
using ONLY the source's balanced background gradedness. The fixed covariance
and spectator antifields are retained. -/
theorem meanFieldRoot_graded (F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (e : Equiv.Perm (Fin legs.length)) :
    meanFieldRoot F s order loop root (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * meanFieldRoot F s order loop root legs q := by
  cases root with
  | inl M =>
    simp only [meanFieldRoot]
    simp_rw [rootedCoefficient_graded F graded, sum_permutedMomenta]
    have hs : (∑ N : BasicField G,
        (basicCovariance s M N (∑ i, q i) : ℂ) *
          (permutationSign legs e * F order loop (.inl N :: legs)
            (prependMomenta (.inl N) (-(∑ i, q i)) q))) =
        permutationSign legs e * ∑ N : BasicField G,
          (basicCovariance s M N (∑ i, q i) : ℂ) *
            F order loop (.inl N :: legs) (prependMomenta (.inl N) (-(∑ i, q i)) q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      ring
    rw [hs, identityRoot_graded]
    by_cases h : order=0 ∧ loop=0 <;> simp [h]
    ring
  | inr M =>
    simp only [meanFieldRoot, identityRoot_graded, sub_zero]
    by_cases h : order=0 ∧ loop=0 <;> simp [h]

/-- Coupling coefficient extraction preserves the source graded identity.
Only the actual sign ±1 is pulled through iterated real derivatives; no
unjustified complex-scalar derivative rule or smoothness is needed here. -/
theorem flowJet_graded (A : ℝ → FlowFamily G) (s : CutoffScales)
    (graded : ∀ g loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      A g loop s.infrared s.ultraviolet (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * A g loop s.infrared s.ultraviolet legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (balanced : BalancedMomenta legs q) :
    flowJet A s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * flowJet A s order loop legs q := by
  have hf : (fun g : ℝ => A g loop s.infrared s.ultraviolet
      (permutedLegs legs e) (permutedMomenta legs e q)) =
      (fun g : ℝ => permutationSign legs e * A g loop s.infrared s.ultraviolet legs q) :=
    funext (fun g => graded g loop legs q e balanced)
  unfold flowJet
  rw [hf]
  obtain hs | hs := neg_one_pow_eq_or ℂ
    (∑ i : Fin legs.length, ∑ j : Fin legs.length,
      if i<j ∧ e j<e i ∧ (legs.get (e i)).parity=true ∧ (legs.get (e j)).parity=true then 1 else 0)
  · change permutationSign legs e = 1 at hs
    simp [hs]
  · change permutationSign legs e = -1 at hs
    simp [hs, iteratedDeriv_fun_neg]

end YangMills.LegendreInsertionBridge
