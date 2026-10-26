import YangMills.LegendreSplitTransport
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.Legendre YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

def rootedAmplitude (F : FormalAmplitude G) (order loop : ℕ) (root : ExternalLeg G) : OrderedAmplitude G :=
  fun legs q => F order loop (root::legs) (prependMomenta root (-(∑ i, q i)) q)

def quadraticKernelForm (F : FormalAmplitude G) (s : CutoffScales) (order loop : ℕ) : OrderedAmplitude G :=
  fun legs q => (1/2 : ℂ) * ∑ a : Fin (order+1), ∑ l : Fin (loop+1),
    ∑ M : BasicField G, ∑ N : BasicField G, rightDerivativeSign false (.inl M) *
      splitKernelSum (rootedAmplitude F a.val l.val (.inl M))
        (rootedAmplitude F (order-a.val) (loop-l.val) (.inl N))
        (fun p => (basicCovariance s M N p : ℂ)) legs q

theorem gradientQuadratic_eq_kernel (F : FormalAmplitude G) (s : CutoffScales) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (balanced : BalancedMomenta legs q) :
    gradientQuadratic F s order loop legs q = quadraticKernelForm F s order loop legs q := by
  unfold gradientQuadratic quadraticKernelForm
  rw [Finset.powerset_univ]
  apply congrArg (fun z : ℂ => (1/2)*z)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l _
  simp only [splitKernelSum, splitKernelTerm, rootedAmplitude, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N _
  apply Finset.sum_congr rfl
  intro S _
  rw [sum_selectedMomenta, sum_selectedMomenta, selectedMomentum_complement legs S q balanced]
  ring


theorem quadraticKernelForm_graded (F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    quadraticKernelForm F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * quadraticKernelForm F s order loop legs q := by
  have rootGrade (r l : ℕ) (M : ExternalLeg G) :
      ∀ legs q (e : Equiv.Perm (Fin legs.length)),
      rootedAmplitude F r l M (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * rootedAmplitude F r l M legs q :=
    rootedCoefficient_graded F graded r l M
  have sumGrade :
      (∑ a : Fin (order+1), ∑ l : Fin (loop+1), ∑ M : BasicField G, ∑ N : BasicField G,
        rightDerivativeSign false (.inl M) * splitKernelSum
          (rootedAmplitude F a.val l.val (.inl M))
          (rootedAmplitude F (order-a.val) (loop-l.val) (.inl N))
          (fun p => (basicCovariance s M N p : ℂ))
          (permutedLegs legs e) (permutedMomenta legs e q)) =
      permutationSign legs e *
      ∑ a : Fin (order+1), ∑ l : Fin (loop+1), ∑ M : BasicField G, ∑ N : BasicField G,
        rightDerivativeSign false (.inl M) * splitKernelSum
          (rootedAmplitude F a.val l.val (.inl M))
          (rootedAmplitude F (order-a.val) (loop-l.val) (.inl N))
          (fun p => (basicCovariance s M N p : ℂ)) legs q := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro N _
    rw [splitKernelSum_graded _ _ _ (rootGrade _ _ _) (rootGrade _ _ _)]
    ring
  unfold quadraticKernelForm
  rw [sumGrade]
  ring

/-- The actual right/left graded quadratic subtraction preserves the
source background statistics on momentum-conserving configurations. -/
theorem gradientQuadratic_graded_balanced (F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (balanced : BalancedMomenta legs q) :
    gradientQuadratic F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * gradientQuadratic F s order loop legs q := by
  have hp : BalancedMomenta (permutedLegs legs e) (permutedMomenta legs e q) := by
    simpa only [BalancedMomenta, sum_permutedMomenta] using balanced
  rw [gradientQuadratic_eq_kernel F s order loop _ _ hp,
    gradientQuadratic_eq_kernel F s order loop legs q balanced]
  exact quadraticKernelForm_graded F s graded order loop legs q e

theorem legendreTarget_graded_balanced (F : FormalAmplitude G) (s : CutoffScales)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) (balanced : BalancedMomenta legs q) :
    legendreTarget F s order loop (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * legendreTarget F s order loop legs q := by
  change F order loop _ _ - gradientQuadratic F s order loop _ _ = _
  rw [graded order loop legs q e balanced, gradientQuadratic_graded_balanced F s graded _ _ _ _ e balanced]
  change _ = permutationSign legs e * (F order loop legs q - gradientQuadratic F s order loop legs q)
  ring

/-- Background Legendre inversion now follows from the actual source
normalization and balanced graded law, with no separate transform equation. -/
theorem gammaCoeff_inverse_from_source (F : FormalAmplitude G) (s : CutoffScales)
    (free : ∀ loop legs q, F 0 loop legs q = 0)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (balanced : BalancedMomenta legs q) :
    meanFieldCompose (gammaCoeff F s) F s order loop legs q = legendreTarget F s order loop legs q :=
  gammaCoeff_inverse_balanced F s free graded (legendreTarget_graded_balanced F s graded)
    order loop legs q balanced


theorem meanFieldRoot_empty_of_onePoint (F : FormalAmplitude G) (s : CutoffScales)
    (onePoint : ∀ order loop (M : BasicField G),
      F order loop [.inl M] (fun _ => 0) = 0)
    (order loop : ℕ) (root : ExternalLeg G) :
    meanFieldRoot F s order loop root [] (fun i => Fin.elim0 i) = 0 := by
  cases root with
  | inl M =>
    have hz (N : BasicField G) :
        prependMomenta (legs := ([] : List (ExternalLeg G))) (.inl N) 0
          (fun i => Fin.elim0 i) = (fun _ => (0 : Spacetime)) := by
      funext i
      fin_cases i
      rfl
    have hF (N : BasicField G) : F order loop [.inl N]
        (prependMomenta (legs := ([] : List (ExternalLeg G))) (.inl N) 0
          (fun i => Fin.elim0 i)) = 0 :=
      (congrArg (F order loop [.inl N]) (hz N)).trans (onePoint order loop N)
    simp only [meanFieldRoot, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty, neg_zero]
    simp only [identityRoot, reduceCtorEq, if_false, ite_self, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro N _
    apply mul_eq_zero_of_right
    convert hF N using 1
  | inr M => simp [meanFieldRoot, identityRoot]

/-- Full formal background fidelity has source-level sufficient conditions:
free interaction normalization, balanced gradedness and vanishing one-point
vertices. This proves the computed equation, without choosing a transform. -/
theorem amputatedLegendreEquations_from_source (F : FormalAmplitude G) (s : CutoffScales)
    (free : ∀ loop legs q, F 0 loop legs q = 0)
    (graded : ∀ order loop legs q (e : Equiv.Perm (Fin legs.length)),
      BalancedMomenta legs q →
      F order loop (permutedLegs legs e) (permutedMomenta legs e q) =
        permutationSign legs e * F order loop legs q)
    (onePoint : ∀ order loop (M : BasicField G),
      F order loop [.inl M] (fun _ => 0) = 0) :
    AmputatedLegendreEquations F s := by
  exact ⟨meanFieldRoot_empty_of_onePoint F s onePoint, free,
    gammaCoeff_inverse_from_source F s free graded⟩

end YangMills.LegendreInsertionBridge
