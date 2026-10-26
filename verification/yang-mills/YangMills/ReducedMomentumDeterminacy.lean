import YangMills.FiniteJetDeterminacy

noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
open scoped ContDiff
variable {G : CompactSimpleGaugeGroup}

/-- The actual independent coordinates: retain all momenta except the last. -/
def reducedMomentumProjection (legs : List (ExternalLeg G)) :
    (Fin legs.length → Spacetime) →L[ℝ] (Fin legs.length → Spacetime) :=
  ContinuousLinearMap.pi fun i =>
    if i.val + 1 = legs.length then 0 else ContinuousLinearMap.proj i

@[simp] theorem reducedMomentumProjection_apply (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (i : Fin legs.length) :
    reducedMomentumProjection legs q i =
      if i.val + 1 = legs.length then 0 else q i := by
  simp only [reducedMomentumProjection, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem conservingMomenta_reducedProjection (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    conservingMomenta legs (reducedMomentumProjection legs q) = conservingMomenta legs q := by
  classical
  funext i
  unfold conservingMomenta
  split_ifs with hi
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [reducedMomentumProjection_apply, if_neg]
    have hj' := (Finset.mem_filter.mp hj).2
    omega
  · simp [hi]

theorem reducedMomentumProjection_basis (legs : List (ExternalLeg G))
    (d : Fin legs.length × Fin 4) :
    reducedMomentumProjection legs (Pi.single d.1 (Pi.single d.2 1)) =
      if d.1.val + 1 < legs.length then Pi.single d.1 (Pi.single d.2 1) else 0 := by
  classical
  ext i j
  simp only [reducedMomentumProjection_apply]
  by_cases h : d.1.val + 1 < legs.length
  · rw [if_pos h]
    by_cases hd : i = d.1
    · subst i
      rw [if_neg (by omega)]
    · simp [hd]
  · rw [if_neg h]
    by_cases hd : i = d.1
    · subst i
      rw [if_pos (by omega)]
      rfl
    · simp [hd]

theorem reduced_extension_projection {legs : List (ExternalLeg G)}
    {f : (Fin legs.length → Spacetime) → ℂ}
    (extension : ∀ q, f q = f (conservingMomenta legs q)) :
    f = f ∘ reducedMomentumProjection legs := by
  funext q
  exact (extension q).trans ((extension _).trans
    (congrArg f (conservingMomenta_reducedProjection legs q))).symm

theorem momentumJet_ofFn {legs : List (ExternalLeg G)} (k : ℕ)
    (p : Fin k → Fin legs.length × Fin 4)
    (f : (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime) :
    momentumJet (List.ofFn p) f q =
      iteratedFDeriv ℝ k f q (fun i => Pi.single (p i).1 (Pi.single (p i).2 1)) := by
  have transport (a b : ℕ) (h : a = b)
      (v : Fin a → (Fin legs.length → Spacetime)) :
      iteratedFDeriv ℝ a f q v =
        iteratedFDeriv ℝ b f q (fun i => v (Fin.cast h.symm i)) := by
    subst b
    rfl
  unfold momentumJet
  rw [transport _ _ List.length_ofFn]
  congr 1
  funext i
  simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self]

/-- The actual reduced-coordinate jets determine the full derivative tensor
of the conserving extension, including all directions along the last leg. -/
theorem iteratedFDeriv_zero_of_reducedJets {legs : List (ExternalLeg G)}
    {f : (Fin legs.length → Spacetime) → ℂ}
    (smooth : ContDiff ℝ ∞ f)
    (extension : ∀ q, f q = f (conservingMomenta legs q)) (k : ℕ)
    (q : Fin legs.length → Spacetime)
    (jets : ∀ directions, ReducedDirections legs directions → directions.length = k →
      momentumJet directions f (reducedMomentumProjection legs q) = 0) :
    iteratedFDeriv ℝ k f q = 0 := by
  classical
  have heq : iteratedFDeriv ℝ k f q =
      (iteratedFDeriv ℝ k f (reducedMomentumProjection legs q)).compContinuousLinearMap
        (fun _ => reducedMomentumProjection legs) := by
    conv_lhs => rw [reduced_extension_projection extension]
    exact (reducedMomentumProjection legs).iteratedFDeriv_comp_right smooth q
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  rw [heq]
  apply doublePi_multilinear_zero
  intro p
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  by_cases hp : ∀ i, (p i).1.val + 1 < legs.length
  · have hdirs : ReducedDirections legs (List.ofFn p) := by
      intro d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact hp i
    have h := jets (List.ofFn p) hdirs List.length_ofFn
    rw [momentumJet_ofFn] at h
    simp_rw [reducedMomentumProjection_basis, if_pos (hp _)]
    exact h
  · obtain ⟨i, hi⟩ := not_forall.mp hp
    apply ContinuousMultilinearMap.map_coord_zero _ i
    rw [reducedMomentumProjection_basis, if_neg hi]

/-- Finite determinacy stated directly in the fixed background flow's actual
`ReducedDirections` and `momentumJet`, with no analyticity assumption. -/
theorem reducedJet_determinacy {legs : List (ExternalLeg G)}
    {f : (Fin legs.length → Spacetime) → ℂ}
    (smooth : ContDiff ℝ ∞ f)
    (extension : ∀ q, f q = f (conservingMomenta legs q)) (degree : ℕ)
    (highest : ∀ directions, ReducedDirections legs directions →
      directions.length = degree+1 → ∀ q, momentumJet directions f q = 0)
    (lower : ∀ directions, ReducedDirections legs directions →
      directions.length ≤ degree → momentumJet directions f 0 = 0) : f = 0 := by
  apply finiteJet_determinacy smooth degree
  · intro q
    exact iteratedFDeriv_zero_of_reducedJets smooth extension _ q
      (fun directions hd hk => highest directions hd hk _)
  · intro k hk
    apply iteratedFDeriv_zero_of_reducedJets smooth extension k 0
    intro directions hd hlen
    simpa using lower directions hd (by omega)

end YangMills.PerturbativeFlow
