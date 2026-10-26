import Problems.YangMills.CohomologicalScaleInsertion

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace YangMills.LegendreInsertionBridge
open YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.Legendre YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

theorem meanFieldRoot_at_free (F : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (loop : ℕ) (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    meanFieldRoot F s 0 loop root legs q =
      if loop = 0 then identityRoot root legs else 0 := by
  cases root <;> simp [meanFieldRoot, hF]

theorem meanFieldCompose_zero_empty (F A : FormalAmplitude G) (s : CutoffScales)
    (q : Fin ([] : List (ExternalLeg G)).length → Spacetime) :
    meanFieldCompose A F s 0 0 [] q = A 0 0 [] q := by
  simp only [meanFieldCompose, List.length_nil, Finset.univ_unique,
    Finset.sum_singleton]
  simp [substitutionSummand, partitionBlock, partitionSign, rootLegs]
  congr 1
  funext i
  exact Fin.elim0 i

theorem meanFieldCompose_zero_singleton (F A : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (K : ExternalLeg G) (q : Fin ([K] : List (ExternalLeg G)).length → Spacetime) :
    meanFieldCompose A F s 0 0 [K] q = A 0 0 [K] q := by
  simp only [meanFieldCompose, List.length_cons, List.length_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp [substitutionSummand, partitionBlock, partitionSign, meanFieldRoot_at_free F s hF]
  have hs : selectedLegs [K] ({0} : Finset (Fin 1)) = [K] := by
    simp [selectedLegs, selectedIndices]
  simp only [hs, identityRoot, List.cons.injEq, and_true]
  rw [Finset.sum_eq_single (fun _ : Fin 1 => K)]
  · dsimp only
    rw [if_pos rfl, mul_one]
    change A 0 0 [K] _ = A 0 0 [K] q
    congr 1
    funext i
    fin_cases i
    simp [rootMomenta, partitionBlock, selectedMomentum]
  · intro b _ hb
    have hbk : K ≠ b 0 := by
      intro h
      apply hb
      funext i
      fin_cases i
      exact h.symm
    simp [hbk]
  · simp


/-- The strictly lower outer-coupling contribution in the actual finite
partition substitution. It uses the full outer coefficient family. -/
def lowerComposition (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ k : Fin (legs.length+1), ∑ assignment : Fin legs.length → Fin k.val,
    ∑ roots : Fin k.val → ExternalLeg G,
    ∑ gOrders : Fin (k.val+1) → Fin (order+1),
    ∑ hOrders : Fin (k.val+1) → Fin (loop+1),
      if (gOrders 0).val < order then
        substitutionSummand A F s order loop legs q k.val assignment roots gOrders hOrders
      else 0

/-- The only remaining identity-root normalization is a finite diagonal
partition sum. It is independent of any proposed insertion inverse. -/
def diagonalComposition (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ k : Fin (legs.length+1), ∑ assignment : Fin legs.length → Fin k.val,
    ∑ roots : Fin k.val → ExternalLeg G,
    ∑ gOrders : Fin (k.val+1) → Fin (order+1),
    ∑ hOrders : Fin (k.val+1) → Fin (loop+1),
      if (gOrders 0).val = order then
        substitutionSummand A F s order loop legs q k.val assignment roots gOrders hOrders
      else 0

theorem substitutionSummand_congr_outer (A H F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (gOrders : Fin (k+1) → Fin (order+1)) (hOrders : Fin (k+1) → Fin (loop+1))
    (h : A (gOrders 0).val (hOrders 0).val (rootLegs roots)
      (rootMomenta legs q assignment roots) =
      H (gOrders 0).val (hOrders 0).val (rootLegs roots)
      (rootMomenta legs q assignment roots)) :
    substitutionSummand A F s order loop legs q k assignment roots gOrders hOrders =
      substitutionSummand H F s order loop legs q k assignment roots gOrders hOrders := by
  simp only [substitutionSummand, h]

theorem meanFieldCompose_split (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    meanFieldCompose A F s order loop legs q =
      lowerComposition A F s order loop legs q + diagonalComposition A F s order loop legs q := by
  unfold meanFieldCompose lowerComposition diagonalComposition
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro go _
  apply Finset.sum_congr rfl
  intro ho _
  by_cases h : (go 0).val < order
  · have he : (go 0).val ≠ order := by omega
    simp [h, he]
  · have he : (go 0).val = order := by have hi := (go 0).isLt; omega
    simp [he]

/-- In a diagonal coupling term all root coupling orders are zero.
Consequently ONLY the exact identity mean-field roots enter; interactions
at positive coupling do not enter this finite normalization problem. -/
theorem substitutionSummand_diagonal_free (A F : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (go : Fin (k+1) → Fin (order+1)) (ho : Fin (k+1) → Fin (loop+1))
    (hdiag : (go 0).val = order) :
    substitutionSummand A F s order loop legs q k assignment roots go ho =
      substitutionSummand A 0 s order loop legs q k assignment roots go ho := by
  unfold substitutionSummand
  split_ifs with h
  · have hz : (∑ b : Fin k, (go b.succ).val) = 0 := by
      have hh := h.2.1
      rw [Fin.sum_univ_succ] at hh
      omega
    congr 1
    apply Finset.prod_congr rfl
    intro b _
    have hb : (go b.succ).val = 0 := by
      have hl := Finset.single_le_sum (fun (i : Fin k) _ => Nat.zero_le (go i.succ).val)
        (Finset.mem_univ b)
      omega
    rw [hb, meanFieldRoot_at_free F s hF]
    rw [meanFieldRoot_at_free 0 s (by intros; rfl)]
  · rfl

theorem diagonalComposition_free (A F : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    diagonalComposition A F s order loop legs q = diagonalComposition A 0 s order loop legs q := by
  unfold diagonalComposition
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro go _
  apply Finset.sum_congr rfl
  intro ho _
  split_ifs with h
  · exact substitutionSummand_diagonal_free A F s hF order loop legs q k.val assignment roots go ho h
  · rfl

/-- A lower outer-coupling term has a positive-coupling root. For the
identity background that exact root is zero, so every such term vanishes. -/
theorem substitutionSummand_free_lower (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (go : Fin (k+1) → Fin (order+1)) (ho : Fin (k+1) → Fin (loop+1))
    (hlower : (go 0).val < order) :
    substitutionSummand A 0 s order loop legs q k assignment roots go ho = 0 := by
  unfold substitutionSummand
  split_ifs with h
  · have hex : ∃ b : Fin k, (go b.succ).val ≠ 0 := by
      by_contra hn
      push Not at hn
      have hh := h.2.1
      rw [Fin.sum_univ_succ] at hh
      simp only [hn, Finset.sum_const_zero, add_zero] at hh
      omega
    obtain ⟨b, hb⟩ := hex
    have hroot : meanFieldRoot (0 : FormalAmplitude G) s (go b.succ).val
        (ho b.succ).val (roots b) (selectedLegs legs (partitionBlock assignment b))
        (selectedMomenta legs (partitionBlock assignment b) q) = 0 := by
      cases hK : roots b <;> simp [meanFieldRoot, hb]
    have hz : (∏ b : Fin k,
        meanFieldRoot (0 : FormalAmplitude G) s (go b.succ).val (ho b.succ).val
          (roots b) (selectedLegs legs (partitionBlock assignment b))
          (selectedMomenta legs (partitionBlock assignment b) q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) hroot
    rw [hz, mul_zero]
  · rfl

theorem lowerComposition_free (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    lowerComposition A 0 s order loop legs q = 0 := by
  unfold lowerComposition
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro assignment _
  apply Finset.sum_eq_zero
  intro roots _
  apply Finset.sum_eq_zero
  intro go _
  apply Finset.sum_eq_zero
  intro ho _
  split_ifs with h
  · exact substitutionSummand_free_lower A s order loop legs q k.val assignment roots go ho h
  · rfl

theorem diagonalComposition_eq_free_compose (A : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    diagonalComposition A 0 s order loop legs q = meanFieldCompose A 0 s order loop legs q := by
  rw [meanFieldCompose_split, lowerComposition_free, zero_add]

/-- The defining recursion really is subtraction of exactly the strictly
lower-coupling contribution of its OWN computed coefficients. -/
theorem insertionGammaCoeff_recurrence (F I : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    insertionGammaCoeff F I s order loop legs q = I order loop legs q -
      lowerComposition (insertionGammaCoeff F I s) F s order loop legs q := by
  conv_lhs => rw [insertionGammaCoeff]
  apply congrArg (fun z : ℂ => I order loop legs q - z)
  unfold lowerComposition
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro go _
  apply Finset.sum_congr rfl
  intro ho _
  split_ifs with h
  · apply substitutionSummand_congr_outer
    simp only [h, dite_true]
  · rfl

theorem lowerComposition_congr_prefix (A H F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hprefix : ∀ r, r < order → ∀ l ls ps, A r l ls ps = H r l ls ps) :
    lowerComposition A F s order loop legs q = lowerComposition H F s order loop legs q := by
  unfold lowerComposition
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro go _
  apply Finset.sum_congr rfl
  intro ho _
  split_ifs with h
  · apply substitutionSummand_congr_outer
    exact hprefix (go 0).val h _ _ _
  · rfl

/-- There is no witness freedom in any inverse satisfying the correct
identity-root normalization: its coefficients MUST be this recursion. -/
theorem insertion_inverse_unique (F I H : FormalAmplitude G) (s : CutoffScales)
    (solution : meanFieldCompose H F s = I)
    (diagonal : ∀ order loop legs q,
      diagonalComposition H F s order loop legs q = H order loop legs q) :
    H = insertionGammaCoeff F I s := by
  have all : ∀ order loop legs q, H order loop legs q = insertionGammaCoeff F I s order loop legs q := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro loop legs q
      have hs : lowerComposition H F s order loop legs q + H order loop legs q = I order loop legs q := by
        rw [← diagonal order loop legs q, ← meanFieldCompose_split, solution]
      have hl := lowerComposition_congr_prefix H (insertionGammaCoeff F I s) F s order loop legs q ih
      rw [insertionGammaCoeff_recurrence, ← hl]
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hs)
  funext order loop legs q
  exact all order loop legs q

/-- Once the universal identity-root diagonal normalization is established,
ALL coupling/loop orders of the concrete recursive insertion inverse follow.
The hypothesis is a finite partition identity, not an assumed inverse or a
candidate 1PI insertion. -/
theorem insertion_inverse_of_diagonal (F I : FormalAmplitude G) (s : CutoffScales)
    (diagonal : ∀ order loop legs q,
      diagonalComposition (insertionGammaCoeff F I s) F s order loop legs q =
        insertionGammaCoeff F I s order loop legs q) :
    meanFieldCompose (insertionGammaCoeff F I s) F s = I := by
  funext order loop legs q
  rw [meanFieldCompose_split, diagonal, insertionGammaCoeff_recurrence]
  ring


/-- General all-order inversion reduced to the universal FREE identity-root
partition normalization. The only background hypothesis is its actual
vanishing coupling-zero jet, exactly as required by the fixed source action. -/
theorem insertion_inverse_of_free_identity (F I : FormalAmplitude G) (s : CutoffScales)
    (hF : ∀ loop legs q, F 0 loop legs q = 0)
    (identity : meanFieldCompose (insertionGammaCoeff F I s) 0 s =
      insertionGammaCoeff F I s) :
    meanFieldCompose (insertionGammaCoeff F I s) F s = I := by
  apply insertion_inverse_of_diagonal
  intro order loop legs q
  rw [diagonalComposition_free _ F s hF,
    diagonalComposition_eq_free_compose, identity]



theorem directionalLegendre_of_free_identity (A I : ℝ → FlowFamily G) (s : CutoffScales)
    (free : ∀ loop legs q, A 0 loop s.infrared s.ultraviolet legs q = 0)
    (identity : meanFieldCompose (directionalGamma A I s) 0 s = directionalGamma A I s) :
    DirectionalLegendreCompatible A I s := by
  apply insertion_inverse_of_free_identity
  · intro loop legs q
    simpa [flowJet] using free loop legs q
  · exact identity


end YangMills.LegendreInsertionBridge
