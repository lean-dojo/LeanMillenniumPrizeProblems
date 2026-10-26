import Problems.YangMills.LocalVertexPermutation

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.LegendreInsertionBridge
variable {G : CompactSimpleGaugeGroup}

/-- Literal Fourier factor and field Kronecker tensor of an assigned leg. -/
def assignedFourierFactor (source : LocalVertexLeg G) (external : ExternalLeg G × Spacetime) : ℂ :=
  if source.field = external.1 then
    (source.derivatives.map (fun μ => -Complex.I * (external.2 μ : ℂ))).prod else 0

/-- One signed source/external bijection in the actual functional derivative. -/
def assignedVertexTerm {n : ℕ} (source : Fin n → LocalVertexLeg G)
    (external : Fin n → ExternalLeg G × Spacetime) (π : Equiv.Perm (Fin n)) : ℂ :=
  parityExternalSign (fun i => (source i).field.parity) π *
    ∏ i : Fin n, assignedFourierFactor (source (π i)) (external i)

/-- Full all-arity head/erase factorization with the actual odd prefix sign. -/
theorem assignedVertexTerm_stableInsert {n : ℕ} (source : Fin (n+1) → LocalVertexLeg G)
    (external : Fin (n+1) → ExternalLeg G × Spacetime) (j : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) :
    assignedVertexTerm source external (stableInsertPermutation j σ) =
      (-1 : ℂ)^headCrossingCount (fun i => (source i).field.parity) j *
        assignedFourierFactor (source j) (external 0) *
          assignedVertexTerm (fun i => source (j.succAbove i)) (fun i => external i.succ) σ := by
  simp only [assignedVertexTerm, parityExternalSign_stableInsert, Fin.prod_univ_succ,
    stableInsertPermutation_zero, stableInsertPermutation_succ]
  ring

/-- Exact actual Grassmann/Fourier derivative as a sum of ALL signed
bijections, including arbitrary repeated even jets and exterior odd jets. -/
theorem localMonomialDerivative_permutation_sum (n : ℕ)
    (source : Fin n → LocalVertexLeg G) (external : Fin n → ExternalLeg G × Spacetime) :
    localMonomialDerivative (List.ofFn source) (List.ofFn external) =
      ∑ π : Equiv.Perm (Fin n), assignedVertexTerm source external π := by
  induction n with
  | zero =>
    simp [localMonomialDerivative, assignedVertexTerm, parityExternalSign, weightedInversionCount]
  | succ n ih =>
    rw [show List.ofFn external = external 0 :: List.ofFn (fun i => external i.succ) from
      List.ofFn_succ]
    change localMonomialDerivative (List.ofFn source)
      (((external 0).1, (external 0).2) :: List.ofFn (fun i => external i.succ)) = _
    simp only [localMonomialDerivative, List.get_ofFn]
    rw [← Equiv.sum_comp ((finCongr (List.length_ofFn (f := source))).symm)]
    simp only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_refl, Fin.val_cast, id_eq]
    rw [sum_stableInsertPermutation]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ofFn_take_drop_succAbove source j, ih]
    simp_rw [assignedVertexTerm_stableInsert]
    conv_rhs => rw [← Finset.mul_sum]
    by_cases hm : (source j).field = (external 0).1
    · simp only [hm, if_true, assignedFourierFactor]
      rw [← hm, ← headCrossingCount_prefix source (fun k => k.field.parity) j]
    · simp only [hm, if_false, assignedFourierFactor, mul_zero, zero_mul]

/-- The all-arity expansion applies literally to the same superalgebra
monomial amplitude used by the insertion engine. -/
theorem densityAmplitude_ofFn_permutation_sum (n : ℕ)
    (source : Fin n → LocalVertexLeg G) (fields : Fin n → ExternalLeg G)
    (q : Fin n → Spacetime) :
    FullBV.densityAmplitude (FullBV.monomial (List.ofFn source)) (List.ofFn fields)
      (fun i => q (Fin.cast (List.length_ofFn (f := fields)) i)) =
        ∑ π : Equiv.Perm (Fin n), assignedVertexTerm source (fun i => (fields i, q i)) π := by
  rw [FullBV.densityAmplitude_monomial]
  have he : List.ofFn (fun i : Fin (List.ofFn fields).length =>
      ((List.ofFn fields).get i, q (Fin.cast (List.length_ofFn (f := fields)) i))) =
      List.ofFn (fun i : Fin n => (fields i, q i)) := by
    rw [List.ofFn_congr (List.length_ofFn (f := fields))]
    simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_refl, id_eq]
  rw [he]
  exact localMonomialDerivative_permutation_sum n source (fun i => (fields i, q i))

/-- All actual field Kronecker tensors collapse to one fixed source word
for each source/external permutation. No color/species sum is replaced by
an arbitrary tensor. -/
theorem fieldKronecker_product (n : ℕ) (fields external : Fin n → ExternalLeg G)
    (π : Equiv.Perm (Fin n)) :
    (∏ i : Fin n, (if fields (π i) = external i then (1 : ℂ) else 0)) =
      if fields = (fun j => external (π.symm j)) then 1 else 0 := by
  classical
  by_cases he : fields = (fun j => external (π.symm j))
  · subst fields
    simp
  · rw [if_neg he]
    have hn : ∃ i, fields (π i) ≠ external i := by
      by_contra hn
      push Not at hn
      apply he
      funext j
      simpa only [π.apply_symm_apply] using hn (π.symm j)
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [if_neg hi])

theorem sum_fieldKronecker (n : ℕ) (external : Fin n → ExternalLeg G)
    (π : Equiv.Perm (Fin n)) (F : (Fin n → ExternalLeg G) → ℂ) :
    (∑ fields : Fin n → ExternalLeg G,
      (∏ i : Fin n, if fields (π i) = external i then (1 : ℂ) else 0) * F fields) =
        F (fun j => external (π.symm j)) := by
  classical
  simp_rw [fieldKronecker_product]
  simp

end YangMills.IntegratedNormalization
