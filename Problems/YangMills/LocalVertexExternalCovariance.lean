import Problems.YangMills.LocalVertexAmplitudePolarization
import Problems.YangMills.FourierTaylorSigns

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators ContDiff
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.LegendreInsertionBridge
variable {G : CompactSimpleGaugeGroup}

/-- Universal Koszul composition, derived from the already proved actual
partition-sign factorization with an injective block assignment. -/
theorem parityExternalSign_comp {n : ℕ} (p : Fin n → Bool)
    (a e : Equiv.Perm (Fin n)) :
    parityExternalSign p (a * e) =
      parityExternalSign (fun i => p (a i)) e * parityExternalSign p a := by
  have hi : parityInternalSign (fun i => p (a i)) a e = 1 := by
    unfold parityInternalSign
    have hz : (∑ i : Fin n, ∑ j : Fin n,
        if i < j ∧ e j < e i ∧ a (e i) = a (e j) ∧
          p (a (e i)) = true ∧ p (a (e j)) = true then (1 : ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      have hn : ¬ (i < j ∧ e j < e i ∧ a (e i) = a (e j) ∧
          p (a (e i)) = true ∧ p (a (e j)) = true) := by
        intro h
        have he := e.injective (a.injective h.2.2.1)
        omega
      rw [if_neg hn]
    rw [hz, pow_zero]
  have hf := scalar_parity_factorization (fun i => p (a i)) a e
  rw [hi, mul_one] at hf
  exact hf

/-- The actual assigned Fourier factors are covariant when the external
word is permuted. Nonmatching field words vanish before signs are compared. -/
theorem assignedVertexTerm_external {n : ℕ} (source : Fin n → LocalVertexLeg G)
    (external : Fin n → ExternalLeg G × Spacetime) (a e : Equiv.Perm (Fin n)) :
    assignedVertexTerm source (fun i => external (e i)) (a * e) =
      parityExternalSign (fun i => (external i).1.parity) e *
        assignedVertexTerm source external a := by
  classical
  unfold assignedVertexTerm
  have hr := Equiv.prod_comp e
    (fun j => assignedFourierFactor (source (a j)) (external j))
  simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hr ⊢
  rw [hr, parityExternalSign_comp]
  by_cases hm : ∀ j, (source (a j)).field = (external j).1
  · have hp : (fun j => (source (a j)).field.parity) =
        fun j => (external j).1.parity := funext (fun j => congrArg ExternalLeg.parity (hm j))
    rw [hp]
    ring
  · obtain ⟨j, hj⟩ := not_forall.mp hm
    have hz : (∏ i : Fin n, assignedFourierFactor (source (a i)) (external i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp only [assignedFourierFactor, if_neg hj])
    rw [hz]
    ring

/-- Full independent-momentum graded covariance of the literal all-arity
ordered monomial derivative, including repeated exterior generators. -/
theorem localMonomialDerivative_external (n : ℕ)
    (source : Fin n → LocalVertexLeg G)
    (external : Fin n → ExternalLeg G × Spacetime) (e : Equiv.Perm (Fin n)) :
    localMonomialDerivative (List.ofFn source) (List.ofFn fun i => external (e i)) =
      parityExternalSign (fun i => (external i).1.parity) e *
        localMonomialDerivative (List.ofFn source) (List.ofFn external) := by
  rw [localMonomialDerivative_permutation_sum, localMonomialDerivative_permutation_sum]
  rw [← Equiv.sum_comp (Equiv.mulRight e)]
  simp only [Equiv.coe_mulRight, assignedVertexTerm_external, Finset.mul_sum]

/-- Full independent-momentum graded covariance of every actual local vertex. -/
theorem localVertexAmplitude_graded (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    localVertexAmplitude v g (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e * localVertexAmplitude v g legs q := by
  classical
  have he : (List.ofFn fun i : Fin (permutedLegs legs e).length =>
      ((permutedLegs legs e).get i, permutedMomenta legs e q i)) =
      List.ofFn (fun i : Fin legs.length => (legs.get (e i), q (e i))) := by
    rw [List.ofFn_congr (show (permutedLegs legs e).length = legs.length by
      simp only [permutedLegs, List.length_ofFn])]
    simp only [permutedLegs, permutedMomenta, List.get_ofFn, Fin.cast_cast,
      Fin.cast_refl, id_eq]
    apply congrArg List.ofFn
    funext i
    apply Prod.ext
    · rfl
    · apply congrArg q
      apply congrArg e
      apply Fin.ext
      rfl
  unfold localVertexAmplitude
  rw [he]
  by_cases ha : v.legs.length = legs.length
  · have hs : v.legs = List.ofFn (fun j => v.legs.get (Fin.cast ha.symm j)) := by
      conv_lhs => rw [← List.ofFn_get v.legs]
      rw [List.ofFn_congr ha]
    have hx := localMonomialDerivative_external legs.length
      (fun j => v.legs.get (Fin.cast ha.symm j)) (fun i => (legs.get i, q i)) e
    rw [← hs] at hx
    rw [hx]
    change _ * (permutationSign legs e * _) = _
    ring
  · have h0 := localMonomialDerivative_arity_zero v.legs
      (List.ofFn fun i : Fin legs.length => (legs.get (e i), q (e i)))
      (by simpa only [List.length_ofFn] using ha)
    have h1 := localMonomialDerivative_arity_zero v.legs
      (List.ofFn fun i : Fin legs.length => (legs.get i, q i))
      (by simpa only [List.length_ofFn] using ha)
    rw [h0, h1]
    ring

/-- Full graded covariance for the actual finite local density used in the
normalization map, before any conserving-momentum extension. -/
theorem densityAmplitude_vertices_graded (vertices : List (LocalVertex G)) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (e : Equiv.Perm (Fin legs.length)) :
    FullBV.densityAmplitude (FullBV.densityOfVertices g vertices)
        (permutedLegs legs e) (permutedMomenta legs e q) =
      permutationSign legs e *
        FullBV.densityAmplitude (FullBV.densityOfVertices g vertices) legs q := by
  rw [FullBV.densityAmplitude_vertices]
  unfold localPolynomialAmplitude
  induction vertices with
  | nil => simp
  | cons v rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [localVertexAmplitude_graded, ih, mul_add]

/-- Every actual local superpolynomial amplitude is smooth in independent
momenta: its coefficients are fixed finite jet derivatives, and momentum
dependence is a finite polynomial. -/
theorem densityAmplitude_smooth (P : FullBV.JetAlgebra G) (legs : List (ExternalLeg G)) :
    ContDiff ℝ ∞ (FullBV.densityAmplitude P legs) := by
  classical
  unfold FullBV.densityAmplitude
  apply ContDiff.sum
  intro a ha
  split_ifs
  · apply contDiff_const.mul
    apply contDiff_prod
    intro i hi
    unfold FullBV.jetMomentumPhase
    apply contDiff_prod
    intro μ hμ
    apply ContDiff.pow
    apply contDiff_const.mul
    let C : (Fin legs.length → Spacetime) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj i : (Fin legs.length → Spacetime) →L[ℝ] Spacetime)
    exact Complex.ofRealCLM.contDiff.comp C.contDiff
  · exact contDiff_const

end YangMills.IntegratedNormalization
