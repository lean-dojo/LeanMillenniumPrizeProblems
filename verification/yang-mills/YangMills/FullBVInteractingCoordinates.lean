import YangMills.FullBVMasterEquations

/-! Nonlinear Hamiltonian characteristics of the same master action. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem parity_mul (P Q : JetAlgebra G) : parity (P * Q) = parity P * parity Q := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P R hP hR => simp [add_mul, hP, hR]
  | tmul p u =>
      induction Q using TensorProduct.induction_on with
      | zero => simp
      | add Q R hQ hR => simp [mul_add, hQ, hR]
      | tmul q v => simp [parity, Algebra.TensorProduct.tmul_mul_tmul]

/-- Differentiating a word with no occurrence of the requested species is
zero, including all jet orders. This will remove physical-action vertices
from antifield Euler differentiation without any Ward assumption. -/
theorem leftPartialJet_monomial_absent (j : Jet G) (source : List (LocalVertexLeg G))
    (h : ∀ k ∈ source, k.field ≠ j.field) :
    leftPartialJet j (monomial source) = 0 := by
  classical
  rw [leftPartialJet_monomial]
  induction source with
  | nil => rfl
  | cons k source ih =>
      have hhead : j ≠ vertexJet k := by
        intro he
        exact h k (by simp) ((congrArg Jet.field he).symm)
      simp only [jetWordDerivative, hhead, if_false]
      rw [ih (by intro v hv; exact h v (by simp [hv]))]
      simp

theorem rightEuler_densityOfVertices_absent (field : ExternalLeg G) (g : ℝ)
    (vs : List (LocalVertex G))
    (h : ∀ v ∈ vs, ∀ k ∈ v.legs, k.field ≠ field) :
    rightEuler field (densityOfVertices g vs) = 0 := by
  classical
  have hv (v : LocalVertex G) (hm : v ∈ vs) : rightEuler field (densityOfVertex g v) = 0 := by
    rw [densityOfVertex, rightEuler_smul]
    have hp (alpha : Multiindex) : rightPartialJet ⟨field, alpha⟩ (monomial v.legs) = 0 := by
      by_cases hf : field.parity = true <;>
        simp [rightPartialJet, hf, LinearMap.comp_apply, leftPartialJet_monomial_absent (⟨field, alpha⟩ : Jet G) v.legs (h v hm)]
    simp [rightEuler, hp]
  unfold densityOfVertices
  change (rightEulerLinear field) ((vs.map (densityOfVertex g)).sum) = 0
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply List.sum_eq_zero
  intro v hv'
  rcases List.mem_map.mp hv' with ⟨v, hm, rfl⟩
  exact hv v hm

/-- All physical interaction terms have basic legs. Thus the antifield
Hamiltonian variation comes exclusively from the fixed BV source vertices. -/
theorem rightEuler_physicalAction (K : BasicField G) {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    rightEuler (.inr K) (densityOfVertices g (physicalActionVertices e)) = 0 := by
  apply rightEuler_densityOfVertices_absent
  intro v hv k hk
  rcases List.mem_map.mp hv with ⟨m, hm, rfl⟩
  rcases List.mem_map.mp hk with ⟨leg, hleg, rfl⟩
  simp

/-- An even cubic BV source word has no independent variation rule: its
antifield Euler derivative is the prolonged actual two-field product. -/
theorem rightEuler_basicPair_antifield (K H i j : BasicField G)
    (alpha beta gamma : Multiindex)
    (he : (if i.fermionic then !j.fermionic else j.fermionic) = !H.fermionic) :
    rightEuler (.inr K)
      ((jet ⟨.inl i, alpha⟩ * jet ⟨.inl j, beta⟩) * jet ⟨.inr H, gamma⟩) =
      if H = K then ((-1 : ℂ) ^ derivativeOrder gamma) •
        totalDerivatives gamma (jet ⟨.inl i, alpha⟩ * jet ⟨.inl j, beta⟩) else 0 := by
  classical
  have hp (delta : Multiindex) :
      rightPartialJet ⟨.inr K, delta⟩
        ((jet ⟨.inl i, alpha⟩ * jet ⟨.inl j, beta⟩) * jet ⟨.inr H, gamma⟩) =
        if H = K ∧ delta = gamma then jet ⟨.inl i, alpha⟩ * jet ⟨.inl j, beta⟩ else 0 := by
    simp only [rightPartialJet, ite_apply, LinearMap.comp_apply]
    by_cases hd : delta = gamma
    all_goals
      by_cases hK : H = K
      · subst H
        cases hi : i.fermionic <;> cases hj : j.fermionic <;> cases hk : K.fermionic
        all_goals
          simp_all [rightPartialJet, leftPartialJet_mul, leftPartialJet_jet,
          ExternalLeg.parity, parity_mul, parity_jet, Jet.mk.injEq, hd]
      · have hK' : K ≠ H := Ne.symm hK
        by_cases hf : (ExternalLeg.parity (.inr K)) = true <;>
          simp [rightPartialJet, hf, LinearMap.comp_apply, leftPartialJet_mul, leftPartialJet_jet,
            Jet.mk.injEq, hK, hK']
  unfold rightEuler
  simp only [hp]
  rw [finsum_eq_single _ gamma (by intro delta hd; simp [hd])]
  by_cases hK : H = K <;> simp [hK]

theorem densityOfVertex_triple (c : ℂ) (g : ℝ) (i j k : LocalVertexLeg G) :
    densityOfVertex g (⟨c, 1, [i,j,k]⟩ : LocalVertex G) =
      (c * (g : ℂ)) • ((jet (vertexJet i) * jet (vertexJet j)) * jet (vertexJet k)) := by
  simp [densityOfVertex, monomial, vertexJet, mul_assoc]

def nonlinearSourceDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  ∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, (
    ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
      ((jet ⟨.inl (.ghost b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) * jet ⟨.inr (.ghost a), 0⟩) +
    ∑ mu : Fin 4, (
      (-(structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) * jet ⟨.inr (.gauge mu a), 0⟩) +
      (Complex.I * (structureConstant e a b c : ℂ) * (g : ℂ)) •
        ((jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) *
          jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩)))

/-- Exact expansion of the engine's nonlinear BV source vertex list. -/
theorem antifieldDensity_eq_nonlinearSource {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (antifieldActionVertices e) = nonlinearSourceDensity e g := by
  unfold densityOfVertices antifieldActionVertices
  simp only [List.bind_eq_flatMap]
  simp only [List.map_flatMap, sum_list_flatMap, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    densityOfVertex_triple, vertexJet_nil, vertexJet_single]
  rfl

theorem densityOfVertices_append (g : ℝ) (vs ws : List (LocalVertex G)) :
    densityOfVertices g (vs ++ ws) = densityOfVertices g vs + densityOfVertices g ws := by
  simp [densityOfVertices]

theorem master_basic_characteristic {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (K : BasicField G) :
    stCharacteristic (masterActionDensity e g) (.inl K) =
      stCharacteristic (freeActionDensity G) (.inl K) -
        rightEuler (.inr K) (nonlinearSourceDensity e g) := by
  simp only [stCharacteristic, masterActionDensity, interactionDensity,
    rightEuler_add, densityOfVertices_append, rightEuler_physicalAction,
    antifieldDensity_eq_nonlinearSource, zero_add]
  all_goals abel

theorem rightEuler_ghostSource (K : BasicField G) (a b c : Fin G.dimension) :
    rightEuler (.inr K)
      ((jet ⟨.inl (.ghost b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) * jet ⟨.inr (.ghost a), 0⟩) =
      if .ghost a = K then jet ⟨.inl (.ghost b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩ else 0 := by
  simpa [derivativeOrder_zero] using
    rightEuler_basicPair_antifield K (.ghost a) (.ghost b) (.ghost c) 0 0 0 (by rfl)

theorem rightEuler_gaugeSource (K : BasicField G) (mu : Fin 4) (a b c : Fin G.dimension) :
    rightEuler (.inr K)
      ((jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) * jet ⟨.inr (.gauge mu a), 0⟩) =
      if .gauge mu a = K then jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩ else 0 := by
  simpa [derivativeOrder_zero] using
    rightEuler_basicPair_antifield K (.gauge mu a) (.gauge mu b) (.ghost c) 0 0 0 (by rfl)

theorem rightEuler_auxiliarySource (K : BasicField G) (mu : Fin 4) (a b c : Fin G.dimension) :
    rightEuler (.inr K)
      ((jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) *
        jet ⟨.inr (.auxiliary a), Pi.single mu 1⟩) =
      if .auxiliary a = K then -totalDerivatives (Pi.single mu 1)
        (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) else 0 := by
  simpa [derivativeOrder_single] using
    rightEuler_basicPair_antifield K (.auxiliary a) (.gauge mu b) (.ghost c)
      0 0 (Pi.single mu 1) (by rfl)

/-- Full shifted antighost transformation; physical and all nonlinear source
vertices contribute zero to this coordinate, rather than being omitted. -/
theorem master_characteristic_antighost {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inl (.antighost a)) =
      Complex.I • jet ⟨.inl (.auxiliary a), 0⟩ +
        ∑ mu : Fin 4, jet ⟨.inl (.gauge mu a), Pi.single mu 1⟩ := by
  rw [master_basic_characteristic, free_characteristic_antighost]
  simp [nonlinearSourceDensity, rightEuler_sum, rightEuler_add, rightEuler_smul,
    rightEuler_ghostSource, rightEuler_gaugeSource, rightEuler_auxiliarySource]

theorem master_characteristic_gauge {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (mu : Fin 4) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)) =
      jet ⟨.inl (.ghost a), Pi.single mu 1⟩ +
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a b c : ℂ) * (g : ℂ)) •
          (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) := by
  rw [master_basic_characteristic, free_characteristic_gauge]
  simp [nonlinearSourceDensity, rightEuler_sum, rightEuler_add, rightEuler_smul,
    rightEuler_ghostSource, rightEuler_gaugeSource, rightEuler_auxiliarySource,
    ite_and, Finset.sum_add_distrib, neg_mul, ← Finset.sum_neg_distrib]
  have hn : (∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
      (-((structureConstant e a b c : ℂ) * (g : ℂ))) •
        (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩)) =
      -(∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((structureConstant e a b c : ℂ) * (g : ℂ)) •
          (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    exact neg_smul ((structureConstant e a b c : ℂ) * (g : ℂ))
      (jet (G := G) ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩)
  rw [hn, sub_neg_eq_add]

theorem master_characteristic_ghost {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inl (.ghost a)) =
      -(∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
        ((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          (jet ⟨.inl (.ghost b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩)) := by
  rw [master_basic_characteristic, free_characteristic_ghost]
  simp [nonlinearSourceDensity, rightEuler_sum, rightEuler_add, rightEuler_smul,
    rightEuler_ghostSource, rightEuler_gaugeSource, rightEuler_auxiliarySource]

theorem master_characteristic_auxiliary {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inl (.auxiliary a)) =
      Complex.I • ∑ mu : Fin 4, jet ⟨.inl (.ghost a), Pi.single mu 2⟩ +
      ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ mu : Fin 4,
        (Complex.I * (structureConstant e a b c : ℂ) * (g : ℂ)) •
          totalDerivatives (Pi.single mu 1)
            (jet ⟨.inl (.gauge mu b), 0⟩ * jet ⟨.inl (.ghost c), 0⟩) := by
  rw [master_basic_characteristic, free_characteristic_auxiliary]
  simp [nonlinearSourceDensity, rightEuler_sum, rightEuler_add, rightEuler_smul,
    rightEuler_ghostSource, rightEuler_gaugeSource, rightEuler_auxiliarySource,
    ← Finset.sum_neg_distrib]
  all_goals try simp only [neg_one_smul ℂ, smul_neg, neg_smul, Finset.sum_neg_distrib, neg_neg, sub_neg_eq_add]

end YangMills.FullBV
