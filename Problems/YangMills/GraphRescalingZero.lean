import Problems.YangMills.GraphRescalingDifferential

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 600000
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem graphRescale_zero_monomial (source : List (LocalVertexLeg G)) (hs : source ≠ []) :
    graphRescale 0 (monomial source) = 0 := by
  rw [graphRescale_monomial]
  have hn : source.length ≠ 0 := by
    cases source with
    | nil => exact False.elim (hs rfl)
    | cons k rest => simp
  simp [hn]

theorem graphRescale_zero_leftPartial_monomial (j : Jet G)
    (source : List (LocalVertexLeg G)) (hs : 2 ≤ source.length) :
    graphRescale 0 (leftPartialJet j (monomial source)) = 0 := by
  cases source with
  | nil => simp at hs
  | cons k source =>
    have hn : source ≠ [] := by intro h; simp [h] at hs
    rw [monomial_cons, leftPartialJet_mul, map_add, map_mul, map_mul]
    rw [graphRescale_zero_monomial source hn]
    by_cases hp : j.field.parity = true
    · simp [hp, graphRescale_parity]
    · simp [hp]

theorem graphRescale_zero_rightPartial_monomial (j : Jet G)
    (source : List (LocalVertexLeg G)) (hs : 2 ≤ source.length) :
    graphRescale 0 (rightPartialJet j (monomial source)) = 0 := by
  by_cases hp : j.field.parity = true
  · simp only [rightPartialJet, hp, if_true, LinearMap.comp_apply,
      graphRescale_parity, graphRescale_zero_leftPartial_monomial j source hs, map_zero]
  · simp only [rightPartialJet, hp, Bool.false_eq_true, if_false,
      graphRescale_zero_leftPartial_monomial j source hs]

theorem graphRescale_zero_rightEuler_monomial (field : ExternalLeg G)
    (source : List (LocalVertexLeg G)) (hs : 2 ≤ source.length) :
    graphRescale 0 (rightEuler field (monomial source)) = 0 := by
  have hm := (graphRescale 0).toAddMonoidHom.map_finsum
    (rightEulerSummands_finite field (monomial source))
  change graphRescale 0 (rightEuler field (monomial source)) =
    ∑ᶠ alpha : Multiindex, graphRescale 0 (((-1 : ℂ)^derivativeOrder alpha) •
      totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ (monomial source))) at hm
  rw [hm]
  simp only [map_smul, graphRescale_totalDerivatives,
    graphRescale_zero_rightPartial_monomial _ source hs, totalDerivatives_zeroInput, smul_zero,
    finsum_zero]

theorem graphRescale_zero_rightEuler_vertices (field : ExternalLeg G)
    (terms : List (LocalVertex G)) (hs : ∀ v ∈ terms, 2 ≤ v.legs.length) (g : ℝ) :
    graphRescale 0 (rightEuler field (densityOfVertices g terms)) = 0 := by
  induction terms with
  | nil => simp [densityOfVertices, rightEuler]
  | cons v vs ih =>
    have hv : 2 ≤ v.legs.length := hs v (by simp)
    have hvs : ∀ w ∈ vs, 2 ≤ w.legs.length := by
      intro w hw
      exact hs w (by simp [hw])
    change graphRescale 0 (rightEuler field (densityOfVertex g v + densityOfVertices g vs)) = 0
    rw [rightEuler_add, map_add, ih hvs, add_zero]
    simp only [densityOfVertex, rightEuler_smul, map_smul,
      graphRescale_zero_rightEuler_monomial field v.legs hv, smul_zero]

theorem graphRescale_zero_masterCharacteristic {B : InvariantForm G} (frame : ColorFrame B)
    (field : ExternalLeg G) :
    graphRescale 0 (stCharacteristic (masterActionDensity frame 1) field) = 0 := by
  have he (k : ExternalLeg G) : graphRescale 0 (rightEuler k (masterActionDensity frame 1)) = 0 := by
    rw [masterDensity_eq_vertices]
    apply graphRescale_zero_rightEuler_vertices
    intro v hv
    have hc := masterVertex_graph_count frame v hv
    omega
  cases field <;> simp only [stCharacteristic, map_neg, he, neg_zero]

/-- Endpoint-complete graph characteristic identity, including the abelian
zero-coupling point. This is a direct finite-word proof at zero, not a
continuity assumption about a cohomology classification. -/
theorem graphRescale_masterCharacteristic_all {B : InvariantForm G} (frame : ColorFrame B)
    (g : ℝ) (field : ExternalLeg G) :
    graphRescale (g : ℂ) (stCharacteristic (masterActionDensity frame 1) field) =
      (g : ℂ) • stCharacteristic (masterActionDensity frame g) field := by
  by_cases hg : g = 0
  · subst g
    simp only [Complex.ofReal_zero, graphRescale_zero_masterCharacteristic, zero_smul]
  · exact graphRescale_masterCharacteristic frame g hg field

/-- The actual master ST intertwining is polynomial and endpoint-complete;
it does not divide by the coupling. -/
theorem graphRescale_masterLocalST_all {B : InvariantForm G} (frame : ColorFrame B)
    (g : ℝ) (P : JetAlgebra G) :
    localST (masterActionDensity frame g) (graphRescale (g : ℂ) P) =
      graphRescale (g : ℂ) (localST (masterActionDensity frame 1) P) := by
  have hp (j : Jet G) : graphRescale (g : ℂ)
      (prolongedST (masterActionDensity frame 1) j) =
      (g : ℂ) • prolongedST (masterActionDensity frame g) j := by
    simp only [prolongedST, graphRescale_totalDerivatives,
      graphRescale_masterCharacteristic_all frame g, totalDerivatives_smul]
  induction P using polynomial_induction_jet with
  | zero => simp [localST_zero]
  | one => simp [localST_one]
  | add P Q hP hQ => simp only [map_add, localST_add, hP, hQ]
  | smul c P hP => simp only [map_smul, localST_smul, hP]
  | mul P j hP =>
    rw [map_mul, graphRescale_jet, mul_smul_comm, localST_smul,
      localST_mul_jet, hP, localST_mul_jet]
    simp only [map_add, map_mul, graphRescale_jet, hp, smul_add,
      smul_mul_assoc, mul_smul_comm]
    by_cases hj : j.field.parity = true <;> simp only [hj, if_true, graphRescale_parity]
    all_goals exact rfl

theorem masterLocalST_graphPrimitive_all {B : InvariantForm G} (frame : ColorFrame B)
    (loop : ℕ) (g : ℝ) (P : JetAlgebra G) :
    localST (masterActionDensity frame g) (graphPrimitive loop g P) =
      graphPrimitive loop g (localST (masterActionDensity frame 1) P) := by
  simp only [graphPrimitive, localST_smul, graphRescale_masterLocalST_all]

theorem graphPrimitive_integrated_exact_all {B : InvariantForm G} (frame : ColorFrame B)
    (loop : ℕ) (g : ℝ) (A P : JetAlgebra G)
    (h : localClass A = localSTFunctional (masterActionDensity frame 1) (localClass P)) :
    localClass (graphPrimitive loop g A) =
      localSTFunctional (masterActionDensity frame g) (localClass (graphPrimitive loop g P)) := by
  have ht := congrArg (graphRescaleFunctional (g : ℂ)) h
  simp only [localSTFunctional_localClass, graphRescaleFunctional_localClass] at ht
  rw [← graphRescale_masterLocalST_all frame g P] at ht
  have hs := congrArg (fun x : LocalFunctional G => (g : ℂ)^(2*loop-2) • x) ht
  simpa only [graphPrimitive, localClass, map_smul, localSTFunctional_localClass,
    localST_smul] using! hs

end YangMills.FullBV
