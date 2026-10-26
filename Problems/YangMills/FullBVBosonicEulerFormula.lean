import Problems.YangMills.FullBVGhostAntifield

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Explicit finite word-removal polynomial for an even Euler coordinate.
Every retained descendant is an actual total derivative of the remaining
ordered word, with the integration-by-parts sign fixed by its jet order. -/
def bosonicEulerWord (field : ExternalLeg G) (source : List (LocalVertexLeg G)) : JetAlgebra G :=
  ∑ i : Fin source.length,
    if (source.get i).field = field then
      ((-1 : ℂ) ^ derivativeOrder (vertexJet (source.get i)).derivative) •
        totalDerivatives (vertexJet (source.get i)).derivative
          (monomial (source.take i.val ++ source.drop (i.val + 1))) else 0

theorem rightEuler_monomial_even (field : ExternalLeg G) (hfield : field.parity = false)
    (source : List (LocalVertexLeg G)) :
    rightEuler field (monomial source) = bosonicEulerWord field source := by
  classical
  let index (i : Fin source.length) := vertexJet (source.get i)
  let rest (i : Fin source.length) := monomial (source.take i.val ++ source.drop (i.val + 1))
  let S : Finset Multiindex := Finset.univ.image (fun i => (index i).derivative)
  have hp (alpha : Multiindex) :
      rightPartialJet ⟨field, alpha⟩ (monomial source) =
        ∑ i : Fin source.length,
          if (index i).field = field ∧ alpha = (index i).derivative then rest i else 0 := by
    rw [rightPartialJet]
    simp only [hfield, Bool.false_eq_true, if_false]
    rw [leftPartialJet_monomial_positional]
    unfold positionalJetDerivative
    apply Finset.sum_congr rfl
    intro i hi
    have he : (⟨field, alpha⟩ : Jet G) = index i ↔
        (index i).field = field ∧ alpha = (index i).derivative := by
      cases index i with
      | mk K beta => simp only [Jet.mk.injEq, eq_comm]
    simp only [index, rest] at he ⊢
    simp only [he, prefixSign, hfield, Bool.false_eq_true, if_false, pow_zero, one_smul]
  let F (i : Fin source.length) (alpha : Multiindex) : JetAlgebra G :=
    if (index i).field = field ∧ alpha = (index i).derivative then
      ((-1 : ℂ) ^ derivativeOrder alpha) • totalDerivatives alpha (rest i) else 0
  have hs (alpha : Multiindex) :
      ((-1 : ℂ) ^ derivativeOrder alpha) •
        totalDerivatives alpha (rightPartialJet ⟨field, alpha⟩ (monomial source)) =
          ∑ i : Fin source.length, F i alpha := by
    rw [hp, totalDerivatives_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : (index i).field = field ∧ alpha = (index i).derivative <;> simp [F, h]
  unfold rightEuler
  simp only [hs]
  have hsupport : Function.support (fun alpha => ∑ i : Fin source.length, F i alpha) ⊆ ↑S := by
    intro alpha ha
    by_contra hnot
    apply ha
    apply Finset.sum_eq_zero
    intro i hi
    have hn : alpha ≠ (index i).derivative := by
      intro he
      exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
    simp [F, hn]
  rw [finsum_eq_sum_of_support_subset _ hsupport, Finset.sum_comm]
  unfold bosonicEulerWord
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (index i).derivative]
  · by_cases hf : (index i).field = field <;> simp [F, hf, index, rest, vertexJet]
  · intro alpha ha hn
    simp [F, hn]
  · intro hn
    exact False.elim (hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- Actual vertex coefficient times its explicit finite Euler word. -/
def bosonicEulerVertex (field : ExternalLeg G) (g : ℝ) (v : LocalVertex G) : JetAlgebra G :=
  (v.coefficient * (g : ℂ)^v.couplingOrder) • bosonicEulerWord field v.legs

theorem rightEuler_densityOfVertex_even (field : ExternalLeg G)
    (hfield : field.parity = false) (g : ℝ) (v : LocalVertex G) :
    rightEuler field (densityOfVertex g v) = bosonicEulerVertex field g v := by
  rw [densityOfVertex, rightEuler_smul, rightEuler_monomial_even field hfield]
  rfl

def bosonicEulerVertices (field : ExternalLeg G) (g : ℝ)
    (vs : List (LocalVertex G)) : JetAlgebra G :=
  (vs.map (bosonicEulerVertex field g)).sum

theorem rightEuler_densityOfVertices_even (field : ExternalLeg G)
    (hfield : field.parity = false) (g : ℝ) (vs : List (LocalVertex G)) :
    rightEuler field (densityOfVertices g vs) = bosonicEulerVertices field g vs := by
  change (rightEulerLinear field) ((vs.map (densityOfVertex g)).sum) = _
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  change (vs.map (fun v => rightEuler field (densityOfVertex g v))).sum =
    (vs.map (bosonicEulerVertex field g)).sum
  simp only [rightEuler_densityOfVertex_even field hfield]

/-- Fully finite same-action gauge-antifield correction, computed from the
actual cubic, quartic, ghost and antifield vertices by explicit word removal.
This has no infinite Euler/partial summation and contains no supplied field
images, vertex dictionaries or normalization parameters. -/
def gaugeAntifieldCorrection {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (nu : Fin 4) (a : Fin G.dimension) : JetAlgebra G :=
  bosonicEulerVertices (.inl (.gauge nu a)) g
    (physicalActionVertices e ++ antifieldActionVertices e)

theorem master_characteristic_antigauge_finite {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) (nu : Fin 4) (a : Fin G.dimension) :
    stCharacteristic (masterActionDensity e g) (.inr (.gauge nu a)) =
      -(∑ mu : Fin 4, jet ⟨.inl (.gauge nu a), Pi.single mu 2⟩) +
        jet ⟨.inr (.antighost a), Pi.single nu 1⟩ + gaugeAntifieldCorrection e g nu a := by
  change rightEuler (.inl (.gauge nu a)) (masterActionDensity e g) = _
  conv_lhs => rw [masterActionDensity, rightEuler_add, interactionDensity]
  change stCharacteristic (freeActionDensity G) (.inr (.gauge nu a)) + _ = _
  rw [free_characteristic_antigauge,
    rightEuler_densityOfVertices_even (.inl (.gauge nu a)) (by rfl)]
  rfl

end YangMills.FullBV
