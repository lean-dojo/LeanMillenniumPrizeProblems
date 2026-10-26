import YangMills.FullBVBosonicEulerFormula
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem parity_one : parity (1 : JetAlgebra G) = 1 := by
  simp [parity, Algebra.TensorProduct.one_def]

theorem parity_monomial (source : List (LocalVertexLeg G)) :
    parity (monomial source) =
      ((-1 : ℂ)^((source.filter (fun k => k.field.parity)).length)) • monomial source := by
  induction source with
  | nil => simp [monomial, parity_one]
  | cons k source ih =>
      rw [monomial_cons, parity_mul, parity_jet, ih]
      by_cases hk : k.field.parity = true
      · simp only [vertexJet, hk, if_true, List.filter_cons, List.length_cons, pow_succ]
        let P : JetAlgebra G := jet (vertexJet k)
        let Q : JetAlgebra G := monomial source
        let r : ℂ := (-1 : ℂ)^((source.filter (fun k => k.field.parity)).length)
        change (-P) * (r • Q) = (r * (-1)) • (P * Q)
        calc
          _ = r • ((-P) * Q) := mul_smul_comm _ _ _
          _ = r • (-(P * Q)) := congrArg (fun X : JetAlgebra G => r • X) (neg_mul P Q)
          _ = _ := by rw [← neg_one_smul ℂ (P * Q), smul_smul]
      · simp [vertexJet, hk, List.filter_cons, mul_smul_comm]

theorem parity_densityOfVertex_even (g : ℝ) (v : LocalVertex G)
    (hv : v.parity = false) : parity (densityOfVertex g v) = densityOfVertex g v := by
  have hn : (v.legs.filter (fun k => k.field.parity)).length % 2 ≠ 1 := by
    exact of_decide_eq_false hv
  have hm : (v.legs.filter (fun k => k.field.parity)).length % 2 = 0 := by
    have hlt := Nat.mod_lt (v.legs.filter (fun k => k.field.parity)).length (by decide : 0 < 2)
    omega
  simp only [densityOfVertex, map_smul, parity_monomial,
    neg_one_pow_eq_pow_mod_two, hm, pow_zero, one_smul]

theorem parity_densityOfVertices_even (g : ℝ) (vs : List (LocalVertex G))
    (h : ∀ v ∈ vs, v.parity = false) :
    parity (densityOfVertices g vs) = densityOfVertices g vs := by
  unfold densityOfVertices
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact parity_densityOfVertex_even g v (h v hv)

theorem freeActionVertices_even (v : LocalVertex G) (hv : v ∈ freeActionVertices G) :
    v.parity = false := by
  simp [freeActionVertices] at hv
  aesop (add simp [LocalVertex.parity, ExternalLeg.parity, BasicField.fermionic])

theorem physicalActionVertices_even {B : InvariantForm G} (e : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ physicalActionVertices e) : v.parity = false := by
  simp [physicalActionVertices, actionMonomials, cubicMonomials, quarticMonomials,
    ghostMonomials, List.bind_eq_flatMap] at hv
  aesop (add simp [LocalVertex.parity, ExternalLeg.parity, BasicField.fermionic])

theorem antifieldActionVertices_even {B : InvariantForm G} (e : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ antifieldActionVertices e) : v.parity = false := by
  simp [antifieldActionVertices, List.bind_eq_flatMap] at hv
  aesop (add simp [LocalVertex.parity, ExternalLeg.parity, BasicField.fermionic])

/-- Actual evenness of the full fixed master action, including all physical,
shifted auxiliary, ghost and antifield source terms. -/
theorem parity_masterActionDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    parity (masterActionDensity e g) = masterActionDensity e g := by
  unfold masterActionDensity interactionDensity freeActionDensity
  rw [map_add, parity_densityOfVertices_even 0 _ freeActionVertices_even]
  congr 1
  apply parity_densityOfVertices_even
  intro v hv
  rcases List.mem_append.mp hv with hp | ha
  · exact physicalActionVertices_even e v hp
  · exact antifieldActionVertices_even e v ha

end YangMills.FullBV
