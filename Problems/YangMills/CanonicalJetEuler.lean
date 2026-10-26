import Problems.YangMills.CanonicalEulerExact
import Problems.YangMills.FullBVIntegratedHamiltonian

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.FieldParameter
variable {G : CompactSimpleGaugeGroup}

/-- Actual even derivation giving the canonical weight of every descendant
of each basic field and its inverse-dual antifield. -/
theorem coordinateDifferential_finsum_jet (F : Jet G → JetAlgebra G) (P : JetAlgebra G) :
    coordinateDifferential (fun j => F j.val) (fun j => F j.val) P = ∑ᶠ j : Jet G, F j * leftPartialJet j P := by
  classical
  have he : (∑ᶠ j : EvenJet G, F j.val * evenPartial j P) =
      ∑ᶠ j : Jet G, if j.field.parity = false then F j * leftPartialJet j P else 0 := by
    calc
      _ = ∑ᶠ j : EvenJet G, F j.val * leftPartialJet j.val P := by
        apply finsum_congr
        intro j
        simp [leftPartialJet, j.property]
      _ = _ := by
        simpa only [finsum_eq_if] using!
          (finsum_subtype_eq_finsum_cond
            (f := fun j : Jet G => F j * leftPartialJet j P)
            (fun j => j.field.parity = false))
  have ho : (∑ᶠ j : OddJet G, F j.val * oddPartial j P) =
      ∑ᶠ j : Jet G, if j.field.parity = true then F j * leftPartialJet j P else 0 := by
    calc
      _ = ∑ᶠ j : OddJet G, F j.val * leftPartialJet j.val P := by
        apply finsum_congr
        intro j
        simp [leftPartialJet, j.property]
      _ = _ := by
        simpa only [finsum_eq_if] using!
          (finsum_subtype_eq_finsum_cond
            (f := fun j : Jet G => F j * leftPartialJet j P)
            (fun j => j.field.parity = true))
  change (∑ᶠ j : EvenJet G, F j.val * evenPartial j P) +
    (∑ᶠ j : OddJet G, F j.val * oddPartial j P) = _
  rw [he,ho, ← finsum_add_distrib
    (jetConditionalSummands_finite (F) P (fun j => j.field.parity = false))
    (jetConditionalSummands_finite (F) P (fun j => j.field.parity = true))]
  apply finsum_congr
  intro j
  cases j.field.parity <;> simp

def jetEuler (weights : BasicScales) (P : JetAlgebra G) : JetAlgebra G :=
  coordinateDifferential
    (fun j => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • evenJet j)
    (fun j => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • oddJet j) P

theorem jetEuler_smul (weights : BasicScales) (r : ℂ) (P : JetAlgebra G) :
    jetEuler weights (r • P) = r • jetEuler weights P :=
  coordinateDifferential_smul _ _ r P

theorem jetEuler_add (weights : BasicScales) (P Q : JetAlgebra G) :
    jetEuler weights (P+Q) = jetEuler weights P + jetEuler weights Q :=
  coordinateDifferential_add _ _ P Q

theorem jetEuler_one (weights : BasicScales) : jetEuler weights (1 : JetAlgebra G) = 0 := by
  have he (j : EvenJet G) : evenPartial j (1 : JetAlgebra G) = 0 := by
    simpa [leftPartialJet, j.property] using! leftPartialJet_one j.val
  have ho (j : OddJet G) : oddPartial j (1 : JetAlgebra G) = 0 := by
    simpa [leftPartialJet, j.property] using! leftPartialJet_one j.val
  simp [jetEuler, coordinateDifferential, he, ho]

theorem jetEuler_jet (weights : BasicScales) (j : Jet G) :
    jetEuler weights (jet j) = (ScaleInsertion.eulerWeight weights j.field : ℂ) • jet j := by
  by_cases hj : j.field.parity = true
  · simpa only [jetEuler, jet, hj, dif_pos] using! coordinateDifferential_oddJet
      (fun j => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • evenJet j)
      (fun j => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • oddJet j) ⟨j,hj⟩
  · simpa only [jetEuler, jet, hj, dif_neg] using! coordinateDifferential_evenJet
      (fun j => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • evenJet j)
      (fun j => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • oddJet j)
      ⟨j, by cases h : j.field.parity <;> simp_all⟩

/-- The canonical Euler operation is even, including in the odd exterior
variables. Its ordinary product rule is proved with the actual involution. -/
theorem jetEuler_mul_jet (weights : BasicScales) (P : JetAlgebra G) (j : Jet G) :
    jetEuler weights (P * jet j) = jetEuler weights P * jet j +
      (ScaleInsertion.eulerWeight weights j.field : ℂ) • (P * jet j) := by
  by_cases hj : j.field.parity = true
  · simp only [jet, hj, dif_pos, jetEuler]
    rw [coordinateDifferential_mul_oddJet]
    rw [smul_mul_assoc, oddJet_mul_parity]
  · simp only [jet, dif_neg hj, jetEuler]
    rw [coordinateDifferential_mul_evenJet]
    rw [smul_mul_assoc, evenJet_commute]

/-- Exact signed word count, proved for arbitrary ordered ghost/antifield
words rather than evaluated on commuting numerical ghost coordinates. -/
theorem jetEuler_monomial (weights : BasicScales) (source : List (LocalVertexLeg G)) :
    jetEuler weights (monomial source) =
      ((source.map (fun k => ScaleInsertion.eulerWeight weights k.field)).sum : ℂ) • monomial source := by
  induction source using List.reverseRecOn with
  | nil => simp [monomial, jetEuler_one]
  | append_singleton source k ih =>
    have he : monomial (source ++ [k]) = monomial source * jet (vertexJet k) := by
      simp [monomial, List.map_append, List.prod_append, vertexJet]
    rw [he, jetEuler_mul_jet, ih, smul_mul_assoc]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, Complex.ofReal_add, vertexJet]
    rw [add_smul]


theorem eulerAction_vertex_general (weights : BasicScales) (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    ScaleInsertion.eulerAction weights (localVertexAmplitude v g) legs q =
      ((v.legs.map (fun j => ScaleInsertion.eulerWeight weights j.field)).sum : ℂ) *
        localVertexAmplitude v g legs q := by
  by_cases hz : localVertexAmplitude v g legs q = 0
  · simp [ScaleInsertion.eulerAction, hz]
  · have hd : localMonomialDerivative v.legs (List.ofFn (fun i => (legs.get i, q i))) ≠ 0 := by
      intro h
      apply hz
      unfold localVertexAmplitude
      rw [h, mul_zero]
    have hp := YangMills.WardAction.localDerivative_support _ _ hd
    have he : (List.ofFn (fun i => (legs.get i, q i))).map Prod.fst = legs := by
      simp only [List.map_ofFn, Function.comp_def, List.ofFn_get]
    rw [he] at hp
    have hw := (hp.map (ScaleInsertion.eulerWeight weights)).sum_eq
    unfold ScaleInsertion.eulerAction
    rw [← hw, List.map_map]
    rfl

/-- The canonical jet derivation computes exactly the external field/source
Euler operation used by the CS residual, for the actual ordered density
coefficients, including every antifield/ghost sector. -/
theorem densityAmplitude_jetEuler_vertex (weights : BasicScales) (v : LocalVertex G) (g : ℝ) :
    densityAmplitude (jetEuler weights (densityOfVertex g v)) =
      ScaleInsertion.eulerAction weights (localVertexAmplitude v g) := by
  funext legs q
  rw [densityOfVertex, jetEuler_smul, jetEuler_monomial, densityAmplitude_smul,
    densityAmplitude_smul, eulerAction_vertex_general]
  change _ * (_ * densityAmplitude (monomial v.legs) legs q) = _
  rw [densityAmplitude_monomial]
  unfold localVertexAmplitude
  ring

theorem densityAmplitude_jetEuler_vertices (weights : BasicScales)
    (vertices : List (LocalVertex G)) (g : ℝ) :
    densityAmplitude (jetEuler weights (densityOfVertices g vertices)) =
      ScaleInsertion.eulerAction weights (localPolynomialAmplitude vertices g) := by
  induction vertices with
  | nil =>
    funext legs q
    simp [densityOfVertices, jetEuler, coordinateDifferential, localPolynomialAmplitude,
      ScaleInsertion.eulerAction]
  | cons v vs ih =>
    rw [densityOfVertices, List.map_cons, List.sum_cons, jetEuler_add, densityAmplitude_add,
      densityAmplitude_jetEuler_vertex]
    change ScaleInsertion.eulerAction weights (localVertexAmplitude v g) +
      densityAmplitude (jetEuler weights (densityOfVertices g vs)) = _
    rw [ih]
    funext legs q
    change _ + _ = _ * (localVertexAmplitude v g legs q + localPolynomialAmplitude vs g legs q)
    exact (mul_add _ _ _).symm


/-- Exact integration-by-parts bridge from the pointwise signed jet Euler
derivation to the canonical variational Euler density. -/
theorem localClass_jetEuler (weights : BasicScales) (P : JetAlgebra G) :
    localClass (jetEuler weights P) = localClass (leftCanonicalEulerDensity weights P) := by
  have he : (fun j : EvenJet G => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • evenJet j) =
      (fun j : EvenJet G => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • jet j.val) := by
    funext j
    simp [jet, j.property]
  have ho : (fun j : OddJet G => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • oddJet j) =
      (fun j : OddJet G => (ScaleInsertion.eulerWeight weights j.val.field : ℂ) • jet j.val) := by
    funext j
    simp [jet, j.property]
  rw [jetEuler, he, ho, coordinateDifferential_finsum_jet
    (fun j : Jet G => (ScaleInsertion.eulerWeight weights j.field : ℂ) • jet j) P]
  let C : ExternalLeg G → JetAlgebra G :=
    fun field => (ScaleInsertion.eulerWeight weights field : ℂ) • jet ⟨field,0⟩
  trans localClass (∑ᶠ j : Jet G, totalDerivatives j.derivative (C j.field) * leftPartialJet j P)
  · apply congrArg localClass
    apply finsum_congr
    intro j
    simp only [C, totalDerivatives_smul, totalDerivatives_jet, zero_add]
  rw [localClass_prolongation_euler, Fintype.sum_sum_type]
  unfold leftCanonicalEulerDensity
  change (∑ K : BasicField G, (divergences G).mkQ
      (((basicScale weights K : ℝ) : ℂ) • jet ⟨.inl K,0⟩ * leftEuler (.inl K) P)) +
    (∑ K : BasicField G, (divergences G).mkQ
      (((-basicScale weights K : ℝ) : ℂ) • jet ⟨.inr K,0⟩ * leftEuler (.inr K) P)) =
    (divergences G).mkQ (∑ K : BasicField G, (basicScale weights K : ℂ) •
      (jet ⟨.inl K,0⟩ * leftEuler (.inl K) P - jet ⟨.inr K,0⟩ * leftEuler (.inr K) P))
  simp only [Complex.ofReal_neg, smul_mul_assoc, map_sum, map_smul, map_sub, smul_sub,
    neg_smul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

/-- Every actual canonical Euler variation is in the SAME action's exact
integrated image, with explicit generator and the actual quotient. -/
theorem jetEuler_exact (S : JetAlgebra G) (weights : BasicScales) :
    localClass (jetEuler weights S) =
      localSTFunctional S (localClass (rescalingGenerator weights)) := by
  rw [localClass_jetEuler, leftCanonicalEuler_exact]

end YangMills.FullBV
