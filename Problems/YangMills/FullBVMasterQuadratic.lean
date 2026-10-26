import Problems.YangMills.FullBVLocalST

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! Same-action BV master-equation proof work. No CME or nilpotency axiom. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

theorem Jet.eq_of_coordinates {j k : Jet G} (hf : j.field = k.field)
    (hd : j.derivative = k.derivative) : j = k := by
  cases j
  cases k
  cases hf
  cases hd
  rfl

theorem totalDerivative_jet (mu : Fin 4) (j : Jet G) :
    totalDerivative mu (jet j) = jet (j.shift mu) := by
  by_cases h : j.field.parity = true
  · simpa [totalDerivative, jet, h, oddShift, Jet.shift] using
      coordinateDifferential_oddJet (fun i => evenJet (evenShift mu i))
        (fun i => oddJet (oddShift mu i)) ⟨j, h⟩
  · simpa [totalDerivative, jet, h, evenShift, Jet.shift] using
      coordinateDifferential_evenJet (fun i => evenJet (evenShift mu i))
        (fun i => oddJet (oddShift mu i))
        ⟨j, by cases hp : j.field.parity <;> simp_all⟩

theorem derivativeList_count (alpha : Multiindex) (mu : Fin 4) :
    (derivativeList alpha).count mu = alpha mu := by
  fin_cases mu <;>
    simp [derivativeList, List.finRange_succ, List.count_append, List.count_replicate]

theorem derivativeList_length (alpha : Multiindex) :
    (derivativeList alpha).length = derivativeOrder alpha := by
  simp [derivativeList, derivativeOrder, List.finRange_succ, Fin.sum_univ_succ]

theorem totalDerivatives_jet (alpha : Multiindex) (j : Jet G) :
    totalDerivatives alpha (jet j) = jet ⟨j.field, j.derivative + alpha⟩ := by
  have h (ds : List (Fin 4)) (j : Jet G) :
      ds.foldr totalDerivative (jet j) =
        jet ⟨j.field, j.derivative + fun mu => ds.count mu⟩ := by
    induction ds generalizing j with
    | nil =>
        apply congrArg jet
        apply Jet.eq_of_coordinates rfl
        funext mu
        simp
    | cons a ds ih =>
        rw [List.foldr_cons, ih, totalDerivative_jet]
        congr 1
        apply Jet.eq_of_coordinates
        · rfl
        · funext mu
          simp only [Jet.shift, Pi.add_apply, List.count_cons]
          by_cases hm : a = mu
          · subst mu; simp [Nat.add_assoc]
          · simp [hm, Ne.symm hm]
  simpa only [totalDerivatives, derivativeList_count] using h (derivativeList alpha) j

theorem totalDerivative_one (mu : Fin 4) :
    totalDerivative mu (1 : JetAlgebra G) = 0 := by
  simp [totalDerivative, coordinateDifferential, evenPartial, oddPartial,
    Algebra.TensorProduct.one_def]

theorem totalDerivatives_one (alpha : Multiindex) :
    totalDerivatives alpha (1 : JetAlgebra G) = if alpha = 0 then 1 else 0 := by
  have h (ds : List (Fin 4)) : ds.foldr totalDerivative (1 : JetAlgebra G) =
      if ds = [] then 1 else 0 := by
    induction ds with
    | nil => rfl
    | cons a ds ih =>
        simp only [List.foldr_cons, List.cons_ne_nil, if_false]
        rw [ih]
        by_cases hd : ds = [] <;> simp [hd, totalDerivative_one]
  have he : derivativeList alpha = [] ↔ alpha = 0 := by
    constructor
    · intro he
      funext mu
      have hc := derivativeList_count alpha mu
      simpa [he] using hc.symm
    · intro he
      simp [he, derivativeList]
  simpa only [totalDerivatives, he] using h (derivativeList alpha)

/-- Euler support of a quadratic word has only its two actual jet orders. -/
theorem leftEuler_quadratic (field : ExternalLeg G) (j k : Jet G) :
    leftEuler field (jet j * jet k) =
      (if j.field = field then ((-1 : ℂ) ^ derivativeOrder j.derivative) •
        totalDerivatives j.derivative (jet k) else 0) +
      (if k.field = field then ((-1 : ℂ) ^ derivativeOrder k.derivative) •
        totalDerivatives k.derivative (if k.field.parity then parity (jet j) else jet j) else 0) := by
  classical
  have hp (alpha : Multiindex) :
      leftPartialJet ⟨field, alpha⟩ (jet j * jet k) =
        (if j.field = field ∧ alpha = j.derivative then jet k else 0) +
        (if k.field = field ∧ alpha = k.derivative then
          (if k.field.parity then parity (jet j) else jet j) else 0) := by
    rw [leftPartialJet_mul, leftPartialJet_jet, leftPartialJet_jet]
    have hj : (⟨field, alpha⟩ : Jet G) = j ↔ j.field = field ∧ alpha = j.derivative := by
      cases j
      simp only [Jet.mk.injEq, eq_comm]
    have hk : (⟨field, alpha⟩ : Jet G) = k ↔ k.field = field ∧ alpha = k.derivative := by
      cases k
      simp only [Jet.mk.injEq, eq_comm]
    simp only [hj, hk]
    by_cases h : k.field = field <;> simp [h]
  unfold leftEuler
  simp only [hp, totalDerivatives_add, smul_add]
  have hf (P : JetAlgebra G) (a : Multiindex) (test : Prop) [Decidable test] :
      (Function.support (fun alpha : Multiindex => ((-1 : ℂ) ^ derivativeOrder alpha) •
        totalDerivatives alpha (if test ∧ alpha = a then P else 0))).Finite := by
    apply (Set.finite_singleton a).subset
    intro alpha ha
    by_contra hn
    have hh : alpha ≠ a := by simpa using hn
    exact ha (by simp [hh])
  rw [finsum_add_distrib (hf _ _ _) (hf _ _ _)]
  congr 1
  · rw [finsum_eq_single _ j.derivative (by intro alpha ha; simp [ha])]
    by_cases hj : j.field = field <;> simp [hj]
  · rw [finsum_eq_single _ k.derivative (by intro alpha ha; simp [ha])]
    by_cases hk : k.field = field <;> simp [hk]


theorem parity_parity (P : JetAlgebra G) : parity (parity P) = P := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ]
  | tmul p u => simp [parity, CliffordAlgebra.involute_involute]

/-- Right variation of an EVEN quadratic word is fixed by the parity of
the differentiated species; no independent right-derivative convention. -/
theorem rightPartialJet_even_quadratic (i j k : Jet G)
    (he : j.field.parity = k.field.parity) :
    rightPartialJet i (jet j * jet k) =
      (if i.field.parity then (-1 : ℂ) else 1) • leftPartialJet i (jet j * jet k) := by
  classical
  by_cases hi : i.field.parity = true
  · simp only [rightPartialJet, hi, if_true, LinearMap.comp_apply]
    rw [leftPartialJet_mul, leftPartialJet_jet, leftPartialJet_jet]
    by_cases hj : i = j <;> by_cases hk : i = k
    · subst j; subst k
      simp [parity_jet, hi]
    · subst j
      have hkp : k.field.parity = true := he.symm.trans hi
      simp [hk, parity_jet, hi, hkp]
      exact (neg_one_smul ℂ (jet k)).symm
    · subst k
      have hjp : j.field.parity = true := he.trans hi
      simp [hj, parity_jet, hi, hjp]
    · simp [hj, hk]
  · simp [rightPartialJet, hi]

theorem rightEuler_even_quadratic (field : ExternalLeg G) (j k : Jet G)
    (he : j.field.parity = k.field.parity) :
    rightEuler field (jet j * jet k) =
      (if field.parity then (-1 : ℂ) else 1) • leftEuler field (jet j * jet k) := by
  simp only [rightEuler, leftEuler, rightPartialJet_even_quadratic _ _ _ he,
    totalDerivatives_smul]
  simp only [smul_comm ((-1 : ℂ) ^ _) (if field.parity then (-1 : ℂ) else 1)]
  exact (smul_finsum' _ (leftEulerSummands_finite field (jet j * jet k))).symm


theorem sum_list_flatMap {I M : Type*} [AddMonoid M] (f : I → List M) (is : List I) :
    (is.flatMap f).sum = (is.map fun i => (f i).sum).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih]

@[simp] theorem vertexJet_nil (K : ExternalLeg G) :
    vertexJet (⟨K, []⟩ : LocalVertexLeg G) = ⟨K, 0⟩ := rfl

@[simp] theorem vertexJet_single (K : ExternalLeg G) (mu : Fin 4) :
    vertexJet (⟨K, [mu]⟩ : LocalVertexLeg G) = ⟨K, Pi.single mu 1⟩ := by
  refine Jet.eq_of_coordinates ?_ ?_
  · rfl
  · funext nu
    by_cases h : mu = nu <;> simp [vertexJet, h, eq_comm]

@[simp] theorem vertexJet_double (K : ExternalLeg G) (mu : Fin 4) :
    vertexJet (⟨K, [mu, mu]⟩ : LocalVertexLeg G) = ⟨K, Pi.single mu 2⟩ := by
  refine Jet.eq_of_coordinates ?_ ?_
  · rfl
  · funext nu
    by_cases h : mu = nu <;> simp [vertexJet, h, eq_comm]

theorem densityOfVertex_pair (c : ℂ) (j k : LocalVertexLeg G) :
    densityOfVertex 0 (⟨c, 0, [j,k]⟩ : LocalVertex G) =
      c • (jet (vertexJet j) * jet (vertexJet k)) := by
  simp [densityOfVertex, monomial, vertexJet]

/-- Closed quadratic density obtained from the actual free vertex list. -/
def freeDensityQuadratic (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension, (
    (1 / 2 : ℂ) • (jet ⟨.inl (.auxiliary a), 0⟩ * jet ⟨.inl (.auxiliary a), 0⟩) +
    (-Complex.I) • (jet ⟨.inl (.auxiliary a), 0⟩ * jet ⟨.inr (.antighost a), 0⟩) +
    ∑ mu : Fin 4, (
      jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.ghost a), Pi.single mu 1⟩ +
      (-1 : ℂ) • (jet ⟨.inl (.ghost a), Pi.single mu 1⟩ * jet ⟨.inr (.gauge mu a), 0⟩) +
      (-1 : ℂ) • (jet ⟨.inl (.gauge mu a), Pi.single mu 1⟩ * jet ⟨.inr (.antighost a), 0⟩) +
      (-Complex.I) • (jet ⟨.inl (.ghost a), Pi.single mu 2⟩ * jet ⟨.inr (.auxiliary a), 0⟩) +
      ∑ nu : Fin 4, (1 / 2 : ℂ) •
        (jet ⟨.inl (.gauge nu a), Pi.single mu 1⟩ * jet ⟨.inl (.gauge nu a), Pi.single mu 1⟩)))

theorem freeActionDensity_eq_quadratic : freeActionDensity G = freeDensityQuadratic G := by
  unfold freeActionDensity densityOfVertices freeActionVertices
  simp only [List.map_flatMap, sum_list_flatMap, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, densityOfVertex_pair, vertexJet_nil, vertexJet_single, vertexJet_double, one_smul]
  simp only [freeDensityQuadratic, add_assoc]

end YangMills.FullBV
