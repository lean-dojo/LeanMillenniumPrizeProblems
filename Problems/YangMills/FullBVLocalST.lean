import Problems.YangMills.FullBVBridge

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-! Pointwise ST action on actual polynomial words. No divergence quotient is
used: all jet descendants occur through the Hamiltonian characteristic. -/
noncomputable section
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Canonical Grassmann differentiation of a raw vertex word. The ordered
removal rule is fixed, including a crossing sign for every odd prefix. -/
def jetWordDerivative (j : Jet G) : List (LocalVertexLeg G) → JetAlgebra G
  | [] => 0
  | k :: source =>
      (if j = vertexJet k then monomial source else 0) +
      crossingSign j.field k • (jet (vertexJet k) * jetWordDerivative j source)

theorem leftPartialJet_monomial (j : Jet G) (source : List (LocalVertexLeg G)) :
    leftPartialJet j (monomial source) = jetWordDerivative j source := by
  classical
  induction source with
  | nil => simpa [monomial, jetWordDerivative] using leftPartialJet_one j
  | cons k source ih =>
      rw [monomial_cons, leftPartialJet_mul, leftPartialJet_jet, ih]
      by_cases hj : j.field.parity = true <;> by_cases hk : k.field.parity = true
      all_goals
        simp [jetWordDerivative, crossingSign, hj, hk, parity_jet, vertexJet,
          ite_mul]
      all_goals
        change -(jet (vertexJet k)) * jetWordDerivative j source =
          (-1 : ℂ) • (jet (vertexJet k) * jetWordDerivative j source)
        calc
          _ = -(jet (vertexJet k) * jetWordDerivative j source) :=
            neg_mul (jet (vertexJet k)) (jetWordDerivative j source)
          _ = _ := (neg_one_smul ℂ
            (jet (vertexJet k) * jetWordDerivative j source)).symm

/-- The same derivative as a finite sum over removed word positions. -/
def positionalJetDerivative (j : Jet G) (source : List (LocalVertexLeg G)) :
    JetAlgebra G :=
  ∑ i : Fin source.length,
    if j = vertexJet (source.get i) then
      prefixSign j.field source i.val •
        monomial (source.take i.val ++ source.drop (i.val + 1)) else 0

theorem jetWordDerivative_positional (j : Jet G) (source : List (LocalVertexLeg G)) :
    jetWordDerivative j source = positionalJetDerivative j source := by
  classical
  induction source with
  | nil => simp [jetWordDerivative, positionalJetDerivative]
  | cons k source ih =>
      rw [jetWordDerivative, ih]
      unfold positionalJetDerivative
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, Fin.val_zero, prefixSign_zero, one_smul,
        List.take_zero, List.nil_append]
      congr 1
      rw [Finset.mul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Fin.val_succ, prefixSign_cons_succ,
        List.take_succ_cons, List.drop_succ_cons, List.cons_append, monomial_cons]
      by_cases h : j = vertexJet source[i.val]
      · simp [h, mul_smul_comm, smul_smul]
      · simp [h]

theorem leftPartialJet_monomial_positional (j : Jet G)
    (source : List (LocalVertexLeg G)) :
    leftPartialJet j (monomial source) = positionalJetDerivative j source := by
  rw [leftPartialJet_monomial, jetWordDerivative_positional]

/-- The full pointwise characteristic, evaluated on a labelled descendant. -/
def prolongedST (S : JetAlgebra G) (j : Jet G) : JetAlgebra G :=
  totalDerivatives j.derivative (stCharacteristic S j.field)

/-- Completely fixed polynomial-word formula for local ST. The summands have
finite support by `evenSummands_finite`/`oddSummands_finite`; a derivative of a
field is retained and varied by the prolonged characteristic. -/
theorem localST_monomial (S : JetAlgebra G) (source : List (LocalVertexLeg G)) :
    localST S (monomial source) =
      (∑ᶠ j : EvenJet G, prolongedST S j.val * jetWordDerivative j.val source) +
      ∑ᶠ j : OddJet G, prolongedST S j.val * jetWordDerivative j.val source := by
  classical
  unfold localST coordinateDifferential
  congr 1
  · apply finsum_congr
    intro j
    rw [← leftPartialJet_monomial]
    simp [leftPartialJet, j.property, prolongedST]
  · apply finsum_congr
    intro j
    rw [← leftPartialJet_monomial]
    simp [leftPartialJet, j.property, prolongedST]

theorem localST_monomial_positional (S : JetAlgebra G)
    (source : List (LocalVertexLeg G)) :
    localST S (monomial source) =
      (∑ᶠ j : EvenJet G, prolongedST S j.val * positionalJetDerivative j.val source) +
      ∑ᶠ j : OddJet G, prolongedST S j.val * positionalJetDerivative j.val source := by
  simpa only [← jetWordDerivative_positional] using localST_monomial S source

/-- Variation of a fixed source vertex is extracted through the same canonical
jet density, with its actual coefficient and coupling order. -/
theorem densityAmplitude_localST_vertex (S : JetAlgebra G) (v : LocalVertex G) (g : ℝ) :
    densityAmplitude (localST S (densityOfVertex g v)) =
      (v.coefficient * (g : ℂ) ^ v.couplingOrder) •
        densityAmplitude (localST S (monomial v.legs)) := by
  rw [densityOfVertex, localST_smul, densityAmplitude_smul]

/-- Multiplicity-normalized words use the same pointwise ST operator. The
normalization is a scalar and introduces no independent variation map. -/
def normalizedWord (normalization : ℂ) (source : List (LocalVertexLeg G)) :
    JetAlgebra G := normalization • monomial source

theorem localST_normalizedWord (S : JetAlgebra G) (r : ℂ)
    (source : List (LocalVertexLeg G)) :
    localST S (normalizedWord r source) = r •
      ((∑ᶠ j : EvenJet G, prolongedST S j.val * jetWordDerivative j.val source) +
        ∑ᶠ j : OddJet G, prolongedST S j.val * jetWordDerivative j.val source) := by
  rw [normalizedWord, localST_smul, localST_monomial]

end YangMills.FullBV
