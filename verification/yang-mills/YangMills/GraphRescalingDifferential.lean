import YangMills.GraphRescaling
import YangMills.FullBVActionParity
noncomputable section
set_option maxHeartbeats 600000
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

theorem graphRescale_parity (t : ℂ) (P : JetAlgebra G) :
    graphRescale t (parity P) = parity (graphRescale t P) := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp [parity_one]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | smul c P hP => simp only [map_smul, hP]
  | mul P j hP =>
    simp only [parity_mul, map_mul, hP, graphRescale_jet, map_smul, parity_jet]
    by_cases h : j.field.parity = true <;> simp [h]

theorem graphRescale_totalDerivative (t : ℂ) (mu : Fin 4) (P : JetAlgebra G) :
    graphRescale t (totalDerivative mu P) = totalDerivative mu (graphRescale t P) := by
  induction P using polynomial_induction_jet with
  | zero => simp [totalDerivative_zero]
  | one => simp [totalDerivative_one]
  | add P Q hP hQ => simp only [totalDerivative_add, map_add, hP, hQ]
  | smul c P hP => simp only [totalDerivative_smul, map_smul, hP]
  | mul P j hP =>
    simp only [totalDerivative_mul, map_add, map_mul, hP, graphRescale_jet,
      totalDerivative_jet, totalDerivative_smul, mul_smul_comm, smul_add]

theorem graphRescale_totalDerivatives (t : ℂ) (alpha : Multiindex) (P : JetAlgebra G) :
    graphRescale t (totalDerivatives alpha P) = totalDerivatives alpha (graphRescale t P) := by
  unfold totalDerivatives
  generalize derivativeList alpha = l
  induction l with
  | nil => rfl
  | cons mu l ih => simp only [List.foldr_cons, graphRescale_totalDerivative, ih]

/-- The actual coupling/field graph map has its literal canonical
Jacobian factor on every left odd/even jet derivative. -/
theorem leftPartialJet_graphRescale (t : ℂ) (j : Jet G) (P : JetAlgebra G) :
    leftPartialJet j (graphRescale t P) = t • graphRescale t (leftPartialJet j P) := by
  induction P using polynomial_induction_jet with
  | zero => simp
  | one => simp [leftPartialJet_one]
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add]
  | smul c P hP =>
    simp only [map_smul, hP, smul_smul]
    congr 1
    ring
  | mul P k hP =>
    simp only [map_mul, graphRescale_jet, leftPartialJet_mul, map_add, map_smul,
      leftPartialJet_jet, hP, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    by_cases he : j = k
    · subst k
      by_cases hj : j.field.parity = true <;> simp [hj, graphRescale_parity]
    · simp [he]

theorem rightPartialJet_graphRescale (t : ℂ) (j : Jet G) (P : JetAlgebra G) :
    rightPartialJet j (graphRescale t P) = t • graphRescale t (rightPartialJet j P) := by
  by_cases hj : j.field.parity = true
  · simp only [rightPartialJet, hj, if_true, LinearMap.comp_apply,
      leftPartialJet_graphRescale, map_smul, graphRescale_parity]
  · simp only [rightPartialJet, hj, Bool.false_eq_true, if_false, leftPartialJet_graphRescale]

theorem rightEuler_graphRescale (t : ℂ) (field : ExternalLeg G) (P : JetAlgebra G) :
    rightEuler field (graphRescale t P) = t • graphRescale t (rightEuler field P) := by
  let L : JetAlgebra G →ₗ[ℂ] JetAlgebra G := t • (graphRescale t).toLinearMap
  have hm := L.toAddMonoidHom.map_finsum (rightEulerSummands_finite field P)
  change t • graphRescale t (rightEuler field P) =
    ∑ᶠ alpha : Multiindex, t • graphRescale t
      (((-1 : ℂ)^derivativeOrder alpha) • totalDerivatives alpha
        (rightPartialJet ⟨field, alpha⟩ P)) at hm
  rw [hm]
  unfold rightEuler
  apply finsum_congr
  intro alpha
  simp only [rightPartialJet_graphRescale, totalDerivatives_smul, map_smul,
    graphRescale_totalDerivatives, smul_smul]
  congr 1
  ring

/-- The graph map intertwines the SAME actual master characteristic. The
nonzero coupling permits cancellation, but the map itself contains no
negative powers and remains defined at zero. -/
theorem graphRescale_masterCharacteristic {B : InvariantForm G} (frame : ColorFrame B)
    (g : ℝ) (hg : g ≠ 0) (field : ExternalLeg G) :
    graphRescale (g : ℂ) (stCharacteristic (masterActionDensity frame 1) field) =
      (g : ℂ) • stCharacteristic (masterActionDensity frame g) field := by
  have he (k : ExternalLeg G) :
      graphRescale (g : ℂ) (rightEuler k (masterActionDensity frame 1)) =
        (g : ℂ) • rightEuler k (masterActionDensity frame g) := by
    have h := congrArg (rightEuler k) (graphRescale_masterDensity frame g)
    rw [rightEuler_graphRescale, rightEuler_smul, pow_two, mul_smul] at h
    exact (smul_right_injective (JetAlgebra G) (Complex.ofReal_ne_zero.mpr hg)) h
  cases field <;> simp only [stCharacteristic, map_neg, he, smul_neg]

/-- Exact pointwise transport of the action-derived ST operation, including
all ghost and antifield descendants. -/
theorem graphRescale_masterLocalST {B : InvariantForm G} (frame : ColorFrame B)
    (g : ℝ) (hg : g ≠ 0) (P : JetAlgebra G) :
    localST (masterActionDensity frame g) (graphRescale (g : ℂ) P) =
      graphRescale (g : ℂ) (localST (masterActionDensity frame 1) P) := by
  have hp (j : Jet G) : graphRescale (g : ℂ)
      (prolongedST (masterActionDensity frame 1) j) =
      (g : ℂ) • prolongedST (masterActionDensity frame g) j := by
    simp only [prolongedST, graphRescale_totalDerivatives,
      graphRescale_masterCharacteristic frame g hg, totalDerivatives_smul]
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

/-- At any positive-loop order, transporting a fixed-coupling Ward primitive
uses only a nonnegative scalar power, rather than a Laurent ansatz. -/
def graphPrimitive (loop : ℕ) (g : ℝ) (P : JetAlgebra G) : JetAlgebra G :=
  (g : ℂ)^(2*loop-2) • graphRescale (g : ℂ) P

theorem masterLocalST_graphPrimitive {B : InvariantForm G} (frame : ColorFrame B)
    (loop : ℕ) (g : ℝ) (hg : g ≠ 0) (P : JetAlgebra G) :
    localST (masterActionDensity frame g) (graphPrimitive loop g P) =
      graphPrimitive loop g (localST (masterActionDensity frame 1) P) := by
  simp only [graphPrimitive, localST_smul, graphRescale_masterLocalST frame g hg]

theorem graphPrimitive_monomial (loop : ℕ) (g : ℝ) (source : List (LocalVertexLeg G)) :
    graphPrimitive loop g (monomial source) =
      (g : ℂ)^(source.length + (2*loop-2)) • monomial source := by
  simp only [graphPrimitive, graphRescale_monomial, smul_smul, pow_add]
  congr 1
  ring

theorem graphPrimitive_word_graph_count (loop : ℕ) (hl : 1 ≤ loop)
    (source : List (LocalVertexLeg G)) :
    (source.length + (2*loop-2)) + 2 = source.length + 2*loop := by
  omega

/-- The graph map also acts on the actual quotient by divergences. This
is proved from commutation with total derivatives, rather than postulated
as a cohomological interpretation. -/
theorem graphRescale_preserves_divergences (t : ℂ) :
    divergences G ≤ Submodule.comap (graphRescale t).toLinearMap (divergences G) := by
  apply Submodule.span_le.mpr
  intro P hP
  obtain ⟨⟨mu,Q⟩,rfl⟩ := hP
  change graphRescale t (totalDerivative mu Q) ∈ divergences G
  rw [graphRescale_totalDerivative]
  exact Submodule.subset_span ⟨(mu,graphRescale t Q),rfl⟩

def graphRescaleFunctional (t : ℂ) : LocalFunctional G →ₗ[ℂ] LocalFunctional G :=
  (divergences G).mapQ (divergences G) (graphRescale t).toLinearMap
    (graphRescale_preserves_divergences t)

@[simp] theorem graphRescaleFunctional_localClass (t : ℂ) (P : JetAlgebra G) :
    graphRescaleFunctional t (localClass P) = localClass (graphRescale t P) := rfl

/-- Transport of an already established integrated primitive. It neither
asserts that every cocycle is exact nor quotients pointwise observables
by divergences. -/
theorem graphPrimitive_integrated_exact {B : InvariantForm G} (frame : ColorFrame B)
    (loop : ℕ) (g : ℝ) (hg : g ≠ 0) (A P : JetAlgebra G)
    (h : localClass A = localSTFunctional (masterActionDensity frame 1) (localClass P)) :
    localClass (graphPrimitive loop g A) =
      localSTFunctional (masterActionDensity frame g) (localClass (graphPrimitive loop g P)) := by
  have ht := congrArg (graphRescaleFunctional (g : ℂ)) h
  simp only [localSTFunctional_localClass, graphRescaleFunctional_localClass] at ht
  rw [← graphRescale_masterLocalST frame g hg P] at ht
  have hs := congrArg (fun x : LocalFunctional G => (g : ℂ)^(2*loop-2) • x) ht
  simpa only [graphPrimitive, localClass, map_smul, localSTFunctional_localClass,
    localST_smul] using hs

end YangMills.FullBV
