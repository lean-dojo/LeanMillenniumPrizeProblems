import Problems.YangMills.ClassicalGradedQuotient
import Problems.YangMills.IntrinsicFiltration

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace YangMills.CurvatureJetPolynomial
variable {G : CompactSimpleGaugeGroup}

lemma engineeringPart_of_homogeneous (d : ℕ) {p : CurvatureJetPolynomial G}
    (h : p.EngineeringHomogeneous d) : engineeringPart d p = p := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [engineeringPart_coeff]
  split_ifs with same
  · rfl
  · by_contra nonzero
    exact same (h m (MvPolynomial.mem_support_iff.mpr (Ne.symm nonzero)))

lemma grade_representative (d : ℕ) {v : ClassicalSpace G} (hv : v ∈ classicalGrade d) :
    ∃ p : invariantAlgebra G, classicalMk p = v ∧ p.val.EngineeringHomogeneous d := by
  obtain ⟨w,rfl⟩ := hv
  obtain ⟨p,rfl⟩ := (connectionNull G).mkQ_surjective w
  exact ⟨invariantEngineeringPart d p,rfl,engineeringPart_homogeneous d p.val⟩

abbrev HomogeneousIndex (G : CompactSimpleGaugeGroup) :=
  Σ d : ℕ, Fin (Module.finrank ℝ (classicalGrade (G := G) d))

theorem homogeneousBasis_mem (i : HomogeneousIndex G) :
    classicalHomogeneousBasis i ∈ classicalGrade i.1 :=
  classicalGrades_internal.collectedBasis_mem (fun d => Module.finBasis ℝ (classicalGrade d)) i

def homogeneousBasisLabel (i : HomogeneousIndex G) : invariantAlgebra G :=
  Classical.choose (grade_representative i.1 (homogeneousBasis_mem i))

theorem homogeneousBasisLabel_mk (i : HomogeneousIndex G) :
    classicalMk (homogeneousBasisLabel i) = classicalHomogeneousBasis i :=
  (Classical.choose_spec (grade_representative i.1 (homogeneousBasis_mem i))).1

theorem homogeneousBasisLabel_homogeneous (i : HomogeneousIndex G) :
    (homogeneousBasisLabel i).val.EngineeringHomogeneous i.1 :=
  (Classical.choose_spec (grade_representative i.1 (homogeneousBasis_mem i))).2

theorem homogeneousBasisLabel_dimension (i : HomogeneousIndex G) :
    intrinsicEngineeringDimension (homogeneousBasisLabel i) = i.1 := by
  have bounded : HasDimensionAtMost i.1 (homogeneousBasisLabel i).val :=
    fun m hm => le_of_eq (homogeneousBasisLabel_homogeneous i m hm)
  have upper := intrinsicEngineeringDimension_le_of_representative
    (homogeneousBasisLabel i) (homogeneousBasisLabel i) i.1 (fun _ _ => rfl) bounded
  apply le_antisymm upper
  by_contra lower
  have strict : intrinsicEngineeringDimension (homogeneousBasisLabel i) < i.1 := by omega
  obtain ⟨q,same,qbound⟩ := intrinsicEngineeringDimension_representative
    (homogeneousBasisLabel i) (intrinsicEngineeringDimension (homogeneousBasisLabel i)) (le_refl _)
  have equal := engineeringPart_respects i.1 same
  have qzero := engineeringPart_eq_zero_of_bound i.1 _ strict qbound
  have labelequal := engineeringPart_of_homogeneous i.1 (homogeneousBasisLabel_homogeneous i)
  have actualzero : sameOnConnections (homogeneousBasisLabel i).val 0 := by
    intro A x
    have value := equal A x
    rw [qzero,labelequal] at value
    exact value.symm
  have quotientzero : classicalMk (homogeneousBasisLabel i) = 0 := by
    simpa only [map_zero] using (classicalMk_eq_iff (homogeneousBasisLabel i) 0).mpr actualzero
  rw [homogeneousBasisLabel_mk] at quotientzero
  exact classicalHomogeneousBasis.ne_zero i quotientzero

lemma homogeneousCoordinate_projection (i : HomogeneousIndex G) (v : ClassicalSpace G) :
    classicalHomogeneousBasis.repr (classicalProjection i.1 v) i =
      classicalHomogeneousBasis.repr v i := by
  have maps : (classicalHomogeneousBasis.coord i).comp (classicalProjection i.1) =
      classicalHomogeneousBasis.coord i := by
    apply classicalHomogeneousBasis.ext
    intro j
    change classicalHomogeneousBasis.repr (classicalProjection i.1 (classicalHomogeneousBasis j)) i = _
    rw [classicalProjection_on_grade (homogeneousBasis_mem j)]
    by_cases same : i.1=j.1
    · simp only [same,ite_true]
      rfl
    · have different : i ≠ j := fun equal => same (congrArg Sigma.fst equal)
      simp [same,Module.Basis.coord_apply,Module.Basis.repr_self,different]
  exact congrArg (fun f : ClassicalSpace G →ₗ[ℝ] ℝ => f v) maps

lemma homogeneousCoordinates_bound (p : invariantAlgebra G) (i : HomogeneousIndex G)
    (nonzero : classicalHomogeneousBasis.repr (classicalMk p) i ≠ 0) :
    i.1 ≤ intrinsicEngineeringDimension p := by
  by_contra above
  have strict : intrinsicEngineeringDimension p < i.1 := by omega
  obtain ⟨q,same,qbound⟩ := intrinsicEngineeringDimension_representative p
    (intrinsicEngineeringDimension p) (le_refl _)
  have quotientEqual : classicalMk q = classicalMk p := (classicalMk_eq_iff q p).mpr same
  have projectedzero : classicalProjection i.1 (classicalMk p) = 0 := by
    rw [← quotientEqual,classicalProjection_mk]
    have qzero := engineeringPart_eq_zero_of_bound i.1 _ strict qbound
    have labelzero : invariantEngineeringPart i.1 q = 0 := Subtype.ext qzero
    rw [labelzero,map_zero]
  have coordinate := homogeneousCoordinate_projection i (classicalMk p)
  rw [projectedzero,map_zero,Finsupp.zero_apply] at coordinate
  exact nonzero coordinate.symm

/-- Reconstruct labels by the actual finite classical coefficients. -/
def homogeneousCombination (a : HomogeneousIndex G →₀ ℝ) : invariantAlgebra G :=
  a.sum (fun i c => c • homogeneousBasisLabel i)

lemma homogeneousCombination_mk (a : HomogeneousIndex G →₀ ℝ) :
    classicalMk (homogeneousCombination a) =
      Finsupp.linearCombination ℝ classicalHomogeneousBasis a := by
  classical
  unfold homogeneousCombination
  rw [Finsupp.sum,map_sum,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,homogeneousBasisLabel_mk]

lemma homogeneousCombination_evaluate (a : HomogeneousIndex G →₀ ℝ)
    (A : Connection G) (x : Spacetime) :
    (homogeneousCombination a).val.onConnection A x =
      a.sum (fun i c => c * (homogeneousBasisLabel i).val.onConnection A x) := by
  classical
  change connectionEvaluation (homogeneousCombination a) A x = _
  unfold homogeneousCombination
  rw [Finsupp.sum,map_sum]
  simp only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul,connectionEvaluation]
  rfl

/-- A coherent finite filtered basis of the actual invariant observable
quotient exists. Its representatives are genuine engineering homogeneous
polynomials; no analogous quantum normalization is asserted here. -/
def availableFilteredBasis : OPE.FilteredBasis G where
  Index := HomogeneousIndex G
  decidable := Classical.decEq _
  label := homogeneousBasisLabel
  active D := (Finset.range D).sigma (fun d => Finset.univ)
  active_iff i D := by
    simp only [Finset.mem_sigma,Finset.mem_range,Finset.mem_univ,and_true]
    exact (homogeneousBasisLabel_dimension i).symm ▸ Iff.rfl
  independent a h := by
    have actualzero : sameOnConnections (homogeneousCombination a).val 0 := by
      intro A x
      rw [homogeneousCombination_evaluate,h A x]
      simp [onConnection,evaluate]
    have quotientzero : classicalMk (homogeneousCombination a) = 0 := by
      simpa only [map_zero] using (classicalMk_eq_iff (homogeneousCombination a) 0).mpr actualzero
    rw [homogeneousCombination_mk] at quotientzero
    have coefficients := congrArg classicalHomogeneousBasis.repr quotientzero
    simpa only [Module.Basis.repr_linearCombination,map_zero] using coefficients
  spans p := by
    let a := classicalHomogeneousBasis.repr (classicalMk p)
    refine ⟨a,?_,?_⟩
    · intro i hi
      change intrinsicEngineeringDimension (homogeneousBasisLabel i) ≤ intrinsicEngineeringDimension p
      rw [homogeneousBasisLabel_dimension]
      exact homogeneousCoordinates_bound p i (Finsupp.mem_support_iff.mp hi)
    · have equal : classicalMk (homogeneousCombination a) = classicalMk p := by
        rw [homogeneousCombination_mk]
        exact classicalHomogeneousBasis.linearCombination_repr (classicalMk p)
      have same := (classicalMk_eq_iff (homogeneousCombination a) p).mp equal
      intro A x
      rw [← same A x,homogeneousCombination_evaluate]

 theorem availableFilteredBasis_homogeneous (i : (availableFilteredBasis (G := G)).Index) :
    ((availableFilteredBasis (G := G)).label i).val.EngineeringHomogeneous
      (OPE.dimension ((availableFilteredBasis (G := G)).label i)) := by
  change (homogeneousBasisLabel i).val.EngineeringHomogeneous
    (intrinsicEngineeringDimension (homogeneousBasisLabel i))
  rw [homogeneousBasisLabel_dimension]
  exact homogeneousBasisLabel_homogeneous i

end YangMills.CurvatureJetPolynomial
