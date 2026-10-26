import Problems.YangMills.ClassicalFiniteSlices
import Mathlib.Algebra.DirectSum.Module

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace YangMills.CurvatureJetPolynomial
variable {G : CompactSimpleGaugeGroup}

/-- The linear evaluation map uses the same actual smooth connections. -/
def connectionEvaluation : invariantAlgebra G →ₗ[ℝ] (Connection G → Spacetime → ℝ) where
  toFun p A x := p.val.onConnection A x
  map_add' p q := by funext A x; simp [onConnection,evaluate]
  map_smul' c p := by funext A x; simp [onConnection,evaluate]

def connectionNull (G : CompactSimpleGaugeGroup) : Submodule ℝ (invariantAlgebra G) :=
  LinearMap.ker (connectionEvaluation (G := G))

/-- A vector-space presentation of precisely the same evaluation quotient. -/
def ClassicalSpace (G : CompactSimpleGaugeGroup) := invariantAlgebra G ⧸ connectionNull G
instance : AddCommGroup (ClassicalSpace G) := inferInstanceAs (AddCommGroup (_ ⧸ _))
instance : Module ℝ (ClassicalSpace G) := inferInstanceAs (Module ℝ (_ ⧸ _))

def classicalMk : invariantAlgebra G →ₗ[ℝ] ClassicalSpace G := (connectionNull G).mkQ

theorem classicalMk_eq_iff (p q : invariantAlgebra G) :
    classicalMk p = classicalMk q ↔ sameOnConnections p.val q.val := by
  rw [← sub_eq_zero, ← map_sub]
  change Submodule.Quotient.mk (p-q) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change connectionEvaluation (p-q) = 0 ↔ _
  constructor
  · intro h A x
    have := congrFun (congrFun h A) x
    simpa [connectionEvaluation,onConnection,evaluate,sub_eq_zero] using this
  · intro h
    funext A x
    simpa [connectionEvaluation,onConnection,evaluate] using sub_eq_zero.mpr (h A x)

def classicalProjection (d : ℕ) : ClassicalSpace G →ₗ[ℝ] ClassicalSpace G :=
  (connectionNull G).mapQ (connectionNull G) (invariantEngineeringProjection d) (by
    intro p hp
    change connectionEvaluation (invariantEngineeringPart d p) = 0
    have h : sameOnConnections p.val (0 : CurvatureJetPolynomial G) := by
      intro A x
      have value := congrFun (congrFun hp A) x
      simpa [connectionEvaluation,onConnection,evaluate] using value
    funext A x
    have projected := engineeringPart_respects d h A x
    simpa [connectionEvaluation,invariantEngineeringPart,engineeringPart_zero,onConnection,evaluate]
      using projected)

@[simp] theorem classicalProjection_mk (d : ℕ) (p : invariantAlgebra G) :
    classicalProjection d (classicalMk p) = classicalMk (invariantEngineeringPart d p) := rfl

theorem classicalProjection_project (d e : ℕ) (v : ClassicalSpace G) :
    classicalProjection d (classicalProjection e v) =
      if d=e then classicalProjection d v else 0 := by
  induction v using Quotient.inductionOn' with
  | h p =>
    change classicalProjection d (classicalProjection e (classicalMk p)) = _
    rw [classicalProjection_mk,classicalProjection_mk]
    split_ifs with same
    · subst e
      apply congrArg classicalMk
      apply Subtype.ext
      exact (engineeringPart_part d d p.val).trans (if_pos rfl)
    · have equal : invariantEngineeringPart d (invariantEngineeringPart e p) = 0 := by
        apply Subtype.ext
        exact (engineeringPart_part d e p.val).trans (if_neg same)
      rw [equal,map_zero]

/-- Homogeneous quotient components are the ranges of the actual projections. -/
def classicalGrade (d : ℕ) : Submodule ℝ (ClassicalSpace G) := LinearMap.range (classicalProjection (G := G) d)

theorem classicalProjection_on_grade {d e : ℕ} {v : ClassicalSpace G}
    (hv : v ∈ classicalGrade e) :
    classicalProjection d v = if d=e then v else 0 := by
  obtain ⟨w,rfl⟩ := hv
  rw [classicalProjection_project]
  split_ifs with same
  · subst e
    rfl
  · rfl

instance classicalGrade_finiteDimensional (d : ℕ) :
    FiniteDimensional ℝ (classicalGrade (G := G) d) := by
  let f : boundedInvariantSlice (G := G) d →ₗ[ℝ] ClassicalSpace G :=
    classicalMk.comp (boundedInvariantSlice (G := G) d).subtype
  letI : FiniteDimensional ℝ (LinearMap.range f) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f)
  intro v hv
  obtain ⟨w,rfl⟩ := hv
  induction w using Quotient.inductionOn' with
  | h p =>
    change classicalMk (invariantEngineeringPart d p) ∈ LinearMap.range f
    refine ⟨⟨invariantEngineeringPart d p, ?_⟩,rfl⟩
    intro m hm
    exact le_of_eq (engineeringPart_homogeneous d p.val m hm)

theorem classicalGrades_independent : iSupIndep (classicalGrade (G := G)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v belongs zero i hi
  have projected := congrArg (classicalProjection (G := G) i) zero
  simp only [map_sum,map_zero] at projected
  have collapse : (∑ j ∈ s, classicalProjection i (v j)) = v i := by
    calc
      _ = ∑ j ∈ s, if i=j then v j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact classicalProjection_on_grade (belongs j hj)
      _ = v i := by simp [hi]
  rw [collapse] at projected
  exact projected

theorem classicalGrades_span : (⨆ d, classicalGrade (G := G) d) = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  induction v using Quotient.inductionOn' with
  | h p =>
    change classicalMk p ∈ ⨆ d, classicalGrade d
    have decomposition := congrArg classicalMk (invariantEngineeringParts_sum p)
    rw [map_sum] at decomposition
    rw [← decomposition]
    apply Submodule.sum_mem
    intro d _
    apply (le_iSup (classicalGrade (G := G)) d)
    exact ⟨classicalMk p,rfl⟩

/-- The genuine invariant connection quotient is an internal direct sum of
finite-dimensional homogeneous components. -/
theorem classicalGrades_internal : DirectSum.IsInternal (classicalGrade (G := G)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    classicalGrades_independent classicalGrades_span

/-- Each component has a finite basis; their disjoint union is coherent in
every engineering truncation, independently of any quantum scheme. -/
def classicalHomogeneousBasis :
    Module.Basis (Σ d : ℕ, Fin (Module.finrank ℝ (classicalGrade (G := G) d))) ℝ
      (ClassicalSpace G) :=
  classicalGrades_internal.collectedBasis (fun d => Module.finBasis ℝ (classicalGrade d))

end YangMills.CurvatureJetPolynomial
