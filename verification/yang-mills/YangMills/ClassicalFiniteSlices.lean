import YangMills.ClassicalHomogeneousDescent
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace YangMills.CurvatureJetPolynomial
variable {G : CompactSimpleGaugeGroup}

instance boundedCoordinateFinite (d : ℕ) : Finite {c : CurvatureJetCoordinate G // c.1.dimension ≤ d} := by
  letI : Fintype {l : List (Fin 4) // l.length ≤ d} := (List.finite_length_le (Fin 4) d).fintype
  apply Finite.of_injective (fun c : {c : CurvatureJetCoordinate G // c.1.dimension ≤ d} =>
    (c.val.1.mu, c.val.1.nu,
      (⟨c.val.1.derivatives, by have h := c.property; unfold CurvatureJet.dimension at h; omega⟩ :
        {l : List (Fin 4) // l.length ≤ d}), c.val.2))
  intro a b equal
  apply Subtype.ext
  rcases a with ⟨⟨⟨am,an,ads⟩,ac⟩,ha⟩
  rcases b with ⟨⟨⟨bm,bn,bds⟩,bc⟩,hb⟩
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at equal
  rcases equal with ⟨hm,hn,hds,hc⟩
  subst bm; subst bn; subst bds; subst bc
  rfl

lemma monomial_term_le (m : CurvatureJetCoordinate G →₀ ℕ) (c : CurvatureJetCoordinate G) :
    m c * c.1.dimension ≤ (monomialDimension (G := G)) m := by
  classical
  by_cases zero : m c = 0
  · simp [zero]
  · exact Finset.single_le_sum (fun i _ => Nat.zero_le (m i * i.1.dimension))
      (Finsupp.mem_support_iff.mpr zero)

lemma monomial_exponent_le (m : CurvatureJetCoordinate G →₀ ℕ) (c : CurvatureJetCoordinate G) :
    m c ≤ (monomialDimension (G := G)) m := by
  have term := monomial_term_le m c
  have positive : 1 ≤ c.1.dimension := by unfold CurvatureJet.dimension; omega
  simpa only [Nat.mul_one] using (Nat.mul_le_mul_left (m c) positive).trans term

lemma monomial_coordinate_le {m : CurvatureJetCoordinate G →₀ ℕ} {c : CurvatureJetCoordinate G}
    (nonzero : m c ≠ 0) : c.1.dimension ≤ (monomialDimension (G := G)) m := by
  have term := monomial_term_le m c
  have positive : 1 ≤ m c := by omega
  simpa only [Nat.one_mul] using (Nat.mul_le_mul_right c.1.dimension positive).trans term

/-- Bounded engineering weight leaves only finitely many actual monomials,
including the constant monomial at degree zero. -/
instance boundedMonomialFinite (d : ℕ) :
    Finite {m : CurvatureJetCoordinate G →₀ ℕ // (monomialDimension (G := G)) m ≤ d} := by
  letI : Fintype {c : CurvatureJetCoordinate G // c.1.dimension ≤ d} := Fintype.ofFinite _
  let encode (m : {m : CurvatureJetCoordinate G →₀ ℕ // (monomialDimension (G := G)) m ≤ d}) :
      {c : CurvatureJetCoordinate G // c.1.dimension ≤ d} → Fin (d+1) :=
    fun c => ⟨m.val c.val, Nat.lt_succ_of_le ((monomial_exponent_le m.val c.val).trans m.property)⟩
  apply Finite.of_injective encode
  intro a b equal
  apply Subtype.ext
  apply Finsupp.ext
  intro c
  by_cases bounded : c.1.dimension ≤ d
  · exact congrArg Fin.val (congrFun equal ⟨c,bounded⟩)
  · have azero : a.val c = 0 := by
      by_contra nonzero
      exact bounded ((monomial_coordinate_le nonzero).trans a.property)
    have bzero : b.val c = 0 := by
      by_contra nonzero
      exact bounded ((monomial_coordinate_le nonzero).trans b.property)
    rw [azero,bzero]

/-- The full bounded-weight polynomial slice, before invariance or identities. -/
def boundedSlice (d : ℕ) : Submodule ℝ (CurvatureJetPolynomial G) :=
  Finsupp.supported ℝ ℝ {m | (monomialDimension (G := G)) m ≤ d}

lemma mem_boundedSlice (d : ℕ) (p : CurvatureJetPolynomial G) :
    p ∈ boundedSlice d ↔ HasDimensionAtMost d p := by
  rfl

instance boundedSlice_finiteDimensional (d : ℕ) : FiniteDimensional ℝ (boundedSlice (G := G) d) := by
  letI : Fintype {m : CurvatureJetCoordinate G →₀ ℕ // (monomialDimension (G := G)) m ≤ d} := Fintype.ofFinite _
  letI : FiniteDimensional ℝ ({m : CurvatureJetCoordinate G →₀ ℕ // (monomialDimension (G := G)) m ≤ d} →₀ ℝ) := inferInstance
  let e : boundedSlice (G := G) d ≃ₗ[ℝ]
      ({m : CurvatureJetCoordinate G →₀ ℕ // (monomialDimension (G := G)) m ≤ d} →₀ ℝ) :=
    Finsupp.supportedEquivFinsupp (R := ℝ) (M := ℝ)
      {m : CurvatureJetCoordinate G →₀ ℕ | (monomialDimension (G := G)) m ≤ d}
  exact e.symm.finiteDimensional

/-- The actual invariant bounded slice is a subspace of that finite slice. -/
def boundedInvariantSlice (d : ℕ) : Submodule ℝ (invariantAlgebra G) :=
  (boundedSlice d).comap (invariantAlgebra G).val.toLinearMap

instance boundedInvariantSlice_finiteDimensional (d : ℕ) :
    FiniteDimensional ℝ (boundedInvariantSlice (G := G) d) := by
  let inclusion : boundedInvariantSlice (G := G) d →ₗ[ℝ] boundedSlice (G := G) d :=
    { toFun := fun p => ⟨p.val.val,p.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective inclusion (by
  intro a b equal
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : boundedSlice (G := G) d => z.val) equal)

end YangMills.CurvatureJetPolynomial
