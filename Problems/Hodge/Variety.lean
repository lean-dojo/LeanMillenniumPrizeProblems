import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Defs

namespace VarietyDefinition

open AlgebraicGeometry Scheme Complex
open scoped BigOperators

universe u v u₁ u₂ u₃

/-!
## Hodge-theoretic definitions

The definitions below isolate the geometric input, cohomology groups, Hodge summands, and
cycle-class maps needed for the Hodge conjecture.

The Clay PDF uses Hodge theory of smooth projective complex varieties.  This file represents that
theory by an explicit interface: rational and complex cohomology, Hodge summands, filtration,
algebraic cycles, closed analytic subspaces, Chow comparison, and cycle classes.
-/

/--
Projective coordinates for the complex points of a variety.

Projectivity is represented by an explicit homogeneous-coordinate embedding witness: every point
receives nonzero homogeneous coordinates in some finite projective space.
-/
structure ProjectiveEmbedding (points : Type*) where
  /-- The ambient projective space is `ℙ^ambient_dimension(ℂ)`. -/
  ambient_dimension : ℕ
  /-- Homogeneous coordinates of a point in `ℂ^(N+1)`. -/
  homogeneous_coord : points → Fin (ambient_dimension + 1) → ℂ
  /-- Homogeneous coordinates are not all zero. -/
  nonzero : ∀ x : points, ∃ i : Fin (ambient_dimension + 1), homogeneous_coord x i ≠ 0

/--
Analytic/geometric realization of a nonsingular complex algebraic variety.

The Clay PDF uses the complex analytic manifold attached to a projective nonsingular algebraic
variety.  This bundle records the data the Hodge statement uses: complex points, their topology,
complex dimension, and a projective embedding.
-/
structure SmoothProjectiveRealization (X : Scheme) where
  /-- Complex points of the variety. -/
  points : Type*
  /-- Topology on the complex points. -/
  topology : TopologicalSpace points
  /-- Complex dimension of the nonsingular variety. -/
  complex_dimension : ℕ
  /-- A finite projective embedding of the complex points. -/
  projective_embedding : ProjectiveEmbedding points
  /-- Projective complex varieties are compact in the analytic topology. -/
  compact : CompactSpace points

namespace SmoothProjectiveRealization

/-- The complex points as a `TopCat` object for singular homology constructions. -/
noncomputable def top_cat {X : Scheme} (R : SmoothProjectiveRealization X) : TopCat :=
  letI : TopologicalSpace R.points := R.topology
  TopCat.of R.points

end SmoothProjectiveRealization

/--
A smooth projective variety over a field, specialized in this repository to `K = ℂ`.

The field `realization` supplies the compact complex analytic/projective model used by the Hodge
statement.
-/
structure SmoothProjectiveVariety (K : Type*) [Field K] where
  /-- The underlying scheme. -/
  X : Scheme
  /-- The structure morphism making `X` an algebraic variety over `K`. -/
  structure_map : X ⟶ Spec (.of K)
  /-- Non-singularity over `K`, using Mathlib's smooth morphism predicate. -/
  smooth : Smooth structure_map
  /-- The complex analytic/projective realization used by the Hodge statement. -/
  realization : SmoothProjectiveRealization X

attribute [instance] SmoothProjectiveVariety.smooth

/--
The cohomology, Hodge decomposition, and cycle-class structures used for a fixed variety `X`.

This interface records the objects mentioned by the Clay formulation: rational cohomology, complex
cohomology, Hodge summands, the Hodge filtration, algebraic cycles, closed analytic subspaces,
Chow's comparison, and the cycle-class map.
-/
structure HodgeData (X : SmoothProjectiveVariety ℂ) where
  /-- Rational cohomology groups `H^n(X, ℚ)` (as `ℚ`-vector spaces). -/
  cohomology_q : ℕ → Type u₁
  [cohomology_q_add : ∀ n, AddCommGroup (cohomology_q n)]
  [cohomology_q_module : ∀ n, Module ℚ (cohomology_q n)]

  /-- Complex cohomology groups `H^n(X, ℂ)` (as `ℂ`-vector spaces). -/
  cohomology_c : ℕ → Type u₂
  [cohomology_c_add : ∀ n, AddCommGroup (cohomology_c n)]
  [cohomology_c_module_c : ∀ n, Module ℂ (cohomology_c n)]
  /-- We also view complex cohomology as a `ℚ`-module (restriction of scalars). -/
  [cohomology_c_module_q : ∀ n, Module ℚ (cohomology_c n)]
  /-- Compatibility of the `ℚ`- and `ℂ`-actions on `H^n(X, ℂ)`. -/
  [cohomology_c_is_scalar_tower : ∀ n, IsScalarTower ℚ ℂ (cohomology_c n)]

  /-- Extension of scalars `H^n(X, ℚ) → H^n(X, ℂ)` (as a `ℚ`-linear map). -/
  extension_of_scalars_qc : ∀ n : ℕ, cohomology_q n →ₗ[ℚ] cohomology_c n

  /-- The Hodge summand `H^{p,q}(X) ⊂ H^n(X, ℂ)` (Clay PDF, equation (1)). -/
  hodge_subspace : ∀ n _p _q : ℕ, Submodule ℂ (cohomology_c n)

  /-- Algebraic cycles of codimension `p`. -/
  algebraic_cycle : ℕ → Type u₃
  /-- Closed analytic subspaces of codimension `p`, as in the Chow-theorem wording. -/
  closed_analytic_subspace : ℕ → Type u₃
  /-- Recorded codimension of an algebraic-cycle representative. -/
  algebraic_cycle_codimension : ∀ p : ℕ, algebraic_cycle p → ℕ
  /-- Algebraic cycles indexed by `p` really have codimension `p`. -/
  algebraic_cycle_codimension_eq :
    ∀ p : ℕ, ∀ Z : algebraic_cycle p, algebraic_cycle_codimension p Z = p
  /-- Recorded codimension of a closed analytic subspace. -/
  closed_analytic_subspace_codimension : ∀ p : ℕ, closed_analytic_subspace p → ℕ
  /-- Closed analytic subspaces indexed by `p` really have codimension `p`. -/
  closed_analytic_subspace_codimension_eq :
    ∀ p : ℕ, ∀ A : closed_analytic_subspace p, closed_analytic_subspace_codimension p A = p
  /--
  Chow's theorem for projective varieties, as data: closed analytic subspaces of codimension `p`
  and algebraic cycles of codimension `p` are equivalent.
  -/
  chow_equiv : ∀ p : ℕ, closed_analytic_subspace p ≃ algebraic_cycle p
  /-- Cycle class map `Z^p(X) → H^{2p}(X, ℚ)` (a rational version of `cl(Z)`). -/
  cycle_class : ∀ p : ℕ, algebraic_cycle p → cohomology_q (2 * p)

  /--
  Cycle classes are of type `(p,p)` after complexification (Clay PDF, Section 1):
  `cl(Z)` maps into `H^{p,p}(X) ⊂ H^{2p}(X, ℂ)`.

  This is the standard Hodge-theoretic fact for the cycle-class map.
  -/
  cycle_class_is_pp :
    ∀ p : ℕ, ∀ Z : algebraic_cycle p,
      extension_of_scalars_qc (2 * p) (cycle_class p Z) ∈ hodge_subspace (2 * p) p p

namespace HodgeData

variable {X : SmoothProjectiveVariety ℂ}

/-- The additive group structure on `H^n(X,ℚ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : AddCommGroup (data.cohomology_q n) :=
  data.cohomology_q_add n

/-- The `ℚ`-module structure on `H^n(X,ℚ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : Module ℚ (data.cohomology_q n) :=
  data.cohomology_q_module n

/-- The additive group structure on `H^n(X,ℂ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : AddCommGroup (data.cohomology_c n) :=
  data.cohomology_c_add n

/-- The `ℂ`-module structure on `H^n(X,ℂ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : Module ℂ (data.cohomology_c n) :=
  data.cohomology_c_module_c n

/-- The `ℚ`-module structure on `H^n(X,ℂ)`, by restriction of scalars (from the `HodgeData` fields). -/
instance (data : HodgeData X) (n : ℕ) : Module ℚ (data.cohomology_c n) :=
  data.cohomology_c_module_q n

/-- Compatibility of the `ℚ`- and `ℂ`-actions on `H^n(X,ℂ)` (from the `HodgeData` fields). -/
instance (data : HodgeData X) (n : ℕ) : IsScalarTower ℚ ℂ (data.cohomology_c n) :=
  data.cohomology_c_is_scalar_tower n

/--
The Hodge filtration `F^p H^n(X, ℂ) := ⊕_{a ≥ p} H^{a,n-a}` from the Clay PDF (Section 1).

We build it from the chosen Hodge summands `H^{a,n-a}` provided by `hodge_subspace`.
-/
def hodge_filtration (data : HodgeData X) (n p : ℕ) : Submodule ℂ (data.cohomology_c n) :=
  ⨆ a : ℕ, ⨆ (_ha : p ≤ a), ⨆ (_han : a ≤ n), data.hodge_subspace n a (n - a)

/--
Each Hodge summand `H^{a,n-a}` with `a ≥ p` is contained in the Hodge filtration `F^p`.

This is immediate from the definition of `hodge_filtration` as a supremum.
-/
theorem hodge_subspace_le_hodge_filtration (data : HodgeData X) (n p a : ℕ) (ha : p ≤ a) (han : a ≤ n) :
    data.hodge_subspace n a (n - a) ≤ data.hodge_filtration n p := by
  dsimp [HodgeData.hodge_filtration]
  refine le_trans ?_ (le_iSup (fun a' : ℕ => ⨆ (_ha : p ≤ a'), ⨆ (_han : a' ≤ n),
    data.hodge_subspace n a' (n - a')) a)
  refine le_trans ?_ (le_iSup (fun _ha : p ≤ a => ⨆ (_han : a ≤ n),
    data.hodge_subspace n a (n - a)) ha)
  exact le_iSup (fun _han : a ≤ n => data.hodge_subspace n a (n - a)) han

/--
The `ℚ`-subspace of Hodge classes in degree `2p` (Clay PDF, Section 1):
rational classes whose complexification lies in `H^{p,p}(X)`.
-/
noncomputable def hodge_class (data : HodgeData X) (p : ℕ) : Submodule ℚ (data.cohomology_q (2 * p)) :=
  Submodule.comap (data.extension_of_scalars_qc (2 * p))
    ((data.hodge_subspace (2 * p) p p).restrictScalars ℚ)

/--
Algebraic cycles of codimension `p` with rational coefficients.

This is the formal finite-support version of the Clay phrase “linear combination with rational
coefficients”: an element records finitely many integral/formal cycles and their `ℚ`-coefficients.
-/
@[reducible] def rational_algebraic_cycle (data : HodgeData X) (p : ℕ) :=
  data.algebraic_cycle p →₀ ℚ

/--
Closed analytic subspaces of codimension `p` with rational coefficients.

This is the finite-support version of the Clay wording before applying Chow's theorem.
-/
@[reducible] def rational_closed_analytic_subspace (data : HodgeData X) (p : ℕ) :=
  data.closed_analytic_subspace p →₀ ℚ

/-- Algebraic cycles in the `p`-indexed family have recorded codimension `p`. -/
theorem algebraic_cycle_codimension_eq_index
    (data : HodgeData X) (p : ℕ) (Z : data.algebraic_cycle p) :
    data.algebraic_cycle_codimension p Z = p :=
  data.algebraic_cycle_codimension_eq p Z

/-- Closed analytic subspaces in the `p`-indexed family have recorded codimension `p`. -/
theorem closed_analytic_subspace_codimension_eq_index
    (data : HodgeData X) (p : ℕ) (A : data.closed_analytic_subspace p) :
    data.closed_analytic_subspace_codimension p A = p :=
  data.closed_analytic_subspace_codimension_eq p A

/-- The Chow equivalence preserves the recorded codimension. -/
theorem chow_equiv_preserves_codimension
    (data : HodgeData X) (p : ℕ) (A : data.closed_analytic_subspace p) :
    data.algebraic_cycle_codimension p ((data.chow_equiv p) A) =
      data.closed_analytic_subspace_codimension p A := by
  rw [data.algebraic_cycle_codimension_eq_index p ((data.chow_equiv p) A),
    data.closed_analytic_subspace_codimension_eq_index p A]

/--
Formal rational linear combinations of codimension-`p` cycle classes.

An input `coefficients : data.algebraic_cycle p →₀ ℚ` has finite support and is sent to the corresponding
finite `ℚ`-linear combination of the classes `cl(Z)`.
-/
noncomputable def cycle_class_combination
    (data : HodgeData X) (p : ℕ) :
    (data.algebraic_cycle p →₀ ℚ) →ₗ[ℚ] data.cohomology_q (2 * p) :=
  Finsupp.linearCombination ℚ (data.cycle_class p)

/--
Cycle class of a closed analytic subspace, using Chow's theorem to regard it as an algebraic cycle.
-/
noncomputable def closed_analytic_cycle_class
    (data : HodgeData X) (p : ℕ) :
    data.closed_analytic_subspace p → data.cohomology_q (2 * p) :=
  fun A => data.cycle_class p ((data.chow_equiv p) A)

/--
Formal rational linear combinations of cycle classes of closed analytic subspaces.
-/
noncomputable def analytic_cycle_class_combination
    (data : HodgeData X) (p : ℕ) :
    data.rational_closed_analytic_subspace p →ₗ[ℚ] data.cohomology_q (2 * p) :=
  Finsupp.linearCombination ℚ (data.closed_analytic_cycle_class p)

/--
The cycle-class map on algebraic cycles with rational coefficients,
`Z^p(X)_ℚ → H^{2p}(X,ℚ)`.
-/
noncomputable def rational_cycle_class
    (data : HodgeData X) (p : ℕ) :
    data.rational_algebraic_cycle p →ₗ[ℚ] data.cohomology_q (2 * p) :=
  data.cycle_class_combination p

/-- The `ℚ`-subspace of cohomology generated by cycle classes. -/
def algebraic_cohomology (data : HodgeData X) (p : ℕ) : Submodule ℚ (data.cohomology_q (2 * p)) :=
  Submodule.span ℚ (Set.range (data.cycle_class p))

/--
The algebraic cohomology subspace is exactly the range of rational finite linear combinations of
cycle classes.
-/
theorem algebraic_eq_range_cycle_span
    (data : HodgeData X) (p : ℕ) :
    data.algebraic_cohomology p = LinearMap.range (data.cycle_class_combination p) := by
  dsimp [HodgeData.algebraic_cohomology, HodgeData.cycle_class_combination]
  rw [Finsupp.range_linearCombination]

/--
The algebraic cohomology subspace is the image of the rational cycle-class map
`Z^p(X)_ℚ → H^{2p}(X,ℚ)`.
-/
theorem algebraic_eq_range_rational_cycle
    (data : HodgeData X) (p : ℕ) :
    data.algebraic_cohomology p = LinearMap.range (data.rational_cycle_class p) := by
  exact data.algebraic_eq_range_cycle_span p

/--
By Chow's theorem, the algebraic cohomology subspace is also the range of finite rational
linear combinations of closed analytic subspace classes.
-/
theorem algebraic_eq_range_analytic_cycle
    (data : HodgeData X) (p : ℕ) :
    data.algebraic_cohomology p =
      LinearMap.range (data.analytic_cycle_class_combination p) := by
  have hRange :
      Set.range (data.cycle_class p) = Set.range (data.closed_analytic_cycle_class p) := by
    ext x
    constructor
    · rintro ⟨Z, rfl⟩
      refine ⟨(data.chow_equiv p).symm Z, ?_⟩
      simp [HodgeData.closed_analytic_cycle_class]
    · rintro ⟨A, rfl⟩
      exact ⟨(data.chow_equiv p) A, rfl⟩
  dsimp [HodgeData.algebraic_cohomology, HodgeData.analytic_cycle_class_combination]
  rw [Finsupp.range_linearCombination]
  rw [hRange]

/-- Membership in algebraic cohomology means being a rational linear combination of cycle classes. -/
theorem mem_algebraic_cohomology_iff_cycle_span
    (data : HodgeData X) (p : ℕ) (x : data.cohomology_q (2 * p)) :
    x ∈ data.algebraic_cohomology p ↔
      ∃ coefficients : data.algebraic_cycle p →₀ ℚ,
        data.cycle_class_combination p coefficients = x := by
  rw [data.algebraic_eq_range_cycle_span p]
  exact LinearMap.mem_range

/--
Membership in algebraic cohomology means being in the image of the rational cycle-class map.
-/
theorem mem_algebraic_cohomology_iff_rational_cycle_class
    (data : HodgeData X) (p : ℕ) (x : data.cohomology_q (2 * p)) :
    x ∈ data.algebraic_cohomology p ↔
      ∃ Z : data.rational_algebraic_cycle p,
        data.rational_cycle_class p Z = x := by
  rw [data.algebraic_eq_range_rational_cycle p]
  exact LinearMap.mem_range

/--
Membership in algebraic cohomology also means being a rational linear combination of classes of
closed analytic subspaces, via Chow's theorem.
-/
theorem mem_algebraic_cohomology_iff_analytic_cycle_class
    (data : HodgeData X) (p : ℕ) (x : data.cohomology_q (2 * p)) :
    x ∈ data.algebraic_cohomology p ↔
      ∃ coefficients : data.rational_closed_analytic_subspace p,
        data.analytic_cycle_class_combination p coefficients = x := by
  rw [data.algebraic_eq_range_analytic_cycle p]
  exact LinearMap.mem_range

/--
Membership in `hodge_class p` is exactly the `(p,p)` condition after complexifying a rational
class.
-/
theorem mem_hodge_class_iff_complexified
    (data : HodgeData X) (p : ℕ) (x : data.cohomology_q (2 * p)) :
    x ∈ data.hodge_class p ↔
      data.extension_of_scalars_qc (2 * p) x ∈ data.hodge_subspace (2 * p) p p := by
  rfl

/--
The `ℚ`-subspace `H^{2p}(X, ℚ) ∩ F^p ⊂ H^{2p}(X, ℂ)` from the Clay PDF (Section 1),
expressed as a `ℚ`-submodule of `H^{2p}(X, ℚ)` by taking a preimage under complexification.

The Clay PDF notes that, for projective non-singular varieties,
`H^{2p}(X, ℚ) ∩ H^{p,p}(X) = H^{2p}(X, ℚ) ∩ F^p`.
In this repository we define `hodge_class` using the `(p,p)`-summand, and also provide this
filtration-based variant.
-/
noncomputable def hodge_class_filtration (data : HodgeData X) (p : ℕ) : Submodule ℚ (data.cohomology_q (2 * p)) :=
  Submodule.comap (data.extension_of_scalars_qc (2 * p))
    ((data.hodge_filtration (2 * p) p).restrictScalars ℚ)

/--
Membership in the filtration version is exactly membership in
`F^p H^{2p}(X,ℂ)` after complexification.
-/
theorem mem_hodge_class_filtration_iff_complexified
    (data : HodgeData X) (p : ℕ) (x : data.cohomology_q (2 * p)) :
    x ∈ data.hodge_class_filtration p ↔
      data.extension_of_scalars_qc (2 * p) x ∈ data.hodge_filtration (2 * p) p := by
  rfl

/-- Cycle classes are Hodge classes (the easy direction in the Clay write-up). -/
theorem cycle_class_mem_hodge_class (data : HodgeData X) (p : ℕ) (Z : data.algebraic_cycle p) :
    data.cycle_class p Z ∈ data.hodge_class p := by
  dsimp [HodgeData.hodge_class]
  simpa using data.cycle_class_is_pp p Z

/-- Each cycle class belongs to the `ℚ`-span of all cycle classes. -/
theorem cycle_class_mem_algebraic (data : HodgeData X) (p : ℕ) (Z : data.algebraic_cycle p) :
    data.cycle_class p Z ∈ data.algebraic_cohomology p := by
  dsimp [HodgeData.algebraic_cohomology]
  exact Submodule.subset_span ⟨Z, rfl⟩

/--
Any `(p,p)`-Hodge class is also in the filtration `F^p`.

This corresponds to the inclusion `H^{p,p}(X) ⊂ F^p` for `H^{2p}(X,ℂ)`.
-/
theorem hodge_class_le_hodge_class_filtration (data : HodgeData X) (p : ℕ) :
    data.hodge_class p ≤ data.hodge_class_filtration p := by
  have hpp :
      data.hodge_subspace (2 * p) p p ≤ data.hodge_filtration (2 * p) p := by
    have hp2p : p ≤ 2 * p := by
      -- `p = 1 * p ≤ 2 * p`.
      simpa using (Nat.mul_le_mul_right p (show 1 ≤ 2 from by decide))
    have h2p : 2 * p - p = p := by
      have h : p = p * 2 - p := by
        simpa using (Nat.mul_sub_left_distrib p 2 1)
      simpa [Nat.mul_comm] using h.symm
    have hpp' :
        data.hodge_subspace (2 * p) p (2 * p - p) ≤ data.hodge_filtration (2 * p) p :=
      data.hodge_subspace_le_hodge_filtration (n := 2 * p) (p := p) (a := p) le_rfl hp2p
    simpa [h2p] using hpp'
  have hppQ :
      (data.hodge_subspace (2 * p) p p).restrictScalars ℚ ≤
        (data.hodge_filtration (2 * p) p).restrictScalars ℚ := by
    intro x hx
    exact hpp hx
  exact Submodule.comap_mono (f := data.extension_of_scalars_qc (2 * p)) hppQ

/--
Cycle classes lie in the Hodge filtration `F^p` after complexification.

This is the filtration reformulation of “cycle classes are of type `(p,p)`”
from the Clay PDF (Section 1).
-/
theorem cycle_class_mem_hodge_filtration (data : HodgeData X) (p : ℕ) (Z : data.algebraic_cycle p) :
    data.extension_of_scalars_qc (2 * p) (data.cycle_class p Z) ∈ data.hodge_filtration (2 * p) p := by
  have hp2p : p ≤ 2 * p := by
    simpa using (Nat.mul_le_mul_right p (show 1 ≤ 2 from by decide))
  have h2p : 2 * p - p = p := by
    have h : p = p * 2 - p := by
      simpa using (Nat.mul_sub_left_distrib p 2 1)
    simpa [Nat.mul_comm] using h.symm
  have hmem :
      data.extension_of_scalars_qc (2 * p) (data.cycle_class p Z) ∈ data.hodge_subspace (2 * p) p (2 * p - p) := by
    simpa [h2p] using data.cycle_class_is_pp p Z
  exact (data.hodge_subspace_le_hodge_filtration (n := 2 * p) (p := p) (a := p) le_rfl hp2p) hmem

/-- Cycle classes are Hodge classes in the filtration sense `H^{2p}(X,ℚ) ∩ F^p`. -/
theorem cycle_class_mem_hodge_class_filtration (data : HodgeData X) (p : ℕ) (Z : data.algebraic_cycle p) :
    data.cycle_class p Z ∈ data.hodge_class_filtration p := by
  dsimp [HodgeData.hodge_class_filtration]
  simpa using data.cycle_class_mem_hodge_filtration p Z

/-- Every algebraic class is a Hodge class in the filtration sense `H^{2p}(X,ℚ) ∩ F^p`. -/
theorem algebraic_le_hodge_class_filtration (data : HodgeData X) (p : ℕ) :
    data.algebraic_cohomology p ≤ data.hodge_class_filtration p := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  exact data.cycle_class_mem_hodge_class_filtration p Z

/--
The conjectural inclusion `hodge_class_filtration ≤ algebraic_cohomology` is equivalent to equality,
because `algebraic_cohomology ≤ hodge_class_filtration` is already proved above.
-/
theorem hodge_class_filtration_eq_algebraic_cohomology_iff_le (data : HodgeData X) (p : ℕ) :
    data.hodge_class_filtration p = data.algebraic_cohomology p ↔
      data.hodge_class_filtration p ≤ data.algebraic_cohomology p := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm h (data.algebraic_le_hodge_class_filtration p)

/--
Every algebraic class is a Hodge class.

This direction is immediate from `cycle_class_is_pp`; it is not the Millennium conjecture.
-/
theorem algebraic_cohomology_le_hodge_class (data : HodgeData X) (p : ℕ) :
    data.algebraic_cohomology p ≤ data.hodge_class p := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  exact data.cycle_class_mem_hodge_class p Z

/--
The conjectural direction `hodge_class ≤ algebraic_cohomology` is equivalent to equality, because
`algebraic_cohomology ≤ hodge_class` is already proved above.
-/
theorem hodge_class_eq_algebraic_cohomology_iff_le (data : HodgeData X) (p : ℕ) :
    data.hodge_class p = data.algebraic_cohomology p ↔
      data.hodge_class p ≤ data.algebraic_cohomology p := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm h (data.algebraic_cohomology_le_hodge_class p)

/--
If every rational cohomology class in degree `2p` is the class of an algebraic cycle, then every
Hodge class in that degree is algebraic.
-/
theorem hodge_class_le_algebraic_surjective
    (data : HodgeData X) (p : ℕ)
    (hSurj : ∀ x : data.cohomology_q (2 * p), ∃ Z : data.algebraic_cycle p, data.cycle_class p Z = x) :
    data.hodge_class p ≤ data.algebraic_cohomology p := by
  intro x _hx
  rcases hSurj x with ⟨Z, hZ⟩
  rw [← hZ]
  exact data.cycle_class_mem_algebraic p Z

/--
Surjectivity of the cycle-class map in every even degree implies the Hodge conjecture for the
chosen Hodge data.
-/
theorem hodge_conjecture_surjective_cycle_class
    (data : HodgeData X)
    (hSurj :
      ∀ p : ℕ, ∀ x : data.cohomology_q (2 * p),
        ∃ Z : data.algebraic_cycle p, data.cycle_class p Z = x) :
    ∀ p : ℕ, data.hodge_class p ≤ data.algebraic_cohomology p := by
  intro p
  exact data.hodge_class_le_algebraic_surjective p (hSurj p)

end HodgeData

/--
Coherence conditions for Hodge-theoretic data.

These conditions connect the Hodge summands, total degree, and Hodge filtration in the form used
by the Clay statement.
-/
structure HodgeDataCoherence {X : SmoothProjectiveVariety ℂ} (data : HodgeData X) : Prop where
  /-- The summand `H^{p,q}` contributes only to degree `p+q`. -/
  hodge_subspace_eq_bot_of_degree_ne :
    ∀ n p q : ℕ, p + q ≠ n → data.hodge_subspace n p q = ⊥
  /--
  The projective Hodge-theory identity used by the Clay PDF:
  rational `(p,p)`-classes equal rational classes in the Hodge filtration `F^p`.
  -/
  hodge_class_eq_hodge_class_filtration :
    ∀ p : ℕ, data.hodge_class p = data.hodge_class_filtration p

namespace HodgeDataCoherence

variable {X : SmoothProjectiveVariety ℂ} {data : HodgeData X}

/-- Coherent Hodge data supplies the filtration agreement used in the Clay formulation. -/
theorem filtration_agreement (coh : HodgeDataCoherence data) :
    ∀ p : ℕ, data.hodge_class p = data.hodge_class_filtration p :=
  coh.hodge_class_eq_hodge_class_filtration

/-- Coherent Hodge data rules out off-degree Hodge summands. -/
theorem hodge_subspace_eq_bot (coh : HodgeDataCoherence data) {n p q : ℕ}
    (hdeg : p + q ≠ n) :
    data.hodge_subspace n p q = ⊥ :=
  coh.hodge_subspace_eq_bot_of_degree_ne n p q hdeg

/-- Membership in an off-degree Hodge summand is equivalent to being zero. -/
theorem mem_hodge_subspace_iff_eq_zero_of_degree_ne
    (coh : HodgeDataCoherence data) {n p q : ℕ} (hdeg : p + q ≠ n)
    (x : data.cohomology_c n) :
    x ∈ data.hodge_subspace n p q ↔ x = 0 := by
  rw [coh.hodge_subspace_eq_bot hdeg]
  simp

/-- In degree `2p`, the only potentially nonzero summand of the form `H^{p,q}` has `q = p`. -/
theorem hodge_subspace_eq_bot_of_off_diagonal
    (coh : HodgeDataCoherence data) {p q : ℕ} (hqp : q ≠ p) :
    data.hodge_subspace (2 * p) p q = ⊥ := by
  apply coh.hodge_subspace_eq_bot
  intro hdeg
  have hpq : p + q = p + p := by
    simpa [two_mul] using hdeg
  exact hqp (Nat.add_left_cancel hpq)

/-- Off-diagonal classes in degree `2p` are zero for coherent Hodge data. -/
theorem mem_hodge_subspace_iff_eq_zero_of_off_diagonal
    (coh : HodgeDataCoherence data) {p q : ℕ} (hqp : q ≠ p)
    (x : data.cohomology_c (2 * p)) :
    x ∈ data.hodge_subspace (2 * p) p q ↔ x = 0 := by
  rw [coh.hodge_subspace_eq_bot_of_off_diagonal hqp]
  simp

end HodgeDataCoherence

/-!
## Synthetic Hodge-data examples

The following constructions are **not** the Clay Hodge theory of a smooth projective variety.
They are small internal examples used to test the `HodgeData` interface: the cycle-class map,
filtration agreement, Chow comparison, and algebraic-span lemmas should behave correctly in
degenerate and finite-dimensional examples.

The Hodge Millennium statement in `Problems.Hodge.Millennium` quantifies over all coherent
Hodge-theory data packages.  That is a stronger abstract-data envelope around the canonical Clay
statement.  The models below should therefore be read only as consistency checks for the formal
interface, not as witnesses for the Millennium problem.

### One-dimensional model

The following Hodge data has `H^n(X,ℚ) = ℚ` and `H^n(X,ℂ) = ℂ` in every degree, scalar extension
given by the canonical map `ℚ → ℂ`, and one algebraic cycle for every rational class in degree
`2p`.  Its Hodge summands are `⊤` exactly in the matching degree `p+q=n` and `⊥` otherwise.
-/

/-- Synthetic nonzero one-dimensional Hodge data with surjective cycle-class maps. -/
noncomputable def rational_hodge_data (X : SmoothProjectiveVariety ℂ) : HodgeData X :=
  { cohomology_q := fun _ => ℚ
    cohomology_q_add := fun _ => inferInstance
    cohomology_q_module := fun _ => inferInstance
    cohomology_c := fun _ => ℂ
    cohomology_c_add := fun _ => inferInstance
    cohomology_c_module_c := fun _ => inferInstance
    cohomology_c_module_q := fun _ => inferInstance
    cohomology_c_is_scalar_tower := fun _ => inferInstance
    extension_of_scalars_qc := fun _ => Algebra.linearMap ℚ ℂ
    hodge_subspace := fun n p q => if p + q = n then ⊤ else ⊥
    algebraic_cycle := fun _ => ℚ
    closed_analytic_subspace := fun _ => ℚ
    algebraic_cycle_codimension := fun p _ => p
    algebraic_cycle_codimension_eq := by intro p Z; rfl
    closed_analytic_subspace_codimension := fun p _ => p
    closed_analytic_subspace_codimension_eq := by intro p A; rfl
    chow_equiv := fun _ => Equiv.refl ℚ
    cycle_class := fun _ Z => Z
    cycle_class_is_pp := by
      intro p Z
      dsimp
      rw [if_pos]
      · exact Submodule.mem_top
      · simp [two_mul] }

/-- In the one-dimensional Hodge theory, every rational class is a Hodge class. -/
theorem RationalHodgeData.hodge_class_eq_top
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (rational_hodge_data X).hodge_class p = ⊤ := by
  ext x
  constructor
  · intro _hx
    change x ∈ (⊤ : Submodule ℚ ℚ)
    exact Submodule.mem_top
  · intro _hx
    dsimp [HodgeData.hodge_class, rational_hodge_data]
    rw [if_pos]
    · exact Submodule.mem_top
    · simp [two_mul]

/-- In the one-dimensional model, the chosen Hodge filtration contains every rational class. -/
theorem RationalHodgeData.hodge_filtration_eq_top
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (rational_hodge_data X).hodge_filtration (2 * p) p = ⊤ := by
  rw [eq_top_iff]
  intro z _hz
  have hp2p : p ≤ 2 * p := by
    simpa using (Nat.mul_le_mul_right p (show 1 ≤ 2 from by decide))
  have hdeg : p + (2 * p - p) = 2 * p := Nat.add_sub_cancel' hp2p
  have hmem : z ∈ (rational_hodge_data X).hodge_subspace (2 * p) p (2 * p - p) := by
    dsimp [rational_hodge_data]
    rw [if_pos hdeg]
    exact Submodule.mem_top
  exact (rational_hodge_data X).hodge_subspace_le_hodge_filtration
    (n := 2 * p) (p := p) (a := p) le_rfl hp2p hmem

/-- Hence the rational Hodge classes defined through the filtration also fill the whole space. -/
theorem RationalHodgeData.filtration_eq_top
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (rational_hodge_data X).hodge_class_filtration p = ⊤ := by
  rw [eq_top_iff]
  intro x _hx
  dsimp [HodgeData.hodge_class_filtration]
  rw [RationalHodgeData.hodge_filtration_eq_top]
  exact Submodule.mem_top

/-- In the one-dimensional Hodge theory, the cycle classes span all rational cohomology. -/
theorem RationalHodgeData.algebraic_eq_top
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (rational_hodge_data X).algebraic_cohomology p = ⊤ := by
  ext x
  constructor
  · intro _hx
    change x ∈ (⊤ : Submodule ℚ ℚ)
    exact Submodule.mem_top
  · intro _hx
    dsimp [HodgeData.algebraic_cohomology, rational_hodge_data]
    exact Submodule.subset_span ⟨x, rfl⟩

/-- The one-dimensional Hodge theory has surjective cycle-class maps in every codimension. -/
theorem RationalHodgeData.cycle_class_surjective
    (X : SmoothProjectiveVariety ℂ) :
    ∀ p : ℕ, ∀ x : (rational_hodge_data X).cohomology_q (2 * p),
      ∃ Z : (rational_hodge_data X).algebraic_cycle p,
        (rational_hodge_data X).cycle_class p Z = x := by
  intro p x
  exact ⟨x, rfl⟩

/-- Every Hodge class in the one-dimensional rational theory is represented by a cycle. -/
theorem RationalHodgeData.hodge_class_has_cycle
    (X : SmoothProjectiveVariety ℂ) (p : ℕ)
    (x : (rational_hodge_data X).cohomology_q (2 * p))
    (_hx : x ∈ (rational_hodge_data X).hodge_class p) :
    ∃ Z : (rational_hodge_data X).algebraic_cycle p,
      (rational_hodge_data X).cycle_class p Z = x := by
  exact ⟨x, rfl⟩

/-- The one-dimensional Hodge theory satisfies the coherence conditions. -/
theorem RationalHodgeData.coherence (X : SmoothProjectiveVariety ℂ) :
    HodgeDataCoherence (rational_hodge_data X) := by
  constructor
  · intro n p q hdeg
    dsimp [rational_hodge_data]
    rw [if_neg hdeg]
    rfl
  · intro p
    rw [RationalHodgeData.hodge_class_eq_top, RationalHodgeData.filtration_eq_top]

/-- The Hodge conjecture holds for the one-dimensional Hodge theory. -/
theorem RationalHodgeData.hodge_class_le_algebraic
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (rational_hodge_data X).hodge_class p ≤ (rational_hodge_data X).algebraic_cohomology p := by
  intro x _hx
  rw [RationalHodgeData.algebraic_eq_top]
  exact Submodule.mem_top

/-- In the one-dimensional rational Hodge theory, Hodge classes are exactly algebraic classes. -/
theorem RationalHodgeData.hodge_class_eq_algebraic
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (rational_hodge_data X).hodge_class p = (rational_hodge_data X).algebraic_cohomology p := by
  rw [RationalHodgeData.hodge_class_eq_top, RationalHodgeData.algebraic_eq_top]

/-!
## Synthetic finite-dimensional rational Hodge theories

The one-dimensional construction extends to any finite rank `m`: rational cohomology is
`Fin m → ℚ`, complex cohomology is `Fin m → ℂ`, scalar extension is coordinatewise, and every
rational cohomology class is represented by an algebraic cycle.
-/

/-- Coordinatewise extension of scalars from `Fin m → ℚ` to `Fin m → ℂ`. -/
noncomputable def rational_vector_extension (m : ℕ) :
    (Fin m → ℚ) →ₗ[ℚ] (Fin m → ℂ) where
  toFun x i := algebraMap ℚ ℂ (x i)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro a x
    ext i
    change algebraMap ℚ ℂ (a * x i) = a • algebraMap ℚ ℂ (x i)
    rw [map_mul]
    exact (Algebra.smul_def a (algebraMap ℚ ℂ (x i))).symm

/-- Synthetic finite-dimensional rational Hodge data with surjective cycle-class maps. -/
noncomputable def finite_rational_hodge_data (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    HodgeData X :=
  { cohomology_q := fun _ => Fin m → ℚ
    cohomology_q_add := fun _ => inferInstance
    cohomology_q_module := fun _ => inferInstance
    cohomology_c := fun _ => Fin m → ℂ
    cohomology_c_add := fun _ => inferInstance
    cohomology_c_module_c := fun _ => inferInstance
    cohomology_c_module_q := fun _ => inferInstance
    cohomology_c_is_scalar_tower := fun _ => inferInstance
    extension_of_scalars_qc := fun _ => rational_vector_extension m
    hodge_subspace := fun n p q => if p + q = n then ⊤ else ⊥
    algebraic_cycle := fun _ => Fin m → ℚ
    closed_analytic_subspace := fun _ => Fin m → ℚ
    algebraic_cycle_codimension := fun p _ => p
    algebraic_cycle_codimension_eq := by intro p Z; rfl
    closed_analytic_subspace_codimension := fun p _ => p
    closed_analytic_subspace_codimension_eq := by intro p A; rfl
    chow_equiv := fun _ => Equiv.refl (Fin m → ℚ)
    cycle_class := fun _ Z => Z
    cycle_class_is_pp := by
      intro p Z
      change rational_vector_extension m Z ∈
        (if p + p = 2 * p then (⊤ : Submodule ℂ (Fin m → ℂ)) else ⊥)
      rw [if_pos]
      · exact Submodule.mem_top
      · simp [two_mul] }

/-- In the finite-dimensional rational Hodge theory, every rational class is a Hodge class. -/
theorem FiniteRationalHodgeData.hodge_class_eq_top
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (finite_rational_hodge_data m X).hodge_class p = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Submodule.mem_top
  · intro _hx
    dsimp [HodgeData.hodge_class, finite_rational_hodge_data]
    rw [if_pos]
    · exact Submodule.mem_top
    · simp [two_mul]

/-- In the finite-dimensional rational Hodge theory, every class lies in the Hodge filtration. -/
theorem FiniteRationalHodgeData.hodge_filtration_eq_top
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (finite_rational_hodge_data m X).hodge_filtration (2 * p) p = ⊤ := by
  rw [eq_top_iff]
  intro z _hz
  have hp2p : p ≤ 2 * p := by
    simpa using (Nat.mul_le_mul_right p (show 1 ≤ 2 from by decide))
  have hdeg : p + (2 * p - p) = 2 * p := Nat.add_sub_cancel' hp2p
  have hmem : z ∈ (finite_rational_hodge_data m X).hodge_subspace (2 * p) p (2 * p - p) := by
    dsimp [finite_rational_hodge_data]
    rw [if_pos hdeg]
    exact Submodule.mem_top
  exact (finite_rational_hodge_data m X).hodge_subspace_le_hodge_filtration
    (n := 2 * p) (p := p) (a := p) le_rfl hp2p hmem

/-- In the finite-dimensional rational Hodge theory, every rational class lies in the filtration class space. -/
theorem FiniteRationalHodgeData.filtration_eq_top
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (finite_rational_hodge_data m X).hodge_class_filtration p = ⊤ := by
  rw [eq_top_iff]
  intro x _hx
  dsimp [HodgeData.hodge_class_filtration]
  rw [FiniteRationalHodgeData.hodge_filtration_eq_top]
  exact Submodule.mem_top

/-- In the finite-dimensional rational Hodge theory, cycle classes span all rational cohomology. -/
theorem FiniteRationalHodgeData.algebraic_eq_top
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (finite_rational_hodge_data m X).algebraic_cohomology p = ⊤ := by
  ext x
  constructor
  · intro _hx
    exact Submodule.mem_top
  · intro _hx
    change x ∈ Submodule.span ℚ (Set.range (fun Z : Fin m → ℚ => Z))
    exact Submodule.subset_span ⟨x, rfl⟩

/-- The finite-dimensional rational Hodge theory has surjective cycle-class maps. -/
theorem FiniteRationalHodgeData.cycle_class_surjective
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    ∀ p : ℕ, ∀ x : (finite_rational_hodge_data m X).cohomology_q (2 * p),
      ∃ Z : (finite_rational_hodge_data m X).algebraic_cycle p,
        (finite_rational_hodge_data m X).cycle_class p Z = x := by
  intro p x
  exact ⟨x, rfl⟩

/-- Every Hodge class in the finite-dimensional rational theory is represented by a cycle. -/
theorem FiniteRationalHodgeData.hodge_class_has_cycle
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ)
    (x : (finite_rational_hodge_data m X).cohomology_q (2 * p))
    (_hx : x ∈ (finite_rational_hodge_data m X).hodge_class p) :
    ∃ Z : (finite_rational_hodge_data m X).algebraic_cycle p,
      (finite_rational_hodge_data m X).cycle_class p Z = x := by
  exact ⟨x, rfl⟩

/-- The coordinate basis cycle maps to the same coordinate basis cohomology class. -/
theorem FiniteRationalHodgeData.cycle_class_single
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) (i : Fin m) :
    (finite_rational_hodge_data m X).cycle_class p (Pi.single i (1 : ℚ)) =
      Pi.single i (1 : ℚ) := by
  rfl

/-- Each coordinate basis class is algebraic in the finite-dimensional rational Hodge theory. -/
theorem FiniteRationalHodgeData.single_mem_algebraic
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) (i : Fin m) :
    Pi.single i (1 : ℚ) ∈ (finite_rational_hodge_data m X).algebraic_cohomology p := by
  change Pi.single i (1 : ℚ) ∈ Submodule.span ℚ (Set.range (fun Z : Fin m → ℚ => Z))
  exact Submodule.subset_span ⟨Pi.single i (1 : ℚ), rfl⟩

/-- The finite-dimensional rational Hodge theory satisfies the coherence conditions. -/
theorem FiniteRationalHodgeData.coherence
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) :
    HodgeDataCoherence (finite_rational_hodge_data m X) := by
  constructor
  · intro n p q hdeg
    dsimp [finite_rational_hodge_data]
    rw [if_neg hdeg]
    rfl
  · intro p
    rw [FiniteRationalHodgeData.hodge_class_eq_top,
      FiniteRationalHodgeData.filtration_eq_top]

/-- The Hodge conjecture holds for the finite-dimensional rational Hodge theory. -/
theorem FiniteRationalHodgeData.hodge_class_le_algebraic
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (finite_rational_hodge_data m X).hodge_class p ≤
      (finite_rational_hodge_data m X).algebraic_cohomology p := by
  intro x _hx
  rw [FiniteRationalHodgeData.algebraic_eq_top]
  exact Submodule.mem_top

/-- In the finite-dimensional rational Hodge theory, Hodge classes are exactly algebraic classes. -/
theorem FiniteRationalHodgeData.hodge_class_eq_algebraic
    (m : ℕ) (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (finite_rational_hodge_data m X).hodge_class p =
      (finite_rational_hodge_data m X).algebraic_cohomology p := by
  rw [FiniteRationalHodgeData.hodge_class_eq_top,
    FiniteRationalHodgeData.algebraic_eq_top]

/-!
### Zero model

The following one-point cohomology theory is a concrete model of the definitions above.  All
cohomology groups are the zero module, all Hodge summands are the whole zero module, and the single
cycle class is zero.  The Hodge conjecture is then provable directly from the definitions.

This is another interface example, not the geometric Hodge theory appearing in the Clay
statement.
-/

/-- The one-point cohomology group used by `zero_hodge_data`. -/
inductive ZeroCohomology : Type u
  | star

namespace ZeroCohomology

/-- The unique additive group structure on the one-point cohomology group. -/
instance : AddCommGroup ZeroCohomology where
  zero := star
  add _ _ := star
  neg _ := star
  nsmul _ _ := star
  zsmul _ _ := star
  add_assoc := by intro a b c; cases a; cases b; cases c; rfl
  zero_add := by intro a; cases a; rfl
  add_zero := by intro a; cases a; rfl
  neg_add_cancel := by intro a; cases a; rfl
  add_comm := by intro a b; cases a; cases b; rfl

/-- The unique module structure over any semiring on the one-point cohomology group. -/
instance (R : Type*) [Semiring R] : Module R ZeroCohomology where
  smul _ _ := star
  one_smul := by intro x; cases x; rfl
  mul_smul := by intro r s x; cases x; rfl
  smul_zero := by intro r; rfl
  smul_add := by intro r x y; cases x; cases y; rfl
  add_smul := by intro r s x; cases x; rfl
  zero_smul := by intro x; cases x; rfl

/-- Scalar towers act trivially on the one-point cohomology group. -/
instance (R S : Type*) [Semiring R] [Semiring S] [SMul R S] :
    IsScalarTower R S ZeroCohomology where
  smul_assoc := by intro r s x; cases x; rfl

/-- The one-point cohomology group is subsingleton. -/
instance : Subsingleton ZeroCohomology :=
  ⟨by intro x y; cases x; cases y; rfl⟩

/-- Every element of the one-point cohomology group is zero. -/
theorem eq_zero (x : ZeroCohomology) : x = 0 :=
  Subsingleton.elim x 0

end ZeroCohomology

/-- The unique rational linear map between zero cohomology groups. -/
noncomputable def zero_extension (_n : ℕ) : ZeroCohomology.{u} →ₗ[ℚ] ZeroCohomology.{v} :=
  0

/-- A concrete Hodge theory with zero cohomology in every degree. -/
noncomputable def zero_hodge_data (X : SmoothProjectiveVariety ℂ) :
    HodgeData.{u₁, u₂, u₃} X :=
  { cohomology_q := fun _ => ZeroCohomology.{u₁}
    cohomology_q_add := fun _ => inferInstance
    cohomology_q_module := fun _ => inferInstance
    cohomology_c := fun _ => ZeroCohomology.{u₂}
    cohomology_c_add := fun _ => inferInstance
    cohomology_c_module_c := fun _ => inferInstance
    cohomology_c_module_q := fun _ => inferInstance
    cohomology_c_is_scalar_tower := fun _ => inferInstance
    extension_of_scalars_qc := zero_extension
    hodge_subspace := fun _ _ _ => ⊤
    algebraic_cycle := fun _ => ZeroCohomology.{u₃}
    closed_analytic_subspace := fun _ => ZeroCohomology.{u₃}
    algebraic_cycle_codimension := fun p _ => p
    algebraic_cycle_codimension_eq := by intro p Z; rfl
    closed_analytic_subspace_codimension := fun p _ => p
    closed_analytic_subspace_codimension_eq := by intro p A; rfl
    chow_equiv := fun _ => Equiv.refl ZeroCohomology.{u₃}
    cycle_class := fun _ _ => 0
    cycle_class_is_pp := by intro _ _; exact Submodule.mem_top }

/-- The zero-cohomology Hodge theory satisfies the coherence conditions. -/
theorem ZeroHodgeData.coherence (X : SmoothProjectiveVariety ℂ) :
    HodgeDataCoherence (zero_hodge_data X) := by
  constructor
  · intro n p q _h
    dsimp [zero_hodge_data]
    ext x
    constructor
    · intro _hx
      rw [ZeroCohomology.eq_zero x]
      exact Submodule.zero_mem _
    · intro _hx
      exact Submodule.mem_top
  · intro p
    dsimp [zero_hodge_data, HodgeData.hodge_class, HodgeData.hodge_class_filtration]
    ext x
    constructor
    · intro _hx
      rw [ZeroCohomology.eq_zero x]
      exact Submodule.zero_mem _
    · intro _hx
      rw [ZeroCohomology.eq_zero x]
      exact Submodule.zero_mem _

/-- The Hodge conjecture holds for the constructed zero-cohomology Hodge theory. -/
theorem ZeroHodgeData.hodge_class_le_algebraic
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (zero_hodge_data X).hodge_class p ≤ (zero_hodge_data X).algebraic_cohomology p := by
  intro x _hx
  rw [ZeroCohomology.eq_zero x]
  exact Submodule.zero_mem _

/-- In the zero-cohomology Hodge theory, Hodge classes are exactly algebraic classes. -/
theorem ZeroHodgeData.hodge_class_eq_algebraic
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (zero_hodge_data X).hodge_class p = (zero_hodge_data X).algebraic_cohomology p :=
  le_antisymm (ZeroHodgeData.hodge_class_le_algebraic X p)
    ((zero_hodge_data X).algebraic_cohomology_le_hodge_class p)

/-- In the zero-cohomology Hodge theory, filtration Hodge classes are algebraic. -/
theorem ZeroHodgeData.filtration_le_algebraic
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (zero_hodge_data X).hodge_class_filtration p ≤ (zero_hodge_data X).algebraic_cohomology p := by
  intro x _hx
  rw [ZeroCohomology.eq_zero x]
  exact Submodule.zero_mem _

/--
In the zero-cohomology Hodge theory, filtration Hodge classes are exactly algebraic classes.
-/
theorem ZeroHodgeData.filtration_eq_algebraic
    (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (zero_hodge_data X).hodge_class_filtration p = (zero_hodge_data X).algebraic_cohomology p :=
  le_antisymm (ZeroHodgeData.filtration_le_algebraic X p)
    ((zero_hodge_data X).algebraic_le_hodge_class_filtration p)

end VarietyDefinition
