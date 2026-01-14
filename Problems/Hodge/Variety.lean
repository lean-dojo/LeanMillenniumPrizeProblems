import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Span.Defs

set_option linter.unusedVariables false
set_option diagnostics true
set_option diagnostics.threshold 5000

namespace VarietyDefinition

open AlgebraicGeometry Scheme Complex
open scoped BigOperators

/-!
## Hodge conjecture scaffolding (no axioms)

Mathlib does not currently provide a full development of singular cohomology of complex varieties
or the cycle class map in the generality needed for the Hodge conjecture. To keep this repository
`axiom`-free, we *parameterize* the statement by a package of data (`HodgeData`) containing the
relevant objects and maps.
-/

/-- A structure representing a smooth projective variety over a field. -/
structure SmoothProjectiveVariety (K : Type*) [Field K] where
  /-- The underlying scheme. -/
  X : Scheme
  /-- The scheme is smooth. -/
  is_smooth : Prop
  /-- The scheme is projective. -/
  is_projective : Prop

/--
All the extra objects needed to state the Hodge conjecture for a fixed variety `X`.

This is *data*, not an assertion that such objects exist.
-/
structure HodgeData (X : SmoothProjectiveVariety ℂ) where
  /-- Rational cohomology groups `H^n(X, ℚ)` (as `ℚ`-vector spaces). -/
  cohomologyQ : ℕ → Type*
  [cohomologyQ_add : ∀ n, AddCommGroup (cohomologyQ n)]
  [cohomologyQ_module : ∀ n, Module ℚ (cohomologyQ n)]

  /-- Complex cohomology groups `H^n(X, ℂ)` (as `ℂ`-vector spaces). -/
  cohomologyC : ℕ → Type*
  [cohomologyC_add : ∀ n, AddCommGroup (cohomologyC n)]
  [cohomologyC_moduleC : ∀ n, Module ℂ (cohomologyC n)]
  /-- We also view complex cohomology as a `ℚ`-module (restriction of scalars). -/
  [cohomologyC_moduleQ : ∀ n, Module ℚ (cohomologyC n)]
  /-- Compatibility of the `ℚ`- and `ℂ`-actions on `H^n(X, ℂ)`. -/
  [cohomologyC_isScalarTower : ∀ n, IsScalarTower ℚ ℂ (cohomologyC n)]

  /-- Extension of scalars `H^n(X, ℚ) → H^n(X, ℂ)` (as a `ℚ`-linear map). -/
  extensionOfScalarsQC : ∀ n : ℕ, cohomologyQ n →ₗ[ℚ] cohomologyC n

  /-- The Hodge summand `H^{p,q}(X) ⊂ H^n(X, ℂ)` (Clay PDF, equation (1)). -/
  hodgeSubspace : ∀ n p q : ℕ, Submodule ℂ (cohomologyC n)

  /-- Algebraic cycles of codimension `p`. -/
  algebraicCycle : ℕ → Type*
  /-- Cycle class map `Z^p(X) → H^{2p}(X, ℚ)` (a rational version of `cl(Z)`). -/
  cycleClass : ∀ p : ℕ, algebraicCycle p → cohomologyQ (2 * p)

  /--
  Cycle classes are of type `(p,p)` after complexification (Clay PDF, Section 1):
  `cl(Z)` maps into `H^{p,p}(X) ⊂ H^{2p}(X, ℂ)`.

  This is included as a *field* (data), not as an `axiom`.
  -/
  cycleClass_is_pp :
    ∀ p : ℕ, ∀ Z : algebraicCycle p,
      extensionOfScalarsQC (2 * p) (cycleClass p Z) ∈ hodgeSubspace (2 * p) p p

namespace HodgeData

variable {X : SmoothProjectiveVariety ℂ}

/-- The additive group structure on `H^n(X,ℚ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : AddCommGroup (data.cohomologyQ n) :=
  data.cohomologyQ_add n

/-- The `ℚ`-module structure on `H^n(X,ℚ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : Module ℚ (data.cohomologyQ n) :=
  data.cohomologyQ_module n

/-- The additive group structure on `H^n(X,ℂ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : AddCommGroup (data.cohomologyC n) :=
  data.cohomologyC_add n

/-- The `ℂ`-module structure on `H^n(X,ℂ)`, re-exported from the `HodgeData` fields. -/
instance (data : HodgeData X) (n : ℕ) : Module ℂ (data.cohomologyC n) :=
  data.cohomologyC_moduleC n

/-- The `ℚ`-module structure on `H^n(X,ℂ)`, by restriction of scalars (from the `HodgeData` fields). -/
instance (data : HodgeData X) (n : ℕ) : Module ℚ (data.cohomologyC n) :=
  data.cohomologyC_moduleQ n

/-- Compatibility of the `ℚ`- and `ℂ`-actions on `H^n(X,ℂ)` (from the `HodgeData` fields). -/
instance (data : HodgeData X) (n : ℕ) : IsScalarTower ℚ ℂ (data.cohomologyC n) :=
  data.cohomologyC_isScalarTower n

/--
The Hodge filtration `F^p H^n(X, ℂ) := ⊕_{a ≥ p} H^{a,n-a}` from the Clay PDF (Section 1).

We build it from the chosen Hodge summands `H^{a,n-a}` provided by `hodgeSubspace`.
-/
def hodgeFiltration (data : HodgeData X) (n p : ℕ) : Submodule ℂ (data.cohomologyC n) :=
  ⨆ a : ℕ, ⨆ (_ha : p ≤ a), ⨆ (_han : a ≤ n), data.hodgeSubspace n a (n - a)

/--
Each Hodge summand `H^{a,n-a}` with `a ≥ p` is contained in the Hodge filtration `F^p`.

This is immediate from the definition of `hodgeFiltration` as a supremum.
-/
theorem hodgeSubspace_le_hodgeFiltration (data : HodgeData X) (n p a : ℕ) (ha : p ≤ a) (han : a ≤ n) :
    data.hodgeSubspace n a (n - a) ≤ data.hodgeFiltration n p := by
  dsimp [HodgeData.hodgeFiltration]
  refine le_trans ?_ (le_iSup (fun a' : ℕ => ⨆ (_ha : p ≤ a'), ⨆ (_han : a' ≤ n),
    data.hodgeSubspace n a' (n - a')) a)
  refine le_trans ?_ (le_iSup (fun _ha : p ≤ a => ⨆ (_han : a ≤ n),
    data.hodgeSubspace n a (n - a)) ha)
  exact le_iSup (fun _han : a ≤ n => data.hodgeSubspace n a (n - a)) han

/--
The `ℚ`-subspace of Hodge classes in degree `2p` (Clay PDF, Section 1):
rational classes whose complexification lies in `H^{p,p}(X)`.
-/
def hodgeClass (data : HodgeData X) (p : ℕ) : Submodule ℚ (data.cohomologyQ (2 * p)) :=
  Submodule.comap (data.extensionOfScalarsQC (2 * p))
    ((data.hodgeSubspace (2 * p) p p).restrictScalars ℚ)

/-- The `ℚ`-subspace of cohomology generated by cycle classes. -/
def algebraicCohomology (data : HodgeData X) (p : ℕ) : Submodule ℚ (data.cohomologyQ (2 * p)) :=
  Submodule.span ℚ (Set.range (data.cycleClass p))

/--
The `ℚ`-subspace `H^{2p}(X, ℚ) ∩ F^p ⊂ H^{2p}(X, ℂ)` from the Clay PDF (Section 1),
expressed as a `ℚ`-submodule of `H^{2p}(X, ℚ)` by taking a preimage under complexification.

The Clay PDF notes that, for projective non-singular varieties,
`H^{2p}(X, ℚ) ∩ H^{p,p}(X) = H^{2p}(X, ℚ) ∩ F^p`.
In this repository we define `hodgeClass` using the `(p,p)`-summand, and also provide this
filtration-based variant.
-/
def hodgeClassFiltration (data : HodgeData X) (p : ℕ) : Submodule ℚ (data.cohomologyQ (2 * p)) :=
  Submodule.comap (data.extensionOfScalarsQC (2 * p))
    ((data.hodgeFiltration (2 * p) p).restrictScalars ℚ)

/-- Cycle classes are Hodge classes (the easy direction in the Clay write-up). -/
theorem cycleClass_mem_hodgeClass (data : HodgeData X) (p : ℕ) (Z : data.algebraicCycle p) :
    data.cycleClass p Z ∈ data.hodgeClass p := by
  dsimp [HodgeData.hodgeClass]
  simpa using data.cycleClass_is_pp p Z

/-- Each cycle class belongs to the `ℚ`-span of all cycle classes. -/
theorem cycleClass_mem_algebraicCohomology (data : HodgeData X) (p : ℕ) (Z : data.algebraicCycle p) :
    data.cycleClass p Z ∈ data.algebraicCohomology p := by
  dsimp [HodgeData.algebraicCohomology]
  exact Submodule.subset_span ⟨Z, rfl⟩

/--
Any `(p,p)`-Hodge class is also in the filtration `F^p`.

This corresponds to the inclusion `H^{p,p}(X) ⊂ F^p` for `H^{2p}(X,ℂ)`.
-/
theorem hodgeClass_le_hodgeClassFiltration (data : HodgeData X) (p : ℕ) :
    data.hodgeClass p ≤ data.hodgeClassFiltration p := by
  have hpp :
      data.hodgeSubspace (2 * p) p p ≤ data.hodgeFiltration (2 * p) p := by
    have hp2p : p ≤ 2 * p := by
      -- `p = 1 * p ≤ 2 * p`.
      simpa using (Nat.mul_le_mul_right p (show 1 ≤ 2 from by decide))
    have h2p : 2 * p - p = p := by
      have h : p = p * 2 - p := by
        simpa using (Nat.mul_sub_left_distrib p 2 1)
      simpa [Nat.mul_comm] using h.symm
    have hpp' :
        data.hodgeSubspace (2 * p) p (2 * p - p) ≤ data.hodgeFiltration (2 * p) p :=
      data.hodgeSubspace_le_hodgeFiltration (n := 2 * p) (p := p) (a := p) le_rfl hp2p
    simpa [h2p] using hpp'
  have hppQ :
      (data.hodgeSubspace (2 * p) p p).restrictScalars ℚ ≤
        (data.hodgeFiltration (2 * p) p).restrictScalars ℚ := by
    intro x hx
    exact hpp hx
  exact Submodule.comap_mono (f := data.extensionOfScalarsQC (2 * p)) hppQ

/--
Cycle classes lie in the Hodge filtration `F^p` after complexification.

This is the filtration reformulation of “cycle classes are of type `(p,p)`”
from the Clay PDF (Section 1).
-/
theorem cycleClass_mem_hodgeFiltration (data : HodgeData X) (p : ℕ) (Z : data.algebraicCycle p) :
    data.extensionOfScalarsQC (2 * p) (data.cycleClass p Z) ∈ data.hodgeFiltration (2 * p) p := by
  have hp2p : p ≤ 2 * p := by
    simpa using (Nat.mul_le_mul_right p (show 1 ≤ 2 from by decide))
  have h2p : 2 * p - p = p := by
    have h : p = p * 2 - p := by
      simpa using (Nat.mul_sub_left_distrib p 2 1)
    simpa [Nat.mul_comm] using h.symm
  have hmem :
      data.extensionOfScalarsQC (2 * p) (data.cycleClass p Z) ∈ data.hodgeSubspace (2 * p) p (2 * p - p) := by
    simpa [h2p] using data.cycleClass_is_pp p Z
  exact (data.hodgeSubspace_le_hodgeFiltration (n := 2 * p) (p := p) (a := p) le_rfl hp2p) hmem

/-- Cycle classes are Hodge classes in the filtration sense `H^{2p}(X,ℚ) ∩ F^p`. -/
theorem cycleClass_mem_hodgeClassFiltration (data : HodgeData X) (p : ℕ) (Z : data.algebraicCycle p) :
    data.cycleClass p Z ∈ data.hodgeClassFiltration p := by
  dsimp [HodgeData.hodgeClassFiltration]
  simpa using data.cycleClass_mem_hodgeFiltration p Z

/-- Every algebraic class is a Hodge class in the filtration sense `H^{2p}(X,ℚ) ∩ F^p`. -/
theorem algebraicCohomology_le_hodgeClassFiltration (data : HodgeData X) (p : ℕ) :
    data.algebraicCohomology p ≤ data.hodgeClassFiltration p := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  exact data.cycleClass_mem_hodgeClassFiltration p Z

/--
In this scaffolding, the conjectural inclusion `hodgeClassFiltration ≤ algebraicCohomology`
is equivalent to equality, because we always have `algebraicCohomology ≤ hodgeClassFiltration`.
-/
theorem hodgeClassFiltration_eq_algebraicCohomology_iff (data : HodgeData X) (p : ℕ) :
    data.hodgeClassFiltration p = data.algebraicCohomology p ↔
      data.hodgeClassFiltration p ≤ data.algebraicCohomology p := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm h (data.algebraicCohomology_le_hodgeClassFiltration p)

/--
Every algebraic class is a Hodge class.

This direction is immediate from `cycleClass_is_pp`; it is not the Millennium conjecture.
-/
theorem algebraicCohomology_le_hodgeClass (data : HodgeData X) (p : ℕ) :
    data.algebraicCohomology p ≤ data.hodgeClass p := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  exact data.cycleClass_mem_hodgeClass p Z

/--
In this scaffolding, the conjectural direction `hodgeClass ≤ algebraicCohomology`
is equivalent to equality, because we always have `algebraicCohomology ≤ hodgeClass`.
-/
theorem hodgeClass_eq_algebraicCohomology_iff (data : HodgeData X) (p : ℕ) :
    data.hodgeClass p = data.algebraicCohomology p ↔
      data.hodgeClass p ≤ data.algebraicCohomology p := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm h (data.algebraicCohomology_le_hodgeClass p)

end HodgeData

end VarietyDefinition
