import Problems.Hodge.Variety

namespace MillenniumHodge

open AlgebraicGeometry Scheme Complex Algebra VarietyDefinition

universe u u₁ u₂ u₃

/-!
# The Hodge Conjecture

This file states the Clay Millennium problem “Hodge conjecture” in Lean, following the official
Clay problem description:
`Problems/Hodge/references/clay/hodge.pdf`.

Mathlib does not currently include the full algebro-geometric and cohomological foundations
needed to *construct* the cycle class map and Hodge decomposition in the required generality.
To keep this repository `axiom`-free, the statement is parameterized by a data package
`HodgeData` (see `Problems/Hodge/Variety.lean`).

## What is the Hodge Conjecture?

The Hodge Conjecture provides a link between algebraic geometry and differential geometry.
It states that for a non-singular complex projective variety X, every Hodge class is a rational
linear combination of the cohomology classes of algebraic cycles.

More precisely:
- A Hodge class is a rational cohomology class whose complexification lies in the `(p,p)`-summand
  `H^{p,p}(X) ⊂ H^{2p}(X, ℂ)` of the Hodge decomposition (Clay PDF, equation (1)).
- The cycle class of an algebraic cycle is always a Hodge class (Clay PDF, Section 1).
- The conjecture is the converse: every Hodge class is a `ℚ`-linear combination of cycle classes.

This connection is profound because Hodge classes are defined using analysis and differential
geometry (through the Hodge decomposition), while algebraic cycles are purely algebro-geometric
objects.

## Main definitions from Variety.lean

* `SmoothProjectiveVariety`: A smooth projective variety over a field
* `algebraicCycle`: Algebraic cycles of codimension p
* `cycleClass`: The cohomology class of an algebraic cycle
* `HodgeData.hodgeSubspace`: chosen summands `H^{p,q}(X) ⊂ H^n(X, ℂ)`
* `HodgeData.hodgeFiltration`: the Hodge filtration `F^p H^n(X, ℂ)`
* `HodgeData.hodgeClass`: rational `(p,p)`-classes (preimage under complexification)
* `HodgeData.hodgeClassFiltration`: the filtration form `H^{2p}(X,ℚ) ∩ F^p`
* `HodgeData.algebraicCohomology`: the `ℚ`-span of cycle classes
* `HodgeConjecture`: the formal statement of the Millennium problem

## Not yet formalized from the Clay PDF

The Clay write-up contains substantial geometric and Hodge-theoretic content beyond the core
Millennium statement.  At present we do **not** formalize (among other things):

* The cohomology theory itself (singular cohomology of complex varieties) and the construction of
  the cycle class map `cl(Z)` via currents / Poincaré duality.
* The Hodge decomposition isomorphism (Clay PDF, equation (1)) as a *theorem*:
  `H^n(X, ℂ) ≃ ⊕_{p+q=n} H^{p,q}(X)`, nor the harmonic-form interpretation.
* The equality `H^{2p}(X, ℚ) ∩ H^{p,p}(X) = H^{2p}(X, ℚ) ∩ F^p` as a theorem; we provide both
  notions (`hodgeClass` and `hodgeClassFiltration`) and prove the easy inclusion
  `hodgeClass ≤ hodgeClassFiltration`.
* The later sections of the PDF: remarks (e.g. Chow/GAGA), intermediate Jacobians, examples
  (diagonal class, Hard Lefschetz example), and the motives discussion.
-/

/--
The Hodge Conjecture: for a smooth complex projective variety,
every Hodge class is a rational linear combination of cycle classes.
-/
def HodgeConjecture : Prop :=
  ∀ (X : SmoothProjectiveVariety.{0, u} ℂ) (p : ℕ) (data : HodgeData.{u₁, u₂, u₃, u} X),
    data.hodgeClass p ≤ data.algebraicCohomology p

end MillenniumHodge
