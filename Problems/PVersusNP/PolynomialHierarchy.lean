import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Init.Data.List.Lemmas
import Problems.PVersusNP.Millennium

/-!
# The Polynomial Hierarchy

This file defines the polynomial hierarchy (PH), a hierarchy of complexity classes extending P and NP.
We use the standard "quantifier" characterization: each level is obtained by adding a polynomially
bounded existential witness in front of a predicate from the previous co-level.

## Overview

The hierarchy is defined recursively (quantifier form):
- `Σ₀ᴾ = Π₀ᴾ = P`
- `Σₖ₊₁ᴾ` consists of languages `L` such that `a ∈ L ↔ ∃ b (|b| ≤ poly(|a|) ∧ (a,b) ∈ L')` for some `L' ∈ Πₖᴾ`
- `Πₖᴾ` is defined as complements of `Σₖᴾ`

This file uses the quantifier characterization, so it omits the oracle-machine `Δₖᴾ` classes.

## Examples

Examples of problems in different levels:
- Σ₁ᴾ (NP): SAT, Hamiltonian Path, Clique
- Π₁ᴾ (co-NP): TAUTOLOGY, No-Hamiltonian Path
- Σ₂ᴾ: MINSAT (minimizing the number of satisfied clauses)
- Π₂ᴾ: FORALL-EXISTS-SAT (formulas of the form ∀x∃y.φ(x,y))

## Collapse

If P = NP, then the entire polynomial hierarchy collapses to P.  Many complexity theorists believe
the hierarchy is strict, meaning Σᵏᴾ ⊂ Σᵏ⁺¹ᴾ for all k.
-/

namespace Millennium

open Turing
open Computability

/-
  We'll represent the polynomial hierarchy using alternating quantifiers.
  First, we define the complement of a language.
-/
/--
  The complement of a language L is the language consisting of
  all the strings that are not in L.

  For example, if SAT is the set of satisfiable Boolean formulas,
  then co-SAT is the set of unsatisfiable Boolean formulas.
-/
def complement {α : Type} [Primcodable α] (L : Language α) : Language α :=
  fun a => ¬(L a)

/--
`Σₖᴾ` defined via polynomially-bounded alternating quantifiers (quantifier form).

This is one standard characterization of the polynomial hierarchy; it avoids having to formalize
oracle machines inside the development.
-/
def polynomial_hierarchy_sigma_level (k : ℕ) : {α : Type} → [_inst : Primcodable α] → (ea : FinEncoding α) → Language α → Prop
| α, _inst, ea, L =>
  match k with
  | 0 => InPolynomialTime ea L
  | k+1 =>
      -- The witness `b` ranges over *all* finite strings over a finite alphabet `β` (identity
      -- encoding `fin_encoding_string β`), as in `InNondeterministicPolynomialTime`.
      ∃ (β : Type) (_instβ : Fintype β) (_primβ : Primcodable β) (L' : Language (α × List β)),
        -- `L'` is in `Πₖᴾ`, i.e. its complement is in `Σₖᴾ`.
        polynomial_hierarchy_sigma_level k (pair_encoding ea (fin_encoding_string β)) (complement L') ∧
        -- Witness size is polynomially bounded.
        ∃ (p : Polynomial ℕ),
          ∀ a, L a ↔ ∃ b : List β, b.length ≤ Polynomial.eval (ea.encode a).length p ∧ L' (a, b)

/--
`Πₖᴾ` is defined as complements of `Σₖᴾ`.
-/
def polynomial_hierarchy_pi_level (k : ℕ) : {α : Type} → [_inst : Primcodable α] → (ea : FinEncoding α) → Language α → Prop
| _α, _inst, ea, L => polynomial_hierarchy_sigma_level k ea (complement L)

/--
  Σ₀ᴾ = Π₀ᴾ = P

  The base level of the polynomial hierarchy is P, the class of
  problems solvable in polynomial time.
-/
def polynomial_hierarchy_sigma_level_zero {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  polynomial_hierarchy_sigma_level 0 ea

/-- `Π₀ᴾ = P` (since complements do not add power at level `0`). -/
def polynomial_hierarchy_pi_level_zero {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  polynomial_hierarchy_pi_level 0 ea

/--
  Σ₁ᴾ = NP

  The first level of the existential hierarchy is NP, which consists of
  problems verifiable in polynomial time with a suitable certificate.

  Examples: SAT, Hamiltonian Path, Clique problem
-/
def polynomial_hierarchy_sigma_level_one {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  polynomial_hierarchy_sigma_level 1 ea

/--
  Π₁ᴾ = co-NP

  The first level of the universal hierarchy is co-NP, which consists of
  problems whose complement is in NP.

  Examples: TAUTOLOGY, No-Hamiltonian Path, No-Clique
-/
def polynomial_hierarchy_pi_level_one {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  polynomial_hierarchy_pi_level 1 ea L
/--
  The polynomial hierarchy is the union of all Σₖᴾ classes.

  A problem is in PH if it is in Σₖᴾ for some k.

  The polynomial hierarchy collapses if there exists some k such that
  Σₖᴾ = Σₖ₊₁ᴾ, which would imply that for all j ≥ k, Σⱼᴾ = Σₖᴾ.
-/
def polynomial_hierarchy {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ k, polynomial_hierarchy_sigma_level k ea L

/--
  # The polynomial hierarchy collapse conjecture.

  This states that the polynomial hierarchy collapses to some finite level.
  Most complexity theorists believe this is false, meaning the hierarchy
  is infinite (each level is strictly contained in the next).

  If P = NP, then the whole hierarchy collapses to P.
-/
def polynomial_hierarchy_collapses : Prop :=
  ∃ k, ∀ (α : Type) [Primcodable α] (ea : FinEncoding α) (L : Language α),
    polynomial_hierarchy_sigma_level (k+1) ea L → polynomial_hierarchy_sigma_level k ea L

/--
  # A common conjecture that the polynomial hierarchy does not collapse.

  This is related to the P ≠ NP conjecture. If P = NP, then the polynomial
  hierarchy collapses to the first level (P = NP = PH).
-/
def polynomial_hierarchy_does_not_collapse : Prop :=
  ¬polynomial_hierarchy_collapses
end Millennium
