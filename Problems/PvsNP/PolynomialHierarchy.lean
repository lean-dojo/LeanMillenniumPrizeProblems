import Mathlib.Computability.TuringMachine
import Mathlib.Computability.Primrec
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Init.Data.List.Lemmas
import Problems.PvsNP.Millennium

/-!
# The Polynomial Hierarchy

Okay this file was just for fun and basically I wanted to formalize the polynomial hierarchy (PH), which is a hierarchy of complexity classes
that extends the classes P and NP. The hierarchy provides a framework for classifying problems
that require multiple alternating layers of existential and universal quantification.

## Overview

The polynomial hierarchy is defined recursively:
- Σ₀ᴾ = Π₀ᴾ = Δ₀ᴾ = P
- Σᵏ⁺¹ᴾ = NP^{Σᵏᴾ} (problems solvable by an NP machine with access to a Σᵏᴾ oracle)
- Πᵏ⁺¹ᴾ = co-Σᵏ⁺¹ᴾ (the complements of problems in Σᵏ⁺¹ᴾ)
- Δᵏ⁺¹ᴾ = P^{Σᵏᴾ} (problems solvable in polynomial time with access to a Σᵏᴾ oracle)

## Examples

Examples of problems in different levels:
- Σ₁ᴾ (NP): SAT, Hamiltonian Path, Clique
- Π₁ᴾ (co-NP): TAUTOLOGY, No-Hamiltonian Path
- Σ₂ᴾ: MINSAT (minimizing the number of satisfied clauses)
- Π₂ᴾ: FORALL-EXISTS-SAT (formulas of the form ∀x∃y.φ(x,y))

## Collapse

I like the fact that If P = NP, then the entire polynomial hierarchy collapses to P.
Many believe the hierarchy is strict, meaning Σᵏᴾ ⊂ Σᵏ⁺¹ᴾ for all k.
-/

namespace Millennium
set_option linter.unusedVariables false
set_option diagnostics true
set_option diagnostics.threshold 7000

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
def Complement {α : Type} [Primcodable α] (L : Language α) : Language α :=
  fun a => ¬(L a)

/--
  Oracle machines are Turing machines that have access to an oracle,
  which can solve instances of a specific problem in a single step.

  This definition extends our complexity classes to handle oracle machines.
-/
def OracleLanguage {α β : Type} [Primcodable α] [Primcodable β]
    (oracle : Language β) (f : α → β) : Language α :=
  fun a => oracle (f a)

/--
  Σ₀ᴾ = Π₀ᴾ = Δ₀ᴾ = P

  The base level of the polynomial hierarchy is P, the class of
  problems solvable in polynomial time.
-/
def Sigma0P {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  InP ea

def Pi0P {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  Sigma0P ea

def Delta0P {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  Sigma0P ea

/--
  Σ₁ᴾ = NP

  The first level of the existential hierarchy is NP, which consists of
  problems verifiable in polynomial time with a suitable certificate.

  Examples: SAT, Hamiltonian Path, Clique problem
-/
def Sigma1P {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  InNP ea

/--
  Π₁ᴾ = co-NP

  The first level of the universal hierarchy is co-NP, which consists of
  problems whose complement is in NP.

  Examples: TAUTOLOGY, No-Hamiltonian Path, No-Clique
-/
def Pi1P {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  Sigma1P ea (Complement L)

/--
  Δ₁ᴾ = P

  The first level of the delta hierarchy is still P.
-/
def Delta1P {α : Type} [Primcodable α] (ea : FinEncoding α) : Language α → Prop :=
  InP ea

/--
  Δ₂ᴾ = P^NP

  The class of problems solvable in polynomial time given an oracle for NP.
  Equivalently, problems solvable by a polynomial-time algorithm that can
  make a polynomial number of calls to an NP oracle.

  Examples: Problems solvable by binary search over NP queries,
            Finding the exact size of a maximum clique using an NP oracle
-/
def Delta2P {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (β : Type) (instβ : Primcodable β) (eb : FinEncoding β) (L' : Language β) (f : α → β),
    Sigma1P eb L' ∧
    (∃ (comp : TM2ComputableInPolyTime ea eb f), ∀ a, L a ↔ L' (f a))


/--
  The general definition for Σₖᴾ can be recursive, representing
  k alternations of existential and universal quantifiers.
-/
def SigmakP (k : ℕ) : {α : Type} → [inst : Primcodable α] → (ea : FinEncoding α) → Language α → Prop
| α, inst, ea, L =>
  match k with
  | 0 => Sigma0P ea L
  | k+1 =>
      ∃ (β : Type) (instβ : Primcodable β) (eb : FinEncoding β) (L' : Language (α × β)),
        -- L' is in Πₖᴾ, i.e. its complement is in Σₖᴾ.
        SigmakP k (pairEncoding ea eb) (Complement L') ∧
        -- Certificate size is polynomially bounded.
        ∃ (p : Polynomial ℕ),
          ∀ a, L a ↔ ∃ b, (eb.encode b).length ≤ Polynomial.eval (ea.encode a).length p ∧ L' (a, b)

/--
`Πₖᴾ` is defined as complements of `Σₖᴾ`.

This definition is the standard one and avoids any `sorry`/axioms in the hierarchy definitions.
-/
def PikP (k : ℕ) : {α : Type} → [inst : Primcodable α] → (ea : FinEncoding α) → Language α → Prop
| _α, _inst, ea, L => SigmakP k ea (Complement L)
/--
  The polynomial hierarchy is the union of all Σₖᴾ classes.

  A problem is in PH if it is in Σₖᴾ for some k.

  The polynomial hierarchy collapses if there exists some k such that
  Σₖᴾ = Σₖ₊₁ᴾ, which would imply that for all j ≥ k, Σⱼᴾ = Σₖᴾ.
-/
def PolynomialHierarchy {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ k, SigmakP k ea L

/--
  # The polynomial hierarchy collapse conjecture.

  This states that the polynomial hierarchy collapses to some finite level.
  Most complexity theorists believe this is false, meaning the hierarchy
  is infinite (each level is strictly contained in the next).

  If P = NP, then the whole hierarchy collapses to P.
-/
def PHCollapses : Prop :=
  ∃ k, ∀ (α : Type) [Primcodable α] (ea : FinEncoding α) (L : Language α),
    SigmakP (k+1) ea L → SigmakP k ea L

/--
  # A common conjecture that the polynomial hierarchy does not collapse.

  This is related to the P ≠ NP conjecture. If P = NP, then the polynomial
  hierarchy collapses to the first level (P = NP = PH).
-/
def PHDoesNotCollapse : Prop :=
  ¬PHCollapses
end Millennium
