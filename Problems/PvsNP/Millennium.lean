import Mathlib.Tactic.Basic
import Mathlib.Computability.TuringMachine
import Mathlib.Computability.Primrec
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Init.Data.List.Lemmas

/-!
# The P vs NP Problem

This file formalizes the P vs NP problem, one of the seven Millennium Prize Problems
established by the Clay Mathematics Institute. I have used material from my undegraduate complexity theory course.
This was so fun to formalize and I also included another file polynomial time hierarchy.

## Overview

The P vs NP problem asks whether every problem whose solution can be quickly verified
by a computer (NP) can also be quickly solved by a computer (P).

- P refers to polynomial time: problems solvable in polynomial time
- NP refers to nondeterministic polynomial time: problems verifiable in polynomial time

## Examples

Examples of problems in P:
- Sorting a list of numbers
- Finding the greatest common divisor of two integers
- Determining if a number is prime (AKS algorithm)

Examples of problems in NP:
- Boolean satisfiability problem (SAT)
- Traveling salesman problem (TSP)
- Integer factorization
- Graph coloring

Examples of NP-Complete problems:
- Boolean satisfiability problem (SAT)
- Traveling salesman decision problem
- Vertex cover problem
- Subset sum problem

## Importance

If P = NP, many currently intractable computational problems would become efficiently solvable,
with profound implications for cryptography, optimization, and artificial intelligence.
Most computer scientists believe that P ≠ NP.
-/

namespace Millennium
set_option linter.unusedVariables false
set_option diagnostics true
set_option diagnostics.threshold 7000

open Turing
open Computability

/--
  A language (decision problem) is a predicate on strings.
  We'll encode this as a predicate on a type with a finite encoding.

  In computational complexity theory, decision problems are typically
  formulated as languages - sets of strings that satisfy a certain property.

  Examples:
  - SAT: The set of all satisfiable Boolean formulas
  - PRIME: The set of all prime numbers (encoded as strings)
  - HAMPATH: The set of all graphs containing a Hamiltonian path
-/
def Language (α : Type) [Primcodable α] := α → Prop

/--
  The class P consists of languages decidable in polynomial time
  by a deterministic Turing machine.

  A language is in P if there exists a polynomial-time algorithm
  that can determine whether a given input belongs to the language.

  Examples in P:
  - Checking if a number is prime (AKS algorithm)
  - Finding shortest paths in a graph (Dijkstra's algorithm)
  - Linear programming
  - 2-SAT (2-variable per clause satisfiability)
-/
def InP {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (comp : TM2ComputableInPolyTime ea finEncodingBoolBool f),
    ∀ a, L a ↔ f a = true

private def sumInl? {α β : Type} : Sum α β → Option α
  | Sum.inl a => some a
  | Sum.inr _ => none

private def sumInr? {α β : Type} : Sum α β → Option β
  | Sum.inl _ => none
  | Sum.inr b => some b

private theorem filterMap_sumInl_map_inl {α β : Type} (l : List α) :
    (l.map (Sum.inl : α → Sum α β)).filterMap sumInl? = l := by
  induction l with
  | nil => simp
  | cons a t ih => simp [sumInl?, ih]

private theorem filterMap_sumInl_map_inr {α β : Type} (l : List β) :
    (l.map (Sum.inr : β → Sum α β)).filterMap sumInl? = ([] : List α) := by
  induction l with
  | nil => simp
  | cons b t ih => simp [sumInl?, ih]

private theorem filterMap_sumInr_map_inl {α β : Type} (l : List α) :
    (l.map (Sum.inl : α → Sum α β)).filterMap sumInr? = ([] : List β) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [sumInr?, ih]

private theorem filterMap_sumInr_map_inr {α β : Type} (l : List β) :
    (l.map (Sum.inr : β → Sum α β)).filterMap sumInr? = l := by
  induction l with
  | nil => simp
  | cons b t ih => simp [sumInr?, ih]

@[simp] private theorem filterMap_sumInl_comp_inl {α β : Type} (l : List α) :
    List.filterMap (sumInl? ∘ (Sum.inl : α → Sum α β)) l = l := by
  induction l with
  | nil => simp
  | cons a t ih => simp [sumInl?, ih]

@[simp] private theorem filterMap_sumInl_comp_inr {α β : Type} (l : List β) :
    List.filterMap (sumInl? ∘ (Sum.inr : β → Sum α β)) l = ([] : List α) := by
  induction l with
  | nil => simp
  | cons b t ih => simp [sumInl?, ih]

@[simp] private theorem filterMap_sumInr_comp_inl {α β : Type} (l : List α) :
    List.filterMap (sumInr? ∘ (Sum.inl : α → Sum α β)) l = ([] : List β) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [sumInr?, ih]

@[simp] private theorem filterMap_sumInr_comp_inr {α β : Type} (l : List β) :
    List.filterMap (sumInr? ∘ (Sum.inr : β → Sum α β)) l = l := by
  induction l with
  | nil => simp
  | cons b t ih => simp [sumInr?, ih]

/--
  Create an encoding for pairs based on individual encodings.

  This allows us to encode pairs of objects (α × β) using
  the encodings for individual types α and β.

  The approach:
  1. Combine alphabets using Sum type
  2. Encode pairs by mapping elements through Sum.inl or Sum.inr
  3. Decode by separating elements and using original decoders

  This encoding is crucial for defining verification in NP problems
  where we need to handle both the input and its certificate.
-/
def pairEncoding {α β : Type} [Primcodable α] [Primcodable β]
    (ea : FinEncoding α) (eb : FinEncoding β) : FinEncoding (α × β) :=
  { Γ := Sum ea.Γ eb.Γ, -- Combined alphabet using Sum type

    encode := λ p =>
      (ea.encode p.1).map Sum.inl ++ (eb.encode p.2).map Sum.inr,

    decode := λ l =>
      let a_list := l.filterMap sumInl?
      let b_list := l.filterMap sumInr?
      match ea.decode a_list, eb.decode b_list with
      | some a, some b => some (a, b)
      | _, _ => none,

    decode_encode := by
      rintro ⟨a, b⟩
      simp [List.filterMap_append, ea.decode_encode, eb.decode_encode]
    ΓFin := inferInstance
  }
/--
  For NP, we need to define verifiability with a certificate.
  Certificate type will depend on the problem.

  A language is in NP if membership can be efficiently verified using a certificate.
  Specifically, there must exist:
  1. A certificate type β
  2. A polynomial-time verification relation R
  3. A polynomial bound on the size of certificates

  Examples in NP:
  - Boolean satisfiability (SAT): certificate is a satisfying assignment
  - Traveling salesman problem: certificate is a tour below a given cost
  - Graph coloring: certificate is a valid k-coloring
  - Subset sum: certificate is the subset that sums to the target value
-/
def InNP {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (β : Type) (instβ : Primcodable β) (eb : FinEncoding β) (R : α → β → Prop),
    -- There exists a polynomial bound on certificate size
    ∃ (p : Polynomial ℕ),
      -- We need to define verification in terms of a function on pairs
      (∃ (verifier : α × β → Bool)
          (comp : TM2ComputableInPolyTime (pairEncoding ea eb) finEncodingBoolBool verifier),
        ∀ a b, R a b ↔ verifier (a, b) = true) ∧
      -- For every a in the language, there exists a certificate b
      -- with size bounded by a polynomial in the size of a
      (∀ a, L a ↔ ∃ b, R a b ∧ (eb.encode b).length ≤ Polynomial.eval (ea.encode a).length p)


/--
  NP-Completeness: A language is NP-complete if it's in NP and
  every NP language reduces to it in polynomial time.

  NP-complete problems represent the "hardest" problems in NP.
  If any NP-complete problem can be solved in polynomial time,
  then P = NP.

  Examples of NP-complete problems:
  - Boolean satisfiability (SAT): The first proven NP-complete problem (Cook-Levin theorem)
  - 3-SAT: Boolean satisfiability with 3 literals per clause
  - Hamiltonian circuit problem: Finding a cycle that visits each vertex exactly once
  - Clique problem: Finding a complete subgraph of a given size
  - Vertex cover: Finding a set of vertices that covers all edges
-/
def NPComplete {α : Type} [Primcodable α] (ea : FinEncoding α) (L : Language α) : Prop :=
  InNP ea L ∧
  ∀ (β : Type) [Primcodable β] (eb : FinEncoding β) (L' : Language β),
    InNP eb L' →
    ∃ (f : β → α) (comp : TM2ComputableInPolyTime eb ea f),
      ∀ b, L' b ↔ L (f b)

/--
  The P = NP question asks whether these classes are equal.

  If P = NP, then every problem whose solution can be quickly verified (NP)
  can also be quickly solved (P).

  Implications if P = NP:
  - Many hard optimization problems would become efficiently solvable
  - Modern cryptography (based on computational hardness) would be broken
  - Automated theorem proving would be much more powerful
-/
def PEqualsNP : Prop :=
  ∀ (α : Type) [Primcodable α] (ea : FinEncoding α) (L : Language α),
    InP ea L ↔ InNP ea L

/--
  The P ≠ NP conjecture.

  Most computer scientists believe this statement is true, meaning
  that some problems are fundamentally harder to solve than to verify.

  If P ≠ NP, then:
  - Many optimization problems remain computationally intractable
  - Current cryptographic systems remain secure
  - Creative activity like finding mathematical proofs requires insight
    that cannot be fully automated
-/
def PNotEqualsNP : Prop :=
  ¬PEqualsNP

end Millennium
