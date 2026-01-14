import Mathlib.Tactic.Basic
import Mathlib.Computability.TuringMachine
import Mathlib.Computability.Primrec
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Init.Data.List.Lemmas
import Problems.PvsNP.TM2PolyTimeComp

/-!
# The P vs NP Problem

This file formalizes the P vs NP problem, one of the seven Millennium Prize Problems
established by the Clay Mathematics Institute. It follows Cook's Clay problem description:
`Problems/PvsNP/references/clay/pvsnp.pdf`.

The reference PDF is included in this repo under `Problems/PvsNP/references/clay/`.

Note: the Clay PDF also mentions standard *external* results and examples (e.g. AKS: `PRIME ∈ P`,
Cook–Levin: `SAT` is NP-complete). Those results are not yet formalized here; this file focuses on
the definitions and the Clay statement itself.

## Overview

The P vs NP problem asks whether every language accepted by some nondeterministic algorithm
in polynomial time is also accepted by some deterministic algorithm in polynomial time.

- P refers to polynomial time: problems solvable in polynomial time
- NP refers to nondeterministic polynomial time: equivalently, problems verifiable in polynomial time

## Examples

These are narrative examples from the Clay PDF; they are not currently present as Lean theorems in
this repository.

Examples of problems in P:
- Determining if a number is prime (AKS algorithm)
- Reachability in a directed graph (PATH)

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

open _root_.Turing
open Computability

/--
  A language (decision problem) is a predicate on strings.
  We treat this abstractly as a predicate on some input type `α`, together with a choice
  of finite encoding `ea : FinEncoding α` that plays the role of the input alphabet.

  In computational complexity theory, decision problems are typically
  formulated as languages - sets of strings that satisfy a certain property.

  Examples:
  - SAT: The set of all satisfiable Boolean formulas
  - PRIME: The set of all prime numbers (encoded as strings)
  - HAMPATH: The set of all graphs containing a Hamiltonian path
-/
def Language (α : Type) := α → Prop

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
def InP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
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
def pairEncoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinEncoding (α × β) :=
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
Computable many-one reducibility (Cook, Definition 1).

`L₁ ≤ₘ L₂` if there exists a (total) computable function `f` such that
`x ∈ L₁ ↔ f x ∈ L₂`.
-/
def ManyOneReducible {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) : Prop :=
  ∃ (f : α → β) (comp : TM2Computable ea eb f),
    ∀ a, L₁ a ↔ L₂ (f a)

/--
A (binary) checking relation `R` is *computable* if membership in the associated language
`L_R = { w#y | R(w, y) }` is decidable by a Turing machine (without a time bound).
-/
def ComputableCheckingRelation {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (R : α → β → Prop) : Prop :=
  ∃ (verifier : α × β → Bool) (comp : TM2Computable (pairEncoding ea eb) finEncodingBoolBool verifier),
    ∀ a b, R a b ↔ verifier (a, b) = true

/--
Computably enumerable languages (c.e.): `L` is c.e. iff there is a computable checking relation
`R(x, y)` such that `x ∈ L ↔ ∃y, R(x, y)` (Cook, Section 2).
-/
def ComputablyEnumerable {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (β : Type) (eb : FinEncoding β) (R : α → β → Prop),
    ComputableCheckingRelation ea eb R ∧
      ∀ a, L a ↔ ∃ b, R a b

/--
c.e.-completeness (Cook, Definition 2): `L` is c.e.-complete if `L` is c.e. and every c.e.
language many-one reduces to `L`.
-/
def CEComplete {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ComputablyEnumerable ea L ∧
    ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
      ComputablyEnumerable eb L' → ManyOneReducible eb ea L' L

/--
A checking relation `R` is *polynomial-time* if the associated language
`L_R = { w#y | R(w, y) }` is in `P` (Cook's Clay problem description).

We model the separator `#` using `pairEncoding`: the string `w#y` is represented by the
concatenation of the left-tagged encoding of `w` and the right-tagged encoding of `y`.
-/
def PolyTimeCheckingRelation {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (R : α → β → Prop) : Prop :=
  InP (pairEncoding ea eb) (fun p => R p.1 p.2)

/--
`NP` (Cook): A language `L` is in `NP` if there exist `k ∈ ℕ` and a polynomial-time checking
relation `R` such that for all inputs `w`,

`w ∈ L ↔ ∃ y (|y| ≤ |w|^k ∧ R(w, y))`.

Here `|w|` and `|y|` are measured as the lengths of `ea.encode w` and `eb.encode y`.
-/
def InNP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (β : Type) (eb : FinEncoding β) (R : α → β → Prop) (k : ℕ),
    PolyTimeCheckingRelation ea eb R ∧
      ∀ a, L a ↔ ∃ b, (eb.encode b).length ≤ (ea.encode a).length ^ k ∧ R a b

/--
Polynomial-time many-one reducibility (Cook, Definition 3).

`L₁ ≤ₚ L₂` if there is a polynomial-time computable function `f` such that
`x ∈ L₁ ↔ f x ∈ L₂`.
-/
def PolyTimeReducible {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) : Prop :=
  ∃ (f : α → β) (comp : TM2ComputableInPolyTime ea eb f),
    ∀ a, L₁ a ↔ L₂ (f a)


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
def NPComplete {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  InNP ea L ∧
    ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
      InNP eb L' → PolyTimeReducible eb ea L' L

/--
Cook, Proposition 1(a): If `L₁ ≤ₚ L₂` and `L₂ ∈ P`, then `L₁ ∈ P`.
-/
theorem Proposition1a {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) :
    PolyTimeReducible ea eb L₁ L₂ → InP eb L₂ → InP ea L₁ := by
  intro hRed hP
  rcases hRed with ⟨f, hfComp, hf⟩
  rcases hP with ⟨g, hgComp, hg⟩
  classical
  rcases _root_.Millennium.Turing.TM2ComputableInPolyTime.comp hfComp hgComp with ⟨hComp⟩
  refine ⟨g ∘ f, hComp, ?_⟩
  intro a
  simpa [Function.comp] using (hf a).trans (hg (f a))

/--
Transitivity of polynomial-time many-one reducibility.

This is Cook's reducibility notion (`≤ₚ`) and uses the proved composition theorem
`TM2ComputableInPolyTime.comp` from `Problems/PvsNP/TM2PolyTimeComp.lean`.
-/
theorem PolyTimeReducible.trans {α β γ : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (ec : FinEncoding γ) (L₁ : Language α) (L₂ : Language β) (L₃ : Language γ) :
    PolyTimeReducible ea eb L₁ L₂ → PolyTimeReducible eb ec L₂ L₃ → PolyTimeReducible ea ec L₁ L₃ := by
  intro h12 h23
  rcases h12 with ⟨f, hfComp, hf⟩
  rcases h23 with ⟨g, hgComp, hg⟩
  classical
  rcases _root_.Millennium.Turing.TM2ComputableInPolyTime.comp hfComp hgComp with ⟨hComp⟩
  refine ⟨g ∘ f, hComp, ?_⟩
  intro a
  simpa [Function.comp] using (hf a).trans (hg (f a))

/--
Cook, Proposition 1(b): If `L₁` is NP-complete, `L₂ ∈ NP`, and `L₁ ≤ₚ L₂`, then `L₂` is
NP-complete.
-/
theorem Proposition1b {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) :
    NPComplete ea L₁ → InNP eb L₂ → PolyTimeReducible ea eb L₁ L₂ → NPComplete eb L₂ := by
  intro hL₁complete hL₂np hL₁L₂
  refine ⟨hL₂np, ?_⟩
  intro γ ec L₃ hL₃np
  have hL₃L₁ : PolyTimeReducible ec ea L₃ L₁ :=
    hL₁complete.2 ec L₃ hL₃np
  exact PolyTimeReducible.trans ec ea eb L₃ L₁ L₂ hL₃L₁ hL₁L₂

/--
Trivial “string” encoding for `List alphabet` when `alphabet` is finite.

This is the identity encoding (`encode = id`, `decode = some`) and is used to express the Clay
statement for languages over finite alphabets.
-/
def finEncodingString (alphabet : Type) [Fintype alphabet] : FinEncoding (List alphabet) :=
  { Γ := alphabet
    encode := id
    decode := fun l => some l
    decode_encode := by intro l; rfl
    ΓFin := inferInstance }

/--
  The P = NP question, stated in the form used in Cook's Clay problem description:
  does every language in NP also belong to P?

  Implications if P = NP:
  - Many hard optimization problems would become efficiently solvable
  - Modern cryptography (based on computational hardness) would be broken
  - Automated theorem proving would be much more powerful
-/
def PEqualsNP : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InNP (finEncodingString alphabet) L → InP (finEncodingString alphabet) L

/--
Cook, Proposition 1(c): If `L` is NP-complete and `L ∈ P`, then `P = NP`.

Here we phrase `P = NP` as `PEqualsNP`, i.e. the Clay problem statement for languages over
finite alphabets with at least two elements.
-/
theorem Proposition1c (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    NPComplete (finEncodingString alphabet) L → InP (finEncodingString alphabet) L → PEqualsNP := by
  intro hComplete hP alphabet' _ _ L' hNP'
  have hRed : PolyTimeReducible (finEncodingString alphabet') (finEncodingString alphabet) L' L :=
    hComplete.2 (finEncodingString alphabet') L' hNP'
  exact Proposition1a (finEncodingString alphabet') (finEncodingString alphabet) L' L hRed hP

/-- An NP-complete language is, in particular, in NP. -/
theorem NPComplete.inNP {α : Type} {ea : FinEncoding α} {L : Language α} :
    NPComplete ea L → InNP ea L :=
  fun h => h.1

/--
If `L` is NP-complete and `L' ∈ NP`, then `L'` polynomial-time reduces to `L`.

This just unwraps the second field of `NPComplete`.
-/
theorem NPComplete.polyTimeReducible_of_inNP {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {L : Language α} {L' : Language β} :
    NPComplete ea L → InNP eb L' → PolyTimeReducible eb ea L' L := by
  intro h hL'
  exact h.2 eb L' hL'

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

/-- `PNotEqualsNP` is definitionaly `¬PEqualsNP`. -/
theorem PNotEqualsNP_iff : PNotEqualsNP ↔ ¬PEqualsNP :=
  Iff.rfl

end Millennium
