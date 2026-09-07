import Mathlib.Tactic.Basic
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Init.Data.List.Lemmas

/-!
# The P vs NP Problem

This file formalizes the P vs NP problem, one of the seven Millennium Prize Problems
established by the Clay Mathematics Institute. It follows Cook's Clay problem description:
`Problems/PVersusNP/references/clay/pvsnp.pdf`.

The reference PDF is included in this repo under `Problems/PVersusNP/references/clay/`.

Note: the Clay PDF also mentions standard results and examples (e.g. AKS: `PRIME ∈ P`,
Cook–Levin: `SAT` is NP-complete). Those results belong to a larger complexity-theory library;
this file focuses on the definitions and the Clay statement itself.

## Overview

The P vs NP problem asks whether every language accepted by some nondeterministic algorithm
in polynomial time is also accepted by some deterministic algorithm in polynomial time.

- P refers to polynomial time: problems solvable in polynomial time
- NP refers to nondeterministic polynomial time: equivalently, problems verifiable in polynomial time

## Examples

These are examples from the Clay PDF, listed here as mathematical context.

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

open _root_.Turing
open Computability

/--
  A language (decision problem) is a predicate on strings.
  We treat this as a predicate on some input type `α`, together with a choice
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
def InPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : TM2ComputableInPolyTime ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

/-! ## Pair encodings with an explicit separator -/

/-- Alphabet for Cook-style pair strings: left symbols, one separator, and right symbols. -/
@[reducible] private def pair_symbol {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : Type :=
  Sum ea.Γ (Option eb.Γ)

/-- Parse the right side of a `w#y` encoding, accepting only right-tagged symbols. -/
private def parse_pair_right {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β} :
    List (pair_symbol ea eb) → Option (List eb.Γ)
  | [] => some []
  | Sum.inr (some b) :: rest =>
      match parse_pair_right rest with
      | some bs => some (b :: bs)
      | none => none
  | _ => none

/-- Parse a full canonical pair string into its left and right symbol blocks. -/
private def parse_pair {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β} :
    List (pair_symbol ea eb) → Option (List ea.Γ × List eb.Γ)
  | [] => none
  | Sum.inl a :: rest =>
      match parse_pair rest with
      | some (as, bs) => some (a :: as, bs)
      | none => none
  | Sum.inr none :: rest =>
      match parse_pair_right rest with
      | some bs => some ([], bs)
      | none => none
  | Sum.inr (some _) :: _ => none

/-- Parsing an encoded right block returns the original right-symbol list. -/
private theorem parse_pair_right_encode {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    (l : List eb.Γ) :
    parse_pair_right (ea := ea) (eb := eb) (l.map (fun b => Sum.inr (some b))) = some l := by
  induction l with
  | nil => simp [parse_pair_right]
  | cons b t ih => simp [parse_pair_right, ih]

/-- Parsing a canonical `left#right` symbol list returns both component symbol lists. -/
private theorem parse_pair_encode {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    (l : List ea.Γ) (r : List eb.Γ) :
    parse_pair (ea := ea) (eb := eb)
      (l.map Sum.inl ++ Sum.inr none :: r.map (fun b => Sum.inr (some b))) = some (l, r) := by
  induction l with
  | nil => simp [parse_pair, parse_pair_right_encode]
  | cons a t ih => simp [parse_pair, ih]

/--
  Create an encoding for pairs based on individual encodings.

  This allows us to encode pairs of objects (α × β) using
  the encodings for individual types α and β.

  The approach:
  1. Combine alphabets using a left alphabet, a distinguished separator, and a right alphabet
  2. Encode pairs in Cook's `w#y` form: left-coded input, separator, right-coded certificate
  3. Decode by parsing exactly a left block, one separator, and a right block, then using the
     original decoders

  This encoding is crucial for defining verification in NP problems
  where we need to handle both the input and its certificate.
-/
def pair_encoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinEncoding (α × β) :=
  { Γ := pair_symbol ea eb,

    encode := λ p =>
      (ea.encode p.1).map Sum.inl ++
        Sum.inr none :: (eb.encode p.2).map (fun b => Sum.inr (some b)),

    decode := λ l =>
      match parse_pair l with
      | some (a_list, b_list) =>
        match ea.decode a_list, eb.decode b_list with
        | some a, some b => some (a, b)
        | _, _ => none
      | none => none

    decode_encode := by
      rintro ⟨a, b⟩
      simp [parse_pair_encode, ea.decode_encode, eb.decode_encode]
    ΓFin := inferInstance
  }

/-- Canonical pair encodings have the Cook form `w#y`. -/
theorem pair_encoding.encode_eq {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (p : α × β) :
    (pair_encoding ea eb).encode p =
      (ea.encode p.1).map Sum.inl ++
        Sum.inr none :: (eb.encode p.2).map (fun b => Sum.inr (some b)) :=
  rfl

/-- Length of the canonical `w#y` encoding. -/
theorem pair_encoding.length_eq {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (p : α × β) :
    ((pair_encoding ea eb).encode p).length =
      (ea.encode p.1).length + 1 + (eb.encode p.2).length := by
  change (((ea.encode p.1).map (Sum.inl : ea.Γ → pair_symbol ea eb)) ++
      (Sum.inr none :: (eb.encode p.2).map (fun b => Sum.inr (some b)))).length =
    (ea.encode p.1).length + 1 + (eb.encode p.2).length
  simp only [List.length_append, List.length_map, List.length_cons]
  omega

/--
Computable many-one reducibility (Cook, Definition 1).

`L₁ ≤ₘ L₂` if there exists a (total) computable function `f` such that
`x ∈ L₁ ↔ f x ∈ L₂`.
-/
def ManyOneReducible {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) : Prop :=
  ∃ (f : α → β) (_comp : TM2Computable ea.encode eb.encode f),
    ∀ a, L₁ a ↔ L₂ (f a)

/--
Trivial “string” encoding for `List alphabet` when `alphabet` is finite.

This is the identity encoding (`encode = id`, `decode = some`).  It is used both for the input
strings `Σ*` of the Clay statement and for the certificate strings `Γ₁*` in the definitions of
`NP` and of computably enumerable languages: certificates are *all* finite strings over a finite
alphabet, exactly as in Cook's write-up, and not elements of an arbitrary encoded type.
-/
def fin_encoding_string (alphabet : Type) [Fintype alphabet] : FinEncoding (List alphabet) :=
  { Γ := alphabet
    encode := id
    decode := fun l => some l
    decode_encode := by intro l; rfl
    ΓFin := inferInstance }

@[simp] theorem fin_encoding_string_encode (alphabet : Type) [Fintype alphabet]
    (w : List alphabet) : (fin_encoding_string alphabet).encode w = w :=
  rfl

/--
A (binary) checking relation `R` is *computable* if membership in the associated language
`L_R = { w#y | R(w, y) }` is decidable by a Turing machine (without a time bound).
-/
def ComputableCheckingRelation {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (R : α → β → Prop) : Prop :=
  ∃ (verifier : α × β → Bool)
    (_comp : TM2Computable (pair_encoding ea eb).encode finEncodingBoolBool.encode verifier),
    ∀ a b, R a b ↔ verifier (a, b) = true

/--
Computably enumerable languages (c.e.): `L` is c.e. iff there is a computable checking relation
`R(x, y)` such that `x ∈ L ↔ ∃y, R(x, y)` (Cook, Section 2).

The certificates `y` range over *all* finite strings over some finite alphabet `Γ₁` (identity
encoding `fin_encoding_string Γ₁`), so the checking machine must be correct on every pair
`x # y`.  Quantifying over an arbitrary encoded certificate type instead would let the
certificate type itself carry the membership information and make every language c.e.
-/
def ComputablyEnumerable {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop),
    ComputableCheckingRelation ea (fin_encoding_string Γ₁) R ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, R a y

/--
c.e.-completeness (Cook, Definition 2): `L` is c.e.-complete if `L` is c.e. and every c.e.
language many-one reduces to `L`.
-/
def ComputablyEnumerableComplete {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ComputablyEnumerable ea L ∧
    ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
      ComputablyEnumerable eb L' → ManyOneReducible eb ea L' L

/--
A checking relation `R` is *polynomial-time* if the associated language
`L_R = { w#y | R(w, y) }` is in `P` (Cook's Clay problem description).

We model the separator `#` using `pair_encoding`: canonical strings are represented by the
left-tagged encoding of `w`, followed by a distinguished separator symbol, followed by the
right-tagged encoding of `y`.
-/
def PolynomialTimeCheckingRelation {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (R : α → β → Prop) : Prop :=
  InPolynomialTime (pair_encoding ea eb) (fun p => R p.1 p.2)

/--
`NP` (Cook): A language `L` is in `NP` if there exist a finite certificate alphabet `Γ₁`, an
exponent `k ∈ ℕ`, and a polynomial-time checking relation `R ⊆ α × Γ₁*` such that for all inputs
`w`,

`w ∈ L ↔ ∃ y ∈ Γ₁* (|y| ≤ |w|^k ∧ R(w, y))`.

Here `|w|` is the length of `ea.encode w` and `|y|` is the length of the certificate string `y`.
Certificates are all finite strings over `Γ₁` with the identity encoding `fin_encoding_string Γ₁`,
so `L_R = { w#y | R(w, y) } ∈ P` is required over *all* certificate strings, as in Cook's
definition.  (An earlier version quantified over an arbitrary encoded certificate type `β`; that
let the type `β` itself encode membership in `L` and put every language into `NP`.)
-/
def InNondeterministicPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    PolynomialTimeCheckingRelation ea (fin_encoding_string Γ₁) R ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y

/--
Polynomial-time many-one reducibility (Cook, Definition 3).

`L₁ ≤ₚ L₂` if there is a polynomial-time computable function `f` such that
`x ∈ L₁ ↔ f x ∈ L₂`.
-/
def PolynomialTimeReducible {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) : Prop :=
  ∃ (f : α → β) (_comp : TM2ComputableInPolyTime ea.encode eb.encode f),
    ∀ a, L₁ a ↔ L₂ (f a)

/--
Closure of the polynomial-time two-stack Turing-machine computability predicate under composition.

The Cook proposition lemmas below take this machine-model closure principle as an explicit
hypothesis.
-/
def ClayPVersusNP.Support.PolynomialTimeComputableComposition : Prop :=
  ∀ {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β} {eγ : FinEncoding γ}
    {f : α → β} {g : β → γ},
    TM2ComputableInPolyTime eα.encode eβ.encode f →
    TM2ComputableInPolyTime eβ.encode eγ.encode g →
    Nonempty (TM2ComputableInPolyTime eα.encode eγ.encode (g ∘ f))


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
def NondeterministicPolynomialTimeComplete {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  InNondeterministicPolynomialTime ea L ∧
    ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
      InNondeterministicPolynomialTime eb L' → PolynomialTimeReducible eb ea L' L

/--
Cook, Proposition 1(a): If `L₁ ≤ₚ L₂` and `L₂ ∈ P`, then `L₁ ∈ P`.
-/
theorem PolynomialTimeReducible.source_in_p
    {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) :
    ClayPVersusNP.Support.PolynomialTimeComputableComposition → PolynomialTimeReducible ea eb L₁ L₂ → InPolynomialTime eb L₂ → InPolynomialTime ea L₁ := by
  intro hComp hRed hP
  rcases hRed with ⟨f, hfComp, hf⟩
  rcases hP with ⟨g, hgComp, hg⟩
  classical
  rcases hComp hfComp hgComp with ⟨hgfComp⟩
  refine ⟨g ∘ f, hgfComp, ?_⟩
  intro a
  simpa [Function.comp] using (hf a).trans (hg (f a))

/--
Transitivity of polynomial-time many-one reducibility.

This is Cook's reducibility notion (`≤ₚ`). It is conditional on polynomial-time two-stack
Turing-machine computability being closed under composition.
-/
theorem PolynomialTimeReducible.trans {α β γ : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (ec : FinEncoding γ) (L₁ : Language α) (L₂ : Language β) (L₃ : Language γ) :
    ClayPVersusNP.Support.PolynomialTimeComputableComposition →
    PolynomialTimeReducible ea eb L₁ L₂ → PolynomialTimeReducible eb ec L₂ L₃ → PolynomialTimeReducible ea ec L₁ L₃ := by
  intro hComp h12 h23
  rcases h12 with ⟨f, hfComp, hf⟩
  rcases h23 with ⟨g, hgComp, hg⟩
  classical
  rcases hComp hfComp hgComp with ⟨hgfComp⟩
  refine ⟨g ∘ f, hgfComp, ?_⟩
  intro a
  simpa [Function.comp] using (hf a).trans (hg (f a))

/--
Cook, Proposition 1(b): If `L₁` is NP-complete, `L₂ ∈ NP`, and `L₁ ≤ₚ L₂`, then `L₂` is
NP-complete.
-/
theorem NondeterministicPolynomialTimeComplete.transfer
    {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) :
    ClayPVersusNP.Support.PolynomialTimeComputableComposition →
    NondeterministicPolynomialTimeComplete ea L₁ → InNondeterministicPolynomialTime eb L₂ → PolynomialTimeReducible ea eb L₁ L₂ → NondeterministicPolynomialTimeComplete eb L₂ := by
  intro hComp hL₁complete hL₂np hL₁L₂
  refine ⟨hL₂np, ?_⟩
  intro γ ec L₃ hL₃np
  have hL₃L₁ : PolynomialTimeReducible ec ea L₃ L₁ :=
    hL₁complete.2 ec L₃ hL₃np
  exact PolynomialTimeReducible.trans ec ea eb L₃ L₁ L₂ hComp hL₃L₁ hL₁L₂

/--
Cook's Clay verifier data for one language over a finite string alphabet.

This packages the PDF sentence:
`w ∈ L ⇔ ∃ y ∈ Γ₁*, |y| ≤ |w|^k` and a polynomial-time checking relation `R(w,y)`,
where `Γ₁` is the finite certificate alphabet `certificate_alphabet` and certificates are all
finite strings over it.
-/
structure ClayPolynomialTimeVerification
    (alphabet : Type) [Fintype alphabet] (L : Language (List alphabet)) where
  /-- Cook's finite certificate alphabet `Γ₁`. -/
  certificate_alphabet : Type
  [certificate_alphabet_fintype : Fintype certificate_alphabet]
  /-- The checking relation `R ⊆ Σ* × Γ₁*`. -/
  checking_relation : List alphabet → List certificate_alphabet → Prop
  /-- The exponent `k` in the certificate length bound `|y| ≤ |w|^k`. -/
  exponent : ℕ
  /-- `L_R = { w#y | R(w, y) }` is in `P`, over all strings `w ∈ Σ*` and `y ∈ Γ₁*`. -/
  checking_relation_in_polynomial_time :
    PolynomialTimeCheckingRelation (fin_encoding_string alphabet)
      (fin_encoding_string certificate_alphabet) checking_relation
  /-- Cook's membership condition `w ∈ L ⇔ ∃ y (|y| ≤ |w|^k ∧ R(w, y))`. -/
  membership_iff_exists_bounded_certificate :
    ∀ w : List alphabet,
      L w ↔ ∃ y : List certificate_alphabet,
        y.length ≤ w.length ^ exponent ∧ checking_relation w y

attribute [instance] ClayPolynomialTimeVerification.certificate_alphabet_fintype

/-- Clay's polynomial-time-verification wording for `L ∈ NP`. -/
def ClayVerifiableLanguage
    (alphabet : Type) [Fintype alphabet] (L : Language (List alphabet)) : Prop :=
  Nonempty (ClayPolynomialTimeVerification alphabet L)

/-- The Clay verifier wording is exactly the repository's `NP` definition. -/
theorem ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time
    (alphabet : Type) [Fintype alphabet] (L : Language (List alphabet)) :
    ClayVerifiableLanguage alphabet L ↔
      InNondeterministicPolynomialTime (fin_encoding_string alphabet) L := by
  constructor
  · rintro ⟨witness⟩
    exact
      ⟨witness.certificate_alphabet, witness.certificate_alphabet_fintype,
        witness.checking_relation, witness.exponent,
        witness.checking_relation_in_polynomial_time,
        witness.membership_iff_exists_bounded_certificate⟩
  · rintro ⟨Γ₁, _, R, k, hR, hmem⟩
    exact
      ⟨{ certificate_alphabet := Γ₁
         checking_relation := R
         exponent := k
         checking_relation_in_polynomial_time := hR
         membership_iff_exists_bounded_certificate := hmem }⟩

/--
Cook's Clay alphabet hypothesis: `Σ` is a finite alphabet with at least two symbols, and `Σ*` is
the type of finite strings over it.
-/
structure ClayFiniteAlphabet where
  carrier : Type
  [fintype : Fintype carrier]
  [nontrivial : Nontrivial carrier]

attribute [instance] ClayFiniteAlphabet.fintype
attribute [instance] ClayFiniteAlphabet.nontrivial

namespace ClayFiniteAlphabet

/-- The string type `Σ*` for a fixed finite alphabet. -/
def Strings (A : ClayFiniteAlphabet) : Type :=
  List A.carrier

/-- Languages over `Σ*`, matching Cook's “subset `L` of `Σ*`” wording. -/
def Language (A : ClayFiniteAlphabet) : Type :=
  Millennium.Language A.Strings

/-- Fixed-alphabet Clay verifier wording for `L ∈ NP`. -/
def VerifiableLanguage (A : ClayFiniteAlphabet) (L : A.Language) : Prop :=
  ClayVerifiableLanguage A.carrier L

/-- The fixed-alphabet verifier wording is exactly `L ∈ NP`. -/
theorem VerifiableLanguage.iff_in_nondeterministic_polynomial_time
    (A : ClayFiniteAlphabet) (L : A.Language) :
    A.VerifiableLanguage L ↔ InNondeterministicPolynomialTime (fin_encoding_string A.carrier) L :=
  ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time A.carrier L

/-- Fixed-alphabet form of `P = NP` for languages over `Σ*`. -/
def PolynomialTimeEqualsNondeterministicPolynomialTime (A : ClayFiniteAlphabet) : Prop :=
  ∀ L : A.Language,
    InPolynomialTime (fin_encoding_string A.carrier) L ↔ InNondeterministicPolynomialTime (fin_encoding_string A.carrier) L

/-- Fixed-alphabet hard direction: every `NP` language over `Σ*` is in `P`. -/
def NondeterministicPolynomialTimeContainedInPolynomialTime (A : ClayFiniteAlphabet) : Prop :=
  ∀ L : A.Language,
    InNondeterministicPolynomialTime (fin_encoding_string A.carrier) L → InPolynomialTime (fin_encoding_string A.carrier) L

end ClayFiniteAlphabet

/-- Length of the canonical finite-string `w#y` encoding. -/
theorem string_pair_encoding.length_eq (alphabet : Type) [Fintype alphabet]
    (p : List alphabet × List alphabet) :
    ((pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode p).length =
      p.1.length + 1 + p.2.length := by
  simp [pair_encoding.length_eq, fin_encoding_string]

/-! ## Concrete two-stack Turing-machine program for finite-string pair projection -/

/-- Stack identifiers for the projection machine: input, output, and temporary work. -/
private inductive StringProjectionStack where
  | input | output | work
  deriving DecidableEq, Fintype

/-- Control labels for the phases of the projection machine. -/
private inductive StringProjectionLabel where
  | copy | emit_work | discard_right | drain | emit_output | done
  deriving DecidableEq, Fintype

/-- Stack alphabets for the left-projection machine: pair input, plain output, and work symbols. -/
private def string_projection_alphabet (alphabet : Type) [Fintype alphabet] :
    StringProjectionStack → Type
  | StringProjectionStack.input =>
      pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)
  | StringProjectionStack.output => alphabet
  | StringProjectionStack.work => alphabet

/-- Finite control state stores the last popped input/work symbol, if any. -/
@[reducible] private def StringProjectionState (alphabet : Type) [Fintype alphabet] : Type :=
  Option (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet))

/-- Arbitrary fallback alphabet symbol used only on unreachable malformed states. -/
private noncomputable def default_string_symbol (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] : alphabet :=
  Classical.choice inferInstance

/-- Convert the stored state symbol into the plain alphabet symbol to push. -/
private noncomputable def string_projection_state_symbol {alphabet : Type} [Fintype alphabet]
    [Nontrivial alphabet] (s : StringProjectionState alphabet) : alphabet :=
  match s with
  | some (Sum.inl a) => a
  | _ => default_string_symbol alphabet

/-- Next label after popping from the input while copying the left block. -/
private def string_projection_input_label {alphabet : Type} [Fintype alphabet]
    (s : StringProjectionState alphabet) : StringProjectionLabel :=
  match s with
  | some (Sum.inl _) => StringProjectionLabel.emit_work
  | some (Sum.inr none) => StringProjectionLabel.discard_right
  | _ => StringProjectionLabel.done

/-- Next label while discarding the right block after the separator has been seen. -/
private def string_projection_discard_label {alphabet : Type} [Fintype alphabet]
    (s : StringProjectionState alphabet) : StringProjectionLabel :=
  match s with
  | some _ => StringProjectionLabel.discard_right
  | none => StringProjectionLabel.drain

/-- Next label after popping from the work stack while draining copied left symbols. -/
private def string_projection_work_label {alphabet : Type} [Fintype alphabet]
    (s : StringProjectionState alphabet) : StringProjectionLabel :=
  match s with
  | some (Sum.inl _) => StringProjectionLabel.emit_output
  | _ => StringProjectionLabel.done

/-- Store the last input-stack pop in the finite control state. -/
private def string_projection_set_input_state {alphabet : Type} [Fintype alphabet]
    (_s : StringProjectionState alphabet)
    (x : Option (string_projection_alphabet alphabet StringProjectionStack.input)) :
    StringProjectionState alphabet :=
  x

/-- Store the last work-stack pop as a left-tagged state symbol. -/
private def string_projection_set_work_state {alphabet : Type} [Fintype alphabet]
    (_s : StringProjectionState alphabet)
    (x : Option (string_projection_alphabet alphabet StringProjectionStack.work)) :
    StringProjectionState alphabet :=
  x.map (fun a => Sum.inl a)

/-- Transition table for the concrete stack machine computing `(w, y) ↦ w`. -/
private noncomputable def left_projection_table (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] :
    StringProjectionLabel →
      Turing.TM2.Stmt (string_projection_alphabet alphabet) StringProjectionLabel
        (StringProjectionState alphabet)
  | StringProjectionLabel.copy =>
      Turing.TM2.Stmt.pop StringProjectionStack.input string_projection_set_input_state
        (Turing.TM2.Stmt.goto string_projection_input_label)
  | StringProjectionLabel.emit_work =>
      Turing.TM2.Stmt.push StringProjectionStack.work string_projection_state_symbol
        (Turing.TM2.Stmt.goto (fun _ => StringProjectionLabel.copy))
  | StringProjectionLabel.discard_right =>
      Turing.TM2.Stmt.pop StringProjectionStack.input string_projection_set_input_state
        (Turing.TM2.Stmt.goto string_projection_discard_label)
  | StringProjectionLabel.drain =>
      Turing.TM2.Stmt.pop StringProjectionStack.work string_projection_set_work_state
        (Turing.TM2.Stmt.goto string_projection_work_label)
  | StringProjectionLabel.emit_output =>
      Turing.TM2.Stmt.push StringProjectionStack.output string_projection_state_symbol
        (Turing.TM2.Stmt.goto (fun _ => StringProjectionLabel.drain))
  | StringProjectionLabel.done =>
      Turing.TM2.Stmt.halt

/--
A concrete two-stack program for projecting the left string from canonical `w#y` inputs.

The program copies the left block onto a work stack until it reads the separator, discards the
right block so the input stack is empty at halt, then drains the work stack to the output stack.
This reverses twice, so the output order is the original left string.
-/
private noncomputable def left_projection_machine (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] : FinTM2 where
  K := StringProjectionStack
  kFin := inferInstance
  k₀ := StringProjectionStack.input
  k₁ := StringProjectionStack.output
  Γ := string_projection_alphabet alphabet
  Λ := StringProjectionLabel
  main := StringProjectionLabel.copy
  ΛFin := inferInstance
  σ := StringProjectionState alphabet
  initialState := none
  σFin := by
    dsimp [StringProjectionState, pair_symbol]
    infer_instance
  Γk₀Fin := by
    dsimp [string_projection_alphabet, pair_symbol]
    infer_instance
  m := left_projection_table alphabet

/-- Convenient explicit configuration constructor for the projection machine. -/
private def string_projection_cfg (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (label : StringProjectionLabel) (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) : (left_projection_machine alphabet).Cfg where
  l := some label
  var := state
  stk
    | StringProjectionStack.input => input
    | StringProjectionStack.output => output
    | StringProjectionStack.work => work

/-- One machine step: a left input symbol is popped and remembered for work-stack emission. -/
private theorem string_projection_step_copy_left (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (a : alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.copy state
          (Sum.inl a :: input) output work) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.emit_work (some (Sum.inl a))
          input output work) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_input_label, string_projection_set_input_state]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: the separator switches the machine from copy mode to discard mode. -/
private theorem string_projection_step_copy_separator (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.copy state
          (Sum.inr none :: input) output work) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.discard_right (some (Sum.inr none))
          input output work) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_input_label, string_projection_set_input_state]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: emit the remembered left symbol onto the work stack. -/
private theorem string_projection_step_emit_work (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (_state : StringProjectionState alphabet)
    (a : alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.emit_work (some (Sum.inl a))
          input output work) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.copy (some (Sum.inl a))
          input output (a :: work)) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_state_symbol]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: discard a right-side input symbol. -/
private theorem string_projection_step_discard_cons (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (next : pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet))
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.discard_right state
          (next :: input) output work) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.discard_right
          (some next) input output work) := by
  cases next <;>
    simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
      string_projection_cfg, string_projection_discard_label, string_projection_set_input_state]
  all_goals
    congr
    ext k
    cases k <;> rfl

/-- One machine step: when the right block is exhausted, start draining the work stack. -/
private theorem string_projection_step_discard_empty (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.discard_right state [] output work) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.drain none [] output work) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_discard_label, string_projection_set_input_state]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: pop a copied left symbol from the work stack. -/
private theorem string_projection_step_drain_cons (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (a : alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.drain state input output (a :: work)) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.emit_output (some (Sum.inl a))
          input output work) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_work_label, string_projection_set_work_state]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: if the work stack is empty, move to the final label. -/
private theorem string_projection_step_drain_empty (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.drain state input output []) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.done none input output []) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_work_label, string_projection_set_work_state]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: emit the remembered work symbol onto the output stack. -/
private theorem string_projection_step_emit_output (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (_state : StringProjectionState alphabet)
    (a : alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.emit_output (some (Sum.inl a))
          input output work) =
      some
        (string_projection_cfg alphabet StringProjectionLabel.drain (some (Sum.inl a))
          input (a :: output) work) := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg, string_projection_state_symbol]
  congr
  ext k
  cases k <;> rfl

/-- One machine step: the final label halts by clearing the label field. -/
private theorem string_projection_step_done (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.done state input output work) =
      some { (string_projection_cfg alphabet StringProjectionLabel.done state input output work) with
        l := none } := by
  simp [Turing.FinTM2.step, left_projection_machine, left_projection_table,
    string_projection_cfg]
  congr

/-- Turn a single `step = some cfg'` equality into a one-step timed evaluation. -/
private noncomputable def string_projection_evals_one_step (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    {cfg cfg' : (left_projection_machine alphabet).Cfg}
    (hstep : (left_projection_machine alphabet).step cfg = some cfg') :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step cfg (some cfg') 1 :=
  { steps := 1
    evals_in_steps := by
      simpa [flip, Option.bind] using hstep
    steps_le_m := le_rfl }

/-- Timed two-step transition copying one left symbol from input to work. -/
private noncomputable def string_projection_evals_copy_left (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (a : alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.copy state
        (Sum.inl a :: input) output work)
      (some
        (string_projection_cfg alphabet StringProjectionLabel.copy (some (Sum.inl a))
          input output (a :: work)))
      2 := by
  let cfg₀ :=
    string_projection_cfg alphabet StringProjectionLabel.copy state
      (Sum.inl a :: input) output work
  let cfg₁ :=
    string_projection_cfg alphabet StringProjectionLabel.emit_work (some (Sum.inl a))
      input output work
  let cfg₂ :=
    string_projection_cfg alphabet StringProjectionLabel.copy (some (Sum.inl a))
      input output (a :: work)
  have h₁ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step cfg₀ (some cfg₁) 1 :=
    string_projection_evals_one_step alphabet
      (string_projection_step_copy_left alphabet state a input output work)
  have h₂ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step cfg₁ (some cfg₂) 1 :=
    string_projection_evals_one_step alphabet
      (string_projection_step_emit_work alphabet (some (Sum.inl a)) a input output work)
  simpa [cfg₀, cfg₁, cfg₂] using
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step 1 1 cfg₀ cfg₁
      (some cfg₂) h₁ h₂

/-- Timed two-step transition moving one work symbol to output. -/
private noncomputable def string_projection_evals_emit_output (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (a : alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.drain state input output (a :: work))
      (some
        (string_projection_cfg alphabet StringProjectionLabel.drain (some (Sum.inl a))
          input (a :: output) work))
      2 := by
  let cfg₀ :=
    string_projection_cfg alphabet StringProjectionLabel.drain state input output (a :: work)
  let cfg₁ :=
    string_projection_cfg alphabet StringProjectionLabel.emit_output (some (Sum.inl a))
      input output work
  let cfg₂ :=
    string_projection_cfg alphabet StringProjectionLabel.drain (some (Sum.inl a))
      input (a :: output) work
  have h₁ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step cfg₀ (some cfg₁) 1 :=
    string_projection_evals_one_step alphabet
      (string_projection_step_drain_cons alphabet state a input output work)
  have h₂ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step cfg₁ (some cfg₂) 1 :=
    string_projection_evals_one_step alphabet
      (string_projection_step_emit_output alphabet (some (Sum.inl a)) a input output work)
  simpa [cfg₀, cfg₁, cfg₂] using
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step 1 1 cfg₀ cfg₁
      (some cfg₂) h₁ h₂

/-- Timed one-step transition consuming the separator and entering right-discard mode. -/
private noncomputable def string_projection_evals_separator (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.copy state
        (Sum.inr none :: input) output work)
      (some
        (string_projection_cfg alphabet StringProjectionLabel.discard_right (some (Sum.inr none))
          input output work))
      1 :=
  string_projection_evals_one_step alphabet
    (string_projection_step_copy_separator alphabet state input output work)

/-- Timed one-step transition discarding one right-side symbol. -/
private noncomputable def string_projection_evals_discard_cons (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (next : pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet))
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.discard_right state
        (next :: input) output work)
      (some
        (string_projection_cfg alphabet StringProjectionLabel.discard_right
          (some next) input output work))
      1 :=
  string_projection_evals_one_step alphabet
    (string_projection_step_discard_cons alphabet state next input output work)

/-- Timed one-step transition from finished right-discarding to work-stack draining. -/
private noncomputable def string_projection_evals_discard_empty (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.discard_right state [] output work)
      (some
        (string_projection_cfg alphabet StringProjectionLabel.drain none [] output work))
      1 :=
  string_projection_evals_one_step alphabet
    (string_projection_step_discard_empty alphabet state output work)

/-- Timed one-step transition from an empty work stack to the final label. -/
private noncomputable def string_projection_evals_drain_empty (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.drain state input output [])
      (some
        (string_projection_cfg alphabet StringProjectionLabel.done none input output []))
      1 :=
  string_projection_evals_one_step alphabet
    (string_projection_step_drain_empty alphabet state input output)

/-- Timed one-step transition from the final label to a halted configuration. -/
private noncomputable def string_projection_evals_done (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.done state input output work)
      (some { (string_projection_cfg alphabet StringProjectionLabel.done state input output work) with
        l := none })
      1 :=
  string_projection_evals_one_step alphabet
    (string_projection_step_done alphabet state input output work)

/-- Control state after copying a whole left block. -/
private def string_projection_copied_state {alphabet : Type} [Fintype alphabet]
    (state : StringProjectionState alphabet) (left : List alphabet) :
    StringProjectionState alphabet :=
  match left with
  | [] => state
  | a :: tail => string_projection_copied_state (some (Sum.inl a)) tail

/-- Control state after discarding a whole right block. -/
private def string_projection_discarded_state {alphabet : Type} [Fintype alphabet]
    (state : StringProjectionState alphabet) (right : List alphabet) :
    StringProjectionState alphabet :=
  match right with
  | [] => state
  | a :: tail => string_projection_discarded_state (some (Sum.inr (some a))) tail

/-- Canonical left-block symbols in the projection machine's input alphabet. -/
private def string_projection_left_symbols (alphabet : Type) [Fintype alphabet]
    (left : List alphabet) :
    List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)) :=
  left.map
    (Sum.inl :
      (fin_encoding_string alphabet).Γ → pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet))

/-- Canonical right-block symbols in the projection machine's input alphabet. -/
private def string_projection_right_symbols (alphabet : Type) [Fintype alphabet]
    (right : List alphabet) :
    List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)) :=
  right.map
    (fun b : (fin_encoding_string alphabet).Γ =>
      (Sum.inr (some b) :
        pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))

/-- Timed run copying an entire left block onto the work stack. -/
private noncomputable def string_projection_evals_copy_left_block
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (left : List alphabet)
    (state : StringProjectionState alphabet)
    (rest : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.copy state
        (left.map
          (Sum.inl :
            (fin_encoding_string alphabet).Γ → pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)) ++
          rest) output work)
      (some
        (string_projection_cfg alphabet StringProjectionLabel.copy
          (string_projection_copied_state state left)
          rest output (left.reverse ++ work)))
      (left.length * 2) := by
  induction left generalizing state work with
  | nil =>
      change StateTransition.EvalsToInTime (left_projection_machine alphabet).step
        (string_projection_cfg alphabet StringProjectionLabel.copy state ([] ++ rest) output work)
        (some
          (string_projection_cfg alphabet StringProjectionLabel.copy (string_projection_copied_state state [])
            rest output ([].reverse ++ work)))
        ([].length * 2)
      rw [List.nil_append]
      simpa [string_projection_copied_state] using
        StateTransition.EvalsToInTime.refl (left_projection_machine alphabet).step
          (string_projection_cfg alphabet StringProjectionLabel.copy state rest output work)
  | cons a tail ih =>
      let cfg₀ :=
        string_projection_cfg alphabet StringProjectionLabel.copy state
          (Sum.inl a :: (tail.map
            (Sum.inl :
              (fin_encoding_string alphabet).Γ → pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)) ++
            rest)) output work
      let cfg₁ :=
        string_projection_cfg alphabet StringProjectionLabel.copy (some (Sum.inl a))
          (tail.map
            (Sum.inl :
              (fin_encoding_string alphabet).Γ → pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)) ++
            rest) output (a :: work)
      let cfg₂ :=
        string_projection_cfg alphabet StringProjectionLabel.copy
          (string_projection_copied_state (some (Sum.inl a)) tail)
          rest output (tail.reverse ++ a :: work)
      have h₁ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
          cfg₀ (some cfg₁) 2 := by
        simpa [cfg₀, cfg₁, fin_encoding_string, List.map_cons, List.cons_append] using
          string_projection_evals_copy_left alphabet state a
            (tail.map
              (Sum.inl :
                (fin_encoding_string alphabet).Γ → pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)) ++
              rest) output work
      have h₂ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
          cfg₁ (some cfg₂) (tail.length * 2) := by
        simpa [cfg₁, cfg₂] using ih (some (Sum.inl a)) (a :: work)
      convert
        StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
          2 (tail.length * 2) cfg₀ cfg₁ (some cfg₂) h₁ h₂
        using 1 <;>
        simp [cfg₀, cfg₂, string_projection_cfg, fin_encoding_string, List.map_cons, List.cons_append,
          List.reverse_cons, List.append_assoc, string_projection_copied_state, Nat.succ_mul,
          Nat.add_comm]
      all_goals
        simp [left_projection_machine]
        try congr

/-- Timed run discarding the entire right block after the separator. -/
private noncomputable def string_projection_evals_discard_right_block
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (right : List alphabet)
    (state : StringProjectionState alphabet)
    (output work : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.discard_right state
        (string_projection_right_symbols alphabet right) output work)
      (some
        (string_projection_cfg alphabet StringProjectionLabel.discard_right
          (string_projection_discarded_state state right)
          [] output work))
      right.length := by
  induction right generalizing state with
  | nil =>
      simpa [string_projection_right_symbols, fin_encoding_string, List.map_nil,
        string_projection_discarded_state] using
        StateTransition.EvalsToInTime.refl (left_projection_machine alphabet).step
          (string_projection_cfg alphabet StringProjectionLabel.discard_right state [] output work)
  | cons a tail ih =>
      let cfg₀ :=
        string_projection_cfg alphabet StringProjectionLabel.discard_right state
          (string_projection_right_symbols alphabet (a :: tail)) output work
      let cfg₁ :=
        string_projection_cfg alphabet StringProjectionLabel.discard_right (some (Sum.inr (some a)))
          (string_projection_right_symbols alphabet tail) output work
      let cfg₂ :=
        string_projection_cfg alphabet StringProjectionLabel.discard_right
          (string_projection_discarded_state (some (Sum.inr (some a))) tail)
          [] output work
      have h₁ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
          cfg₀ (some cfg₁) 1 := by
        simpa [cfg₀, cfg₁, string_projection_right_symbols, fin_encoding_string,
          List.map_cons] using
          string_projection_evals_discard_cons alphabet state (Sum.inr (some a))
            (string_projection_right_symbols alphabet tail) output work
      have h₂ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
          cfg₁ (some cfg₂) tail.length := by
        simpa [cfg₁, cfg₂] using ih (some (Sum.inr (some a)))
      simpa [cfg₀, cfg₁, cfg₂, string_projection_discarded_state,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
          1 tail.length cfg₀ cfg₁ (some cfg₂) h₁ h₂

/-- Timed run draining a whole work block into the output stack. -/
private noncomputable def string_projection_evals_drain_work_block
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (block : List alphabet)
    (state : StringProjectionState alphabet)
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet)))
    (output restWork : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.drain state input output
        (block ++ restWork))
      (some
        (string_projection_cfg alphabet StringProjectionLabel.drain
          (string_projection_copied_state state block)
          input (block.reverse ++ output) restWork))
      (block.length * 2) := by
  induction block generalizing state output with
  | nil =>
      simpa [string_projection_copied_state] using
        StateTransition.EvalsToInTime.refl (left_projection_machine alphabet).step
          (string_projection_cfg alphabet StringProjectionLabel.drain state input output restWork)
  | cons a tail ih =>
      let cfg₀ :=
        string_projection_cfg alphabet StringProjectionLabel.drain state input output
          ((a :: tail) ++ restWork)
      let cfg₁ :=
        string_projection_cfg alphabet StringProjectionLabel.drain (some (Sum.inl a))
          input (a :: output) (tail ++ restWork)
      let cfg₂ :=
        string_projection_cfg alphabet StringProjectionLabel.drain
          (string_projection_copied_state (some (Sum.inl a)) tail)
          input (tail.reverse ++ a :: output) restWork
      have h₁ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
          cfg₀ (some cfg₁) 2 := by
        simpa [cfg₀, cfg₁] using
          string_projection_evals_emit_output alphabet state a input output (tail ++ restWork)
      have h₂ : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
          cfg₁ (some cfg₂) (tail.length * 2) := by
        simpa [cfg₁, cfg₂] using ih (some (Sum.inl a)) (a :: output)
      simpa [cfg₀, cfg₁, cfg₂, string_projection_copied_state, List.reverse_cons,
        List.append_assoc, Nat.succ_mul,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
          2 (tail.length * 2) cfg₀ cfg₁ (some cfg₂) h₁ h₂

/-- Full timed run of the projection machine on a canonical `left#right` input. -/
private noncomputable def string_projection_evals_canonical
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (left right : List alphabet) :
    StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.copy none
        (string_projection_left_symbols alphabet left ++
          Sum.inr none :: string_projection_right_symbols alphabet right)
        [] [])
      (some { (string_projection_cfg alphabet StringProjectionLabel.done none [] left []) with
        l := none })
      (4 * left.length + right.length + 4) := by
  let cfg₀ :=
    string_projection_cfg alphabet StringProjectionLabel.copy none
      (string_projection_left_symbols alphabet left ++
        Sum.inr none :: string_projection_right_symbols alphabet right)
      [] []
  let cfg₁ :=
    string_projection_cfg alphabet StringProjectionLabel.copy
      (string_projection_copied_state none left)
      (Sum.inr none :: string_projection_right_symbols alphabet right) [] left.reverse
  let cfg₂ :=
    string_projection_cfg alphabet StringProjectionLabel.discard_right (some (Sum.inr none))
      (string_projection_right_symbols alphabet right) [] left.reverse
  let cfg₃ :=
    string_projection_cfg alphabet StringProjectionLabel.discard_right
      (string_projection_discarded_state (some (Sum.inr none)) right)
      [] [] left.reverse
  let cfg₄ :=
    string_projection_cfg alphabet StringProjectionLabel.drain none [] [] left.reverse
  let cfg₅ :=
    string_projection_cfg alphabet StringProjectionLabel.drain
      (string_projection_copied_state none left.reverse)
      [] ((left.reverse).reverse ++ []) []
  have hCopy : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      cfg₀ (some cfg₁) (left.length * 2) := by
    simpa [cfg₀, cfg₁, string_projection_left_symbols] using
      string_projection_evals_copy_left_block alphabet left none
        (Sum.inr none :: string_projection_right_symbols alphabet right) [] []
  have hSep : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      cfg₁ (some cfg₂) 1 := by
    simpa [cfg₁, cfg₂] using
      string_projection_evals_separator alphabet (string_projection_copied_state none left)
        (string_projection_right_symbols alphabet right) [] left.reverse
  have hDiscard : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      cfg₂ (some cfg₃) right.length := by
    simpa [cfg₂, cfg₃] using
      string_projection_evals_discard_right_block alphabet right (some (Sum.inr none))
        [] left.reverse
  have hDiscardDone : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      cfg₃ (some cfg₄) 1 := by
    simpa [cfg₃, cfg₄] using
      string_projection_evals_discard_empty alphabet
        (string_projection_discarded_state (some (Sum.inr none)) right) [] left.reverse
  have hDrain : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      cfg₄ (some cfg₅) (left.reverse.length * 2) := by
    simpa [cfg₄, cfg₅] using
      string_projection_evals_drain_work_block alphabet left.reverse none [] [] []
  have hDrainDone : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      cfg₅
      (some (string_projection_cfg alphabet StringProjectionLabel.done none [] left [])) 1 := by
    simpa [cfg₅, List.reverse_reverse] using
      string_projection_evals_drain_empty alphabet
        (string_projection_copied_state none left.reverse) [] left
  have hDone : StateTransition.EvalsToInTime (left_projection_machine alphabet).step
      (string_projection_cfg alphabet StringProjectionLabel.done none [] left [])
      (some { (string_projection_cfg alphabet StringProjectionLabel.done none [] left []) with
        l := none })
      1 :=
    string_projection_evals_done alphabet none [] left []
  have hCopySep :=
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
      (left.length * 2) 1 cfg₀ cfg₁ (some cfg₂) hCopy hSep
  have hThroughDiscard :=
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
      (1 + left.length * 2) right.length cfg₀ cfg₂ (some cfg₃) hCopySep hDiscard
  have hThroughDiscardDone :=
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
      (right.length + (1 + left.length * 2)) 1 cfg₀ cfg₃ (some cfg₄)
      hThroughDiscard hDiscardDone
  have hThroughDrain :=
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
      (1 + (right.length + (1 + left.length * 2))) (left.reverse.length * 2)
      cfg₀ cfg₄ (some cfg₅) hThroughDiscardDone hDrain
  have hThroughDrainDone :=
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
      (left.reverse.length * 2 + (1 + (right.length + (1 + left.length * 2)))) 1
      cfg₀ cfg₅
      (some (string_projection_cfg alphabet StringProjectionLabel.done none [] left []))
      hThroughDrain hDrainDone
  have hAll :=
    StateTransition.EvalsToInTime.trans (left_projection_machine alphabet).step
      (1 + (left.reverse.length * 2 + (1 + (right.length + (1 + left.length * 2))))) 1
      cfg₀ (string_projection_cfg alphabet StringProjectionLabel.done none [] left [])
      (some { (string_projection_cfg alphabet StringProjectionLabel.done none [] left []) with
        l := none })
      hThroughDrainDone hDone
  exact
    { steps := hAll.steps
      evals_in_steps := by
        simpa [cfg₀, List.reverse_reverse] using
          hAll.evals_in_steps
      steps_le_m := by
        exact le_trans hAll.steps_le_m (by
          simp [List.length_reverse]
          omega) }

/-- Mathlib's `initList` agrees with the explicit initial projection configuration. -/
private theorem string_projection_init_list_eq_cfg (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (input : List (pair_symbol (fin_encoding_string alphabet) (fin_encoding_string alphabet))) :
    initList (left_projection_machine alphabet) input =
      string_projection_cfg alphabet StringProjectionLabel.copy none input [] [] := by
  unfold initList string_projection_cfg
  congr
  funext k
  cases k <;> simp [left_projection_machine] <;> rfl

/-- Mathlib's `haltList` agrees with the explicit halted projection configuration. -/
private theorem string_projection_halt_list_eq_cfg (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet]
    (output : List alphabet) :
    haltList (left_projection_machine alphabet) output =
      { (string_projection_cfg alphabet StringProjectionLabel.done none [] output []) with
        l := (none : Option StringProjectionLabel) } := by
  unfold haltList string_projection_cfg
  congr
  funext k
  cases k <;> simp [left_projection_machine] <;> rfl

/-- Canonical-input output correctness derived from the explicit configuration-level run. -/
private noncomputable def string_projection_outputs_canonical
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (left right : List alphabet) :
    TM2OutputsInTime (left_projection_machine alphabet)
      (string_projection_left_symbols alphabet left ++
        Sum.inr none :: string_projection_right_symbols alphabet right)
      (some left)
      (4 * left.length + right.length + 4) := by
  unfold TM2OutputsInTime
  change StateTransition.EvalsToInTime (left_projection_machine alphabet).step
    (initList (left_projection_machine alphabet)
      (string_projection_left_symbols alphabet left ++
        Sum.inr none :: string_projection_right_symbols alphabet right))
    (some (haltList (left_projection_machine alphabet) left))
    (4 * left.length + right.length + 4)
  rw [string_projection_init_list_eq_cfg, string_projection_halt_list_eq_cfg]
  convert string_projection_evals_canonical alphabet left right using 1
  all_goals
    rfl

/-- Identity equivalence between the machine input alphabet and the canonical pair alphabet. -/
@[reducible] private def string_pair_projection_input_equiv (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] :
    (left_projection_machine alphabet).Γ
        (left_projection_machine alphabet).k₀ ≃
      (pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).Γ :=
  Equiv.refl _

/-- Identity equivalence between the machine output alphabet and the string alphabet. -/
@[reducible] private def string_pair_projection_output_equiv (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] :
    (left_projection_machine alphabet).Γ
        (left_projection_machine alphabet).k₁ ≃
      (fin_encoding_string alphabet).Γ :=
  Equiv.refl _

/-- Mapping through the inverse of `Equiv.refl` leaves a list unchanged. -/
private theorem List.map_equiv_refl_symm {α : Type} (xs : List α) :
    List.map (Equiv.refl α).symm xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, ih]
      rfl

/-- The encoded pair input is exactly the canonical left-symbols, separator, and right-symbols. -/
private theorem string_pair_projection_input_encode_eq (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] (p : List alphabet × List alphabet) :
    List.map (string_pair_projection_input_equiv alphabet).invFun
      ((pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode p) =
      string_projection_left_symbols alphabet p.1 ++
        Sum.inr none :: string_projection_right_symbols alphabet p.2 := by
  rw [pair_encoding.encode_eq]
  simp [string_pair_projection_input_equiv, fin_encoding_string, string_projection_left_symbols,
    string_projection_right_symbols]
  exact List.map_equiv_refl_symm _

/-- The encoded left output is exactly the original left string. -/
private theorem string_pair_projection_output_encode_eq (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] (left : List alphabet) :
    List.map (string_pair_projection_output_equiv alphabet).invFun
      ((fin_encoding_string alphabet).encode left) = left := by
  simp [string_pair_projection_output_equiv, fin_encoding_string]
  exact List.map_equiv_refl_symm _

/-- A concrete linear polynomial bound for the finite-string left-projection machine. -/
private noncomputable def left_projection_time : Polynomial ℕ :=
  4 * Polynomial.X + 4

/--
Linear-time correctness statement for `left_projection_machine`.

The machine copies the left block onto a work stack, discards the separator and right block, then
drains the work stack to the output stack.  This fixed linear polynomial gives a concrete
asymptotic bound for the projection primitive.
-/
def LeftProjection.linear_time_correctness_data : Type 1 :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet],
    ∀ p : List alphabet × List alphabet,
      TM2OutputsInTime (left_projection_machine alphabet)
        (List.map (string_pair_projection_input_equiv alphabet).invFun
          ((pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode p))
        (Option.some
          (List.map (string_pair_projection_output_equiv alphabet).invFun
            ((fin_encoding_string alphabet).encode p.1)))
        (left_projection_time.eval
          ((pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode p).length)

/--
The concrete finite-string projection machine satisfies the fixed linear-time correctness
statement on canonical `w#y` inputs.
-/
noncomputable def LeftProjection.linear_time_correctness :
    LeftProjection.linear_time_correctness_data := by
  intro alphabet _ _ p
  let h := string_projection_outputs_canonical alphabet p.1 p.2
  have hInput :
      List.map (string_pair_projection_input_equiv alphabet).invFun
        ((pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode p) =
        string_projection_left_symbols alphabet p.1 ++
          Sum.inr none :: string_projection_right_symbols alphabet p.2 :=
    string_pair_projection_input_encode_eq alphabet p
  have hOutput :
      List.map (string_pair_projection_output_equiv alphabet).invFun
        ((fin_encoding_string alphabet).encode p.1) = p.1 :=
    string_pair_projection_output_encode_eq alphabet p.1
  refine
    { steps := h.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [hInput, hOutput]
    exact h.evals_in_steps
  · exact le_trans h.steps_le_m (by
      simp [left_projection_time, pair_encoding.length_eq, fin_encoding_string]
      omega)

/--
Cook's nontrivial direction of `P = NP`: every finite-alphabet language in `NP` is also in `P`.

The easy inclusion `P ⊆ NP` is proved below from an explicit certificate-ignoring verifier
construction, so this hard direction can be related back to the literal class equality `ClayPVersusNP.Formulations.ClassEquality`.
-/
def ClayPVersusNP.Formulations.HardDirection : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InNondeterministicPolynomialTime (fin_encoding_string alphabet) L → InPolynomialTime (fin_encoding_string alphabet) L

/--
Cook's deterministic-simulation wording: nondeterministic polynomial-time acceptance can be
simulated by deterministic polynomial-time decision.
-/
abbrev ClayPVersusNP.Formulations.DeterministicSimulation : Prop :=
  ClayPVersusNP.Formulations.HardDirection

/-- The deterministic-simulation wording specialized to one fixed finite alphabet. -/
theorem ClayPVersusNP.Formulations.DeterministicSimulation.for_alphabet
    (h : ClayPVersusNP.Formulations.DeterministicSimulation) (A : ClayFiniteAlphabet) :
    A.NondeterministicPolynomialTimeContainedInPolynomialTime :=
  h A.carrier

/--
Clay's informal verification-to-solution wording: every language whose membership has
polynomial-bounded certificates checkable in polynomial time is itself decidable in polynomial time.
-/
def ClayPVersusNP.Formulations.CheckableImpliesSolvable : Prop :=
  ∀ A : ClayFiniteAlphabet, ∀ L : A.Language,
    A.VerifiableLanguage L → InPolynomialTime (fin_encoding_string A.carrier) L

/-- The verification-to-solution wording is exactly the hard direction `NP ⊆ P`. -/
theorem ClayPVersusNP.Formulations.CheckableImpliesSolvable.iff_hard_direction :
    ClayPVersusNP.Formulations.CheckableImpliesSolvable ↔
      ClayPVersusNP.Formulations.HardDirection := by
  constructor
  · intro h alphabet _ _ L hNP
    let A : ClayFiniteAlphabet := { carrier := alphabet }
    have hVer : A.VerifiableLanguage L :=
      (ClayFiniteAlphabet.VerifiableLanguage.iff_in_nondeterministic_polynomial_time A L).2 hNP
    exact h A L hVer
  · intro h A L hVer
    exact h A.carrier L
      ((ClayFiniteAlphabet.VerifiableLanguage.iff_in_nondeterministic_polynomial_time A L).1 hVer)

/--
Cook's nondeterministic-simulation wording and the efficient-verification wording are the same
hard direction, `NP ⊆ P`.
-/
theorem ClayPVersusNP.Formulations.DeterministicSimulation.iff_checkable :
    ClayPVersusNP.Formulations.DeterministicSimulation ↔
      ClayPVersusNP.Formulations.CheckableImpliesSolvable := by
  simpa [ClayPVersusNP.Formulations.DeterministicSimulation,
    ClayPVersusNP.Formulations.HardDirection] using
    ClayPVersusNP.Formulations.CheckableImpliesSolvable.iff_hard_direction.symm

/--
Machine-model closure needed for the easy inclusion `P ⊆ NP`: a polynomial-time decider for `L`
can serve as a polynomial-time verifier whose certificate input is unused.
-/
def ClayPVersusNP.Support.DeciderAsVerifier : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InPolynomialTime (fin_encoding_string alphabet) L →
      PolynomialTimeCheckingRelation (fin_encoding_string alphabet) (fin_encoding_string alphabet)
        (fun a _certificate => L a)

/--
Polynomial-time left projection for the canonical `w#y` pair encoding on finite strings.

This is the concrete machine primitive used in the standard proof that `P ⊆ NP` over the finite
alphabets from Cook's Clay statement: from an encoded pair `(w, y)`, return the input string `w`
in polynomial time.
-/
def LeftProjection.polynomial_time_computable : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet],
    Nonempty
      (TM2ComputableInPolyTime
        (pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode
        (fin_encoding_string alphabet).encode
        (fun p : List alphabet × List alphabet => p.1))

/-- The verified linear-time left-projection machine proves the projection primitive. -/
theorem LeftProjection.polynomial_time_computable.of_linear_time
    (hLinear : LeftProjection.linear_time_correctness_data) :
    LeftProjection.polynomial_time_computable := by
  intro alphabet _ _
  refine ⟨?_⟩
  exact
    { tm := left_projection_machine alphabet
      inputAlphabet := string_pair_projection_input_equiv alphabet
      outputAlphabet := string_pair_projection_output_equiv alphabet
      time := left_projection_time
      outputsFun := hLinear alphabet }

/--
The verifier lift follows from polynomial-time left projection for finite string `w#y` encodings
and closure of polynomial-time computability under composition.
-/
theorem ClayPVersusNP.Support.DeciderAsVerifier.of_projection
    (hProj : LeftProjection.polynomial_time_computable) (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP.Support.DeciderAsVerifier := by
  intro alphabet _ _ L hP
  rcases hP with ⟨decider, hDeciderComp, hDeciderCorrect⟩
  refine ⟨fun p : List alphabet × List alphabet => decider p.1, ?_, ?_⟩
  · let hFstComp := Classical.choice (hProj alphabet)
    let hVerifierComp := Classical.choice (hComp hFstComp hDeciderComp)
    show TM2ComputableInPolyTime
      (pair_encoding (fin_encoding_string alphabet) (fin_encoding_string alphabet)).encode
      (finEncodingBoolBool).encode
      (decider ∘ fun p : List alphabet × List alphabet => p.1)
    exact hVerifierComp
  · intro p
    exact hDeciderCorrect p.1

/--
The verified linear-time left-projection machine leaves only polynomial-time composition closure
as the two-stack Turing-machine infrastructure needed for the decider-as-verifier lift.
-/
theorem ClayPVersusNP.Support.DeciderAsVerifier.of_left_projection_machine
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP.Support.DeciderAsVerifier :=
  ClayPVersusNP.Support.DeciderAsVerifier.of_projection
    (LeftProjection.polynomial_time_computable.of_linear_time
      LeftProjection.linear_time_correctness)
    hComp

/--
The easy direction `P ⊆ NP` for languages over finite alphabets, proved from the corresponding
certificate-ignoring verifier lift for the two-stack Turing-machine model.
-/
theorem PolynomialTimeContainedInNondeterministicPolynomialTime.certificate_verifier :
    ClayPVersusNP.Support.DeciderAsVerifier →
      ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
        InPolynomialTime (fin_encoding_string alphabet) L → InNondeterministicPolynomialTime (fin_encoding_string alphabet) L := by
  intro hLift alphabet _ _ L hP
  refine ⟨alphabet, inferInstance, (fun a _certificate => L a), 0,
    hLift alphabet L hP, ?_⟩
  intro a
  constructor
  · intro hLa
    exact ⟨[], by simp, hLa⟩
  · rintro ⟨_certificate, _hBound, hLa⟩
    exact hLa

/--
The easy inclusion `P ⊆ NP` for finite-string languages, using the verified left-projection
machine above. The only remaining hypothesis is polynomial-time composition closure for the
two-stack Turing-machine model.
-/
theorem PolynomialTimeContainedInNondeterministicPolynomialTime.of_turing_machine_composition
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
      ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
        InPolynomialTime (fin_encoding_string alphabet) L → InNondeterministicPolynomialTime (fin_encoding_string alphabet) L :=
  PolynomialTimeContainedInNondeterministicPolynomialTime.certificate_verifier (ClayPVersusNP.Support.DeciderAsVerifier.of_left_projection_machine hComp)

/--
The literal class-equality formulation of `P = NP` for languages over finite alphabets with at
least two symbols.

This formulation includes both directions; theorem `PolynomialTimeContainedInNondeterministicPolynomialTime.certificate_verifier` proves the
easy direction `P ⊆ NP` from the certificate-ignoring verifier lift.
-/
def ClayPVersusNP.Formulations.ClassEquality : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InPolynomialTime (fin_encoding_string alphabet) L ↔ InNondeterministicPolynomialTime (fin_encoding_string alphabet) L

/--
Stable public name for the checked positive branch of P versus NP.

We intentionally do not define the prize statement as
`ClayPVersusNP.Formulations.ClassEquality ∨ ¬ ClayPVersusNP.Formulations.ClassEquality`: in classical Lean
that proposition is already provable by excluded middle and would not encode the mathematical
challenge.
-/
def ClayPVersusNP : Prop :=
  ClayPVersusNP.Formulations.ClassEquality

/-- The checked positive-branch statement specialized to one fixed finite alphabet. -/
theorem ClayPVersusNP.for_alphabet
    (h : ClayPVersusNP) (A : ClayFiniteAlphabet) :
    A.PolynomialTimeEqualsNondeterministicPolynomialTime :=
  h A.carrier

/--
The literal equality statement implies the hard direction `NP ⊆ P`.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.nondeterministic_polynomial_time_contained_in_polynomial_time : ClayPVersusNP.Formulations.ClassEquality → ClayPVersusNP.Formulations.HardDirection := by
  intro h alphabet _ _ L hNP
  exact (h alphabet L).2 hNP

/--
The literal equality statement implies the easy direction `P ⊆ NP`.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.polynomial_time_contained_in_nondeterministic_polynomial_time :
    ClayPVersusNP.Formulations.ClassEquality →
      ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
        InPolynomialTime (fin_encoding_string alphabet) L → InNondeterministicPolynomialTime (fin_encoding_string alphabet) L := by
  intro h alphabet _ _ L hP
  exact (h alphabet L).1 hP

/--
The literal equality statement is equivalent to the two inclusions `P ⊆ NP` and `NP ⊆ P`.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.iff_subsets :
    ClayPVersusNP.Formulations.ClassEquality ↔
      (∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
        InPolynomialTime (fin_encoding_string alphabet) L → InNondeterministicPolynomialTime (fin_encoding_string alphabet) L) ∧ ClayPVersusNP.Formulations.HardDirection := by
  constructor
  · intro h
    exact ⟨h.polynomial_time_contained_in_nondeterministic_polynomial_time, h.nondeterministic_polynomial_time_contained_in_polynomial_time⟩
  · intro h alphabet _ _ L
    exact ⟨h.1 alphabet L, h.2 alphabet L⟩

/--
Specializing the literal class equality `P = NP` gives Cook's hard direction `NP ⊆ P`.

This is only the forward implication from the literal class equality.  The reverse implication
uses the certificate-ignoring verifier construction below to prove the easy direction `P ⊆ NP`.
-/
theorem ClayPVersusNP.nondeterministic_polynomial_time_contained_in_polynomial_time (h : ClayPVersusNP) : ClayPVersusNP.Formulations.HardDirection :=
  ClayPVersusNP.Formulations.ClassEquality.nondeterministic_polynomial_time_contained_in_polynomial_time h

/--
The hard direction from `P = NP` is Cook's deterministic-simulation wording.
-/
theorem ClayPVersusNP.nondeterministic_polynomial_time_simulation
    (h : ClayPVersusNP) :
    ClayPVersusNP.Formulations.DeterministicSimulation := by
  simpa [ClayPVersusNP.Formulations.DeterministicSimulation, ClayPVersusNP.Formulations.HardDirection] using ClayPVersusNP.nondeterministic_polynomial_time_contained_in_polynomial_time h

/--
The hard direction from `P = NP` says that polynomially checkable languages are polynomial-time
decidable.
-/
theorem ClayPVersusNP.checkable_solvable
    (h : ClayPVersusNP) :
    ClayPVersusNP.Formulations.CheckableImpliesSolvable :=
  ClayPVersusNP.Formulations.CheckableImpliesSolvable.iff_hard_direction.2 (ClayPVersusNP.nondeterministic_polynomial_time_contained_in_polynomial_time h)

/--
`ClayPVersusNP` also gives the easy inclusion `P ⊆ NP`, since the proposition is the literal
class equality `P = NP`.
-/
theorem ClayPVersusNP.polynomial_time_contained_in_nondeterministic_polynomial_time
    (h : ClayPVersusNP) :
      ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
        InPolynomialTime (fin_encoding_string alphabet) L → InNondeterministicPolynomialTime (fin_encoding_string alphabet) L :=
  ClayPVersusNP.Formulations.ClassEquality.polynomial_time_contained_in_nondeterministic_polynomial_time h

/--
The hard direction `NP ⊆ P`, together with the certificate-ignoring verifier lift for the easy
direction, is exactly enough to obtain the literal class equality `P = NP`.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.hard_direction :
    ClayPVersusNP.Support.DeciderAsVerifier → ClayPVersusNP.Formulations.HardDirection → ClayPVersusNP.Formulations.ClassEquality := by
  intro hLift hHard
  exact ClayPVersusNP.Formulations.ClassEquality.iff_subsets.2 ⟨PolynomialTimeContainedInNondeterministicPolynomialTime.certificate_verifier hLift, hHard⟩

/--
The hard direction plus polynomial-time left projection and polynomial-time composition closure
give the literal class equality `P = NP`.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.of_hard_direction_and_projection
    (hProj : LeftProjection.polynomial_time_computable) (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP.Formulations.HardDirection → ClayPVersusNP.Formulations.ClassEquality := by
  intro hHard
  exact ClayPVersusNP.Formulations.ClassEquality.hard_direction
    (ClayPVersusNP.Support.DeciderAsVerifier.of_projection hProj hComp) hHard

/--
The hard direction plus polynomial-time composition closure give the literal class equality
`P = NP`; the easy direction follows from the verified left-projection machine in this file.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.of_hard_direction_and_turing_machine_composition
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP.Formulations.HardDirection → ClayPVersusNP.Formulations.ClassEquality :=
  ClayPVersusNP.Formulations.ClassEquality.hard_direction (ClayPVersusNP.Support.DeciderAsVerifier.of_left_projection_machine hComp)

/--
With the certificate-ignoring verifier construction available, the literal class equality
`P = NP` is equivalent to the hard inclusion `NP ⊆ P`.
-/
theorem ClayPVersusNP.Formulations.ClassEquality.iff_hard_direction
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP.Formulations.ClassEquality ↔ ClayPVersusNP.Formulations.HardDirection := by
  constructor
  · exact ClayPVersusNP.Formulations.ClassEquality.nondeterministic_polynomial_time_contained_in_polynomial_time
  · exact ClayPVersusNP.Formulations.ClassEquality.of_hard_direction_and_turing_machine_composition hComp

/-- With the concrete easy-direction construction, the positive branch is equivalent to `NP ⊆ P`. -/
theorem ClayPVersusNP.iff_hard_direction
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP ↔ ClayPVersusNP.Formulations.HardDirection := by
  simpa [ClayPVersusNP, ClayPVersusNP.Formulations.ClassEquality] using ClayPVersusNP.Formulations.ClassEquality.iff_hard_direction hComp

/--
With the concrete easy-direction construction available, Cook's hard direction `NP ⊆ P` gives
`ClayPVersusNP`.
-/
theorem ClayPVersusNP.Formulations.HardDirection.polynomial_time_equals_nondeterministic_polynomial_time
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) (h : ClayPVersusNP.Formulations.HardDirection) :
    ClayPVersusNP :=
  (ClayPVersusNP.iff_hard_direction hComp).2 h

/-- With the concrete easy-direction construction, the positive branch is equivalent to simulation. -/
theorem ClayPVersusNP.iff_nondeterministic_polynomial_time_simulation
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP ↔ ClayPVersusNP.Formulations.DeterministicSimulation := by
  simpa [ClayPVersusNP, ClayPVersusNP.Formulations.ClassEquality, ClayPVersusNP.Formulations.DeterministicSimulation, ClayPVersusNP.Formulations.HardDirection] using
    ClayPVersusNP.Formulations.ClassEquality.iff_hard_direction hComp

/--
With the concrete easy-direction construction available, Cook's deterministic-simulation wording
is equivalent to the literal class equality `P = NP`.
-/
theorem ClayPVersusNP.Formulations.DeterministicSimulation.polynomial_time_equals_nondeterministic_polynomial_time
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition)
    (h : ClayPVersusNP.Formulations.DeterministicSimulation) :
    ClayPVersusNP :=
  (ClayPVersusNP.iff_nondeterministic_polynomial_time_simulation hComp).2 h

/--
With the same explicit two-stack Turing-machine composition closure assumption, the positive branch
is equivalent to Cook's verification wording: every efficiently checkable language is efficiently
solvable.
-/
theorem ClayPVersusNP.iff_checkable
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP ↔ ClayPVersusNP.Formulations.CheckableImpliesSolvable :=
  (ClayPVersusNP.iff_nondeterministic_polynomial_time_simulation hComp).trans
    ClayPVersusNP.Formulations.DeterministicSimulation.iff_checkable

/--
With the concrete easy-direction construction available, Cook's verification-to-solution wording
is equivalent to the literal class equality `P = NP`.
-/
theorem ClayPVersusNP.Formulations.CheckableImpliesSolvable.polynomial_time_equals_nondeterministic_polynomial_time
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition)
    (h : ClayPVersusNP.Formulations.CheckableImpliesSolvable) :
    ClayPVersusNP :=
  (ClayPVersusNP.iff_checkable hComp).2 h

/--
Cook, Proposition 1(c): if `L` is NP-complete and `L ∈ P`, then the hard direction
`NP ⊆ P` holds.  The literal `P = NP` version is `CookNondeterministicPolynomialTimeCompleteInPolynomialTime.polynomial_time_equals_nondeterministic_polynomial_time`,
which combines this theorem with the formal easy inclusion `P ⊆ NP`.
-/
theorem CookNondeterministicPolynomialTimeCompleteInPolynomialTime.nondeterministic_polynomial_time_contained_in_polynomial_time (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    ClayPVersusNP.Support.PolynomialTimeComputableComposition →
    NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L → InPolynomialTime (fin_encoding_string alphabet) L → ClayPVersusNP.Formulations.HardDirection := by
  intro hComp hComplete hP alphabet' _ _ L' hNP'
  have hRed : PolynomialTimeReducible (fin_encoding_string alphabet') (fin_encoding_string alphabet) L' L :=
    hComplete.2 (fin_encoding_string alphabet') L' hNP'
  exact PolynomialTimeReducible.source_in_p
    (fin_encoding_string alphabet') (fin_encoding_string alphabet) L' L hComp hRed hP

/--
Cook, Proposition 1(c) in literal `P = NP` form, conditional on the standard easy inclusion
`P ⊆ NP` for this two-stack Turing-machine-based model.
-/
theorem CookNondeterministicPolynomialTimeCompleteInPolynomialTime.polynomial_time_equals_nondeterministic_polynomial_time (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    ClayPVersusNP.Support.DeciderAsVerifier →
    ClayPVersusNP.Support.PolynomialTimeComputableComposition →
    NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L → InPolynomialTime (fin_encoding_string alphabet) L → ClayPVersusNP.Formulations.ClassEquality := by
  intro hLift hComp hComplete hP
  exact ClayPVersusNP.Formulations.ClassEquality.hard_direction hLift (CookNondeterministicPolynomialTimeCompleteInPolynomialTime.nondeterministic_polynomial_time_contained_in_polynomial_time alphabet L hComp hComplete hP)

/--
Cook, Proposition 1(c) in literal `P = NP` form, from the projection primitive and composition
closure needed for the easy inclusion and reduction closure.
-/
theorem CookNondeterministicPolynomialTimeCompleteInPolynomialTime.of_projection
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    LeftProjection.polynomial_time_computable →
    ClayPVersusNP.Support.PolynomialTimeComputableComposition →
    NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L → InPolynomialTime (fin_encoding_string alphabet) L → ClayPVersusNP.Formulations.ClassEquality := by
  intro hProj hComp hComplete hP
  exact CookNondeterministicPolynomialTimeCompleteInPolynomialTime.polynomial_time_equals_nondeterministic_polynomial_time alphabet L
    (ClayPVersusNP.Support.DeciderAsVerifier.of_projection hProj hComp) hComp hComplete hP

/--
Cook, Proposition 1(c) in literal `P = NP` form, with the finite-string projection primitive
discharged by the concrete linear-time machine proved above.
-/
theorem CookNondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    ClayPVersusNP.Support.PolynomialTimeComputableComposition →
    NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L → InPolynomialTime (fin_encoding_string alphabet) L → ClayPVersusNP.Formulations.ClassEquality := by
  intro hComp hComplete hP
  exact CookNondeterministicPolynomialTimeCompleteInPolynomialTime.polynomial_time_equals_nondeterministic_polynomial_time alphabet L
    (ClayPVersusNP.Support.DeciderAsVerifier.of_left_projection_machine hComp) hComp hComplete hP

/--
Clay consequence of Cook's Proposition 1(c):
if any `NP`-complete language is decidable in polynomial time, then `P = NP`.
-/
def ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)),
    NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L →
      InPolynomialTime (fin_encoding_string alphabet) L → ClayPVersusNP.Formulations.ClassEquality

/--
The Clay `NP`-complete-in-`P` consequence follows from polynomial-time composition
closure for the concrete two-stack Turing-machine model.
-/
theorem ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) :
    ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime := by
  intro alphabet _ _ L hComplete hP
  exact CookNondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition alphabet L hComp hComplete hP

/-- A polynomial-time `NP`-complete language proves the positive Clay statement `P = NP`. -/
theorem ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition)
    {alphabet : Type} [Fintype alphabet] [Nontrivial alphabet]
    {L : Language (List alphabet)}
    (hComplete : NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L)
    (hP : InPolynomialTime (fin_encoding_string alphabet) L) :
    ClayPVersusNP := by
  simpa [ClayPVersusNP, ClayPVersusNP.Formulations.ClassEquality] using
    CookNondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition alphabet L hComp hComplete hP

namespace ClayFiniteAlphabet

/--
Fixed-alphabet Clay consequence of Cook's Proposition 1(c):
if an `NP`-complete language over this alphabet is in `P`, then `P = NP` over this alphabet.
-/
def NondeterministicPolynomialTimeCompleteInPolynomialTime (A : ClayFiniteAlphabet) : Prop :=
  ∀ L : A.Language,
    NondeterministicPolynomialTimeComplete (fin_encoding_string A.carrier) L →
      InPolynomialTime (fin_encoding_string A.carrier) L → A.PolynomialTimeEqualsNondeterministicPolynomialTime

/-- The global Clay `NP`-complete-in-`P` consequence applies to one fixed alphabet. -/
theorem NondeterministicPolynomialTimeCompleteInPolynomialTime.of_global
    (h : ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime) (A : ClayFiniteAlphabet) :
    A.NondeterministicPolynomialTimeCompleteInPolynomialTime := by
  intro L hComplete hP L'
  exact (h A.carrier L hComplete hP) A.carrier L'

/--
The fixed-alphabet `NP`-complete-in-`P` consequence follows from polynomial-time composition
closure for the concrete two-stack Turing-machine model.
-/
theorem NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition
    (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition) (A : ClayFiniteAlphabet) :
    A.NondeterministicPolynomialTimeCompleteInPolynomialTime :=
  NondeterministicPolynomialTimeCompleteInPolynomialTime.of_global
    (ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition hComp) A

/-- A polynomial-time fixed-alphabet `NP`-complete language proves fixed-alphabet `P = NP`. -/
theorem PolynomialTimeEqualsNondeterministicPolynomialTime.nondeterministic_polynomial_time_complete_in_polynomial_time
    (A : ClayFiniteAlphabet) (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition)
    {L : A.Language}
    (hComplete : NondeterministicPolynomialTimeComplete (fin_encoding_string A.carrier) L)
    (hP : InPolynomialTime (fin_encoding_string A.carrier) L) :
    A.PolynomialTimeEqualsNondeterministicPolynomialTime :=
  (NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition hComp A) L hComplete hP

end ClayFiniteAlphabet

/-- An NP-complete language is, in particular, in NP. -/
theorem NondeterministicPolynomialTimeComplete.in_nondeterministic_polynomial_time {α : Type} {ea : FinEncoding α} {L : Language α} :
    NondeterministicPolynomialTimeComplete ea L → InNondeterministicPolynomialTime ea L :=
  fun h => h.1

/--
If `L` is NP-complete and `L' ∈ NP`, then `L'` polynomial-time reduces to `L`.

This just unwraps the second field of `NondeterministicPolynomialTimeComplete`.
-/
theorem NondeterministicPolynomialTimeComplete.reduces {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {L : Language α} {L' : Language β} :
    NondeterministicPolynomialTimeComplete ea L → InNondeterministicPolynomialTime eb L' → PolynomialTimeReducible eb ea L' L := by
  intro h hL'
  exact h.2 eb L' hL'

/-- Positive outcome of Cook's decision problem: the finite-alphabet classes `P` and `NP` agree. -/
abbrev ClayPVersusNP.Formulations.PositiveBranch : Prop :=
  ClayPVersusNP

/-- Negative outcome of Cook's decision problem: the finite-alphabet classes `P` and `NP` differ. -/
def ClayPVersusNP.Formulations.NegativeBranch : Prop :=
  ¬ ClayPVersusNP

/-!
## How to claim a solution

The two target propositions of this file are

* `Millennium.ClayPVersusNP` — `P = NP` in this finite-alphabet two-stack Turing-machine model
  (the class equality `ClayPVersusNP.Formulations.ClassEquality`), and
* `Millennium.ClayPVersusNP.Formulations.NegativeBranch` — `P ≠ NP`, literally `¬ ClayPVersusNP`.

A solution of the Clay problem is a `sorry`-free proof of **one** of these two propositions, and
the registry (`Problems/Registry.lean`) records both as the admissible outcomes.

No aggregate declaration is provided: neither the disjunction
`ClayPVersusNP ∨ ClayPVersusNP.Formulations.NegativeBranch` nor a two-constructor `Type` whose
constructors carry proofs of the two branches.  The disjunction is an instance of excluded middle,
and the `Type`-shaped version is inhabited just as easily, since `Classical.propDecidable` gives a
`Decidable ClayPVersusNP` instance and `dite` eliminates into `Type`; see
`Tests/AggregateTargets.lean`.  Any such aggregate would therefore be provable without any
complexity theory and would not encode the mathematical challenge.
-/

end Millennium
