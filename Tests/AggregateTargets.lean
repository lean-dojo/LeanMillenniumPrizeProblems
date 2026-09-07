import Mathlib.Logic.Basic

/-!
# Why this repository has no aggregate targets

Two of the Clay problems ask which of several alternatives holds: P versus NP (`P = NP` or
`P ≠ NP`) and Navier–Stokes (Fefferman's cases (A)–(D)).  It is tempting to expose a single
declaration whose proof "settles the problem", either as the disjunction of the alternatives or as
an inductive `Type` with one constructor per alternative.  Neither is a meaningful target:

* the disjunction `P ∨ ¬P` is `Classical.em`;
* the inductive `Type` is inhabited by classical case analysis, because `Classical.propDecidable`
  provides a `Decidable` instance and `dite` eliminates into `Type`.

Both are demonstrated below.  The repository therefore exposes the alternatives as separate named
propositions and states in `README.md` and `Problems/Registry.lean` which of them count as a
solution.
-/

namespace Tests.AggregateTargets

/-- A two-constructor "resolution type" for an arbitrary proposition `P`. -/
inductive Resolution (P : Prop) : Type where
  /-- `P` holds. -/
  | yes (h : P)
  /-- `P` fails. -/
  | no (h : ¬P)

open Classical in
/-- The resolution type is inhabited for every `P`, with no information about `P`. -/
noncomputable def resolve (P : Prop) : Resolution P :=
  if h : P then .yes h else .no h

/-- The disjunction of the two alternatives is excluded middle. -/
theorem or_not (P : Prop) : P ∨ ¬P :=
  Classical.em P

end Tests.AggregateTargets
