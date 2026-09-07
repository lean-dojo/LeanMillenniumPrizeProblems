/-!
# Common Registry Metadata

Shared metadata types for the repository-level registry of Clay Millennium problem statements.
-/

namespace MillenniumProblems

/-! ## Classification types -/

/-- Status of a Clay problem's Lean statement in this repository. -/
inductive ProblemStatus where
  /-- The mathematics is open and the Lean statement is believed to be faithful. -/
  | open_problem
  /-- The mathematics is settled and the Lean statement is believed to be faithful; a Lean proof
  may still be missing. -/
  | solved_problem
  /-- The Lean statement is an interface sketch with known defects.  It is not a valid target: a
  proof of it would not represent progress on the mathematical problem. -/
  | statement_incomplete
  deriving DecidableEq

namespace ProblemStatus

/-- Human-readable status label for generated summaries. -/
def label : ProblemStatus → String
  | open_problem => "open"
  | solved_problem => "solved"
  | statement_incomplete => "statement incomplete (not a valid target)"

end ProblemStatus

/-- The mathematical shape of a solution to a Clay statement. -/
inductive ResolutionShape where
  /-- Solve by proving the stated proposition directly. -/
  | prove
  /-- Solve by proving one of several alternative propositions listed separately. -/
  | prove_one_case
  /-- Solve by constructing an object satisfying the stated properties. -/
  | construct_object
  /-- Solve by proving one of the mutually exclusive mathematical outcomes. -/
  | decide
  deriving DecidableEq

namespace ResolutionShape

/-- Human-readable resolution-shape label for generated summaries. -/
def label : ResolutionShape → String
  | prove => "prove statement"
  | prove_one_case => "prove one case"
  | construct_object => "construct object"
  | decide => "decide between outcomes"

end ResolutionShape

/-! ## Registry record -/

/--
Repository-level metadata for a Clay problem.

The `statement` and `alternative_statements` fields are the checked Lean propositions that this
repository exposes; a proof of any one of them settles the problem.  The string fields are
documentation handles; they deliberately do not affect the mathematical content.
-/
structure ClayProblem where
  /-- Short display name. -/
  short_name : String
  /-- Full display name. -/
  title : String
  /-- The primary Lean proposition tracked by this registry entry. -/
  statement : Prop
  /-- Fully qualified Lean declaration for `statement`. -/
  statement_declaration : String
  /-- Further outcome propositions, for problems that ask which of several alternatives holds.
  A proof of `statement` or of any element of this list settles the problem. -/
  alternative_statements : List Prop := []
  /-- Fully qualified Lean declarations for `alternative_statements`, in the same order. -/
  alternative_statement_declarations : List String := []
  /-- Placeholder declaration whose `sorry` a proof should replace, when the problem has one.

  Problems with several alternatives have no placeholder: any single declaration that covers all
  alternatives, whether a disjunction or an inductive type with one constructor per alternative,
  is provable by classical case analysis (see `Tests/AggregateTargets.lean`).  Problems whose
  statement is incomplete have no placeholder either. -/
  prize_theorem_declaration : Option String := none
  /-- Status of the Lean statement. -/
  status : ProblemStatus
  /-- What kind of mathematical act would resolve the problem. -/
  resolution_shape : ResolutionShape
  /-- Concise explanation of why this resolution shape is used. -/
  resolution_note : String
  /-- Concise note about the main formalization choices in this statement. -/
  formalization_note : String
  /-- Important supporting or alternative declarations. -/
  related_declarations : List String := []

namespace ClayProblem

/-- True when the registry entry is an open problem with a faithful statement. -/
def is_open (problem : ClayProblem) : Bool :=
  problem.status == ProblemStatus.open_problem

/-- True when the registry entry is a solved problem. -/
def is_solved (problem : ClayProblem) : Bool :=
  problem.status == ProblemStatus.solved_problem

/-- True when the registry entry's statement is incomplete and not a valid target. -/
def is_incomplete (problem : ClayProblem) : Bool :=
  problem.status == ProblemStatus.statement_incomplete

/-- All propositions a proof of which settles the problem. -/
def target_statements (problem : ClayProblem) : List Prop :=
  problem.statement :: problem.alternative_statements

end ClayProblem

end MillenniumProblems
