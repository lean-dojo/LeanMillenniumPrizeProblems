/-!
# Common Registry Metadata

Shared metadata types for the repository-level registry of Clay Millennium problem statements.
-/

namespace MillenniumProblems

/-! ## Classification types -/

/-- Current mathematical status of the Clay problem. -/
inductive ProblemStatus where
  | open_problem
  | solved_problem
  deriving DecidableEq

namespace ProblemStatus

/-- Human-readable status label for generated summaries. -/
def label : ProblemStatus → String
  | open_problem => "open"
  | solved_problem => "solved"

end ProblemStatus

/-- The mathematical shape of a solution to a Clay statement. -/
inductive ResolutionShape where
  /-- Solve by proving the stated proposition directly. -/
  | prove
  /-- Solve by proving one case of a formal disjunction already present in the statement. -/
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

The `statement` field is the checked Lean proposition that this repository exposes. The string
fields are documentation handles; they deliberately do not affect the mathematical content.
-/
structure ClayProblem where
  /-- Short display name. -/
  short_name : String
  /-- Full display name. -/
  title : String
  /-- The Lean proposition tracked by this registry entry. -/
  statement : Prop
  /-- Fully qualified Lean declaration for `statement`. -/
  statement_declaration : String
  /-- Optional mutually exclusive alternative outcome, used for decision problems. -/
  alternative_statement : Option Prop := none
  /-- Fully qualified Lean declaration for the optional alternative outcome. -/
  alternative_statement_declaration : Option String := none
  /-- Fully qualified final declaration whose placeholder body future work should replace. -/
  prize_theorem_declaration : String
  /-- Whether the problem is mathematically open or solved. -/
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

/-- True when the registry entry is currently marked open. -/
def is_open (problem : ClayProblem) : Bool :=
  problem.status == ProblemStatus.open_problem

/-- True when the registry entry is currently marked solved. -/
def is_solved (problem : ClayProblem) : Bool :=
  problem.status == ProblemStatus.solved_problem

end ClayProblem

end MillenniumProblems
