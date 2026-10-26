import Problems.YangMills.QuantumObservableLift

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Corrected incoming observables in the fixed OPE extractor

This is the same finite regulated OPE coefficient construction, with actual
quantum cocycle lifts on every incoming insertion. Output labels remain the
FULL local monomial basis: a physical invariant polynomial is not a dual
extractor. Recovery of outgoing physical coefficients uses the same corrected
dictionary and generated quantum Ward quotient.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

structure LiftedInsertionCluster (G : CompactSimpleGaugeGroup) where
  initial : List (InvariantInsertionLabel G × Spacetime)
  last : InvariantInsertionLabel G × Spacetime

def LiftedInsertionCluster.insertions (input : LiftedInsertionCluster G) :
    List (InvariantInsertionLabel G × Spacetime) := input.initial ++ [input.last]

/-- Exact multilinear local-representative expansion, with the remaining
loop index passed to the SAME raw regulated coefficient. Every incoming
hbar correction consumes its own loop order. Local ordering is preserved. -/
def liftedInsertionExpansion (lift : QuantumObservableLift G) (g UV : ℝ)
    (value : ℕ → List (PositionedInsertion G) → ℂ) :
    List (InvariantInsertionLabel G × Spacetime) → ℕ →
      List (PositionedInsertion G) → ℂ
  | [], loop, accumulated => value loop accumulated
  | (p, x) :: rest, loop, accumulated =>
      ∑ l : Fin (loop + 1), (lift.coefficient g p l.val UV).sum (fun m c =>
        c * liftedInsertionExpansion lift g UV value rest (loop - l.val)
          (accumulated ++ [⟨m, x⟩]))

/-- Defensive empty-list branch is never reached from a nonempty lifted
cluster. The distinguished final insertion point is preserved by expansion. -/
def insertionClusterOfList (input : List (PositionedInsertion G)) :
    Option (InsertionCluster G) :=
  match input.reverse with
  | [] => none
  | last :: previous => some ⟨previous.reverse, last⟩

/-- No new coefficient choice: use the exact earlier source (5.5)–(5.7)
extractor after finite expansion of the corrected incoming local fields. -/
def liftedRegulatedOPECoefficient (lift : QuantumObservableLift G)
    (L : InsertedFlowFamily G) (F : OversubtractedFamily G) (g μ UV : ℝ)
    (input : LiftedInsertionCluster G) (loop : ℕ) (output : LocalMonomial G) : ℂ :=
  liftedInsertionExpansion lift g UV (fun remaining raw =>
    match insertionClusterOfList raw with
    | none => 0
    | some cluster => regulatedOPECoefficient L F μ UV cluster remaining output)
    input.insertions loop []

end YangMills.PerturbativeFlow
