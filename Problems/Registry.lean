import Problems.Common.Registry
import Problems.PVersusNP.Millennium
import Problems.RiemannHypothesis.Millennium
import Problems.NavierStokes.Millennium
import Problems.Hodge.Millennium
import Problems.BirchSwinnertonDyer.Millennium
import Problems.YangMills.Millennium
import Problems.YangMills.HamiltonianSpectrum
import Problems.Poincare.Millennium

/-!
# Millennium Prize Problem registry

This module records the repository's statement-first style in Lean.

The problem modules define the Clay mathematical outcomes as `Prop`s.  This registry records, as
checked Lean metadata, which propositions count as a solution of each problem, what kind of
resolution each problem calls for, and which formalization choices are worth knowing.

Design points:
* `statement` is the primary mathematical proposition; `alternative_statements` lists the other
  outcome propositions for problems that ask which of several alternatives holds (P versus NP has
  two outcomes, Navier–Stokes has Fefferman's four).  A proof of any one of them settles the
  problem.
* There is deliberately **no aggregate declaration** for such problems.  The disjunction of the
  alternatives, or an inductive type with one constructor per alternative, is inhabited by
  classical case analysis and therefore carries no information (`Tests/AggregateTargets.lean`,
  `Tests/NavierStokes/AggregateIsTrivial.lean`).
* `prize_theorem_declaration` names the `sorry` placeholder a proof should replace, for the
  problems that have one (Riemann, Birch and Swinnerton-Dyer, Poincaré).
* `status = statement_incomplete` marks statements that are known to be interface sketches rather
  than faithful formalizations (Hodge, Yang–Mills).  They are not valid targets and have no
  placeholder.
* `resolution_shape` says what a future solution would have to do; `formalization_note` records
  modeling choices without changing the proposition.
-/

namespace MillenniumProblems

/-! ## Problem entries -/

/-- Registry entry for P versus NP. -/
def p_versus_np : ClayProblem where
  short_name := "P vs NP"
  title := "P versus NP"
  statement := Millennium.ClayPVersusNP
  statement_declaration := "Millennium.ClayPVersusNP"
  alternative_statements := [Millennium.ClayPVersusNP.Formulations.NegativeBranch]
  alternative_statement_declarations := ["Millennium.ClayPVersusNP.Formulations.NegativeBranch"]
  prize_theorem_declaration := none
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.decide
  resolution_note :=
    "Clay's question is to settle whether P equals NP. A sorry-free proof of either outcome proposition (P = NP, or its negation) settles it. No aggregate declaration is provided: the disjunction and a two-constructor resolution type are both inhabited by classical case analysis."
  formalization_note :=
    "Uses Cook's verifier definition with certificates that are strings over a finite alphabet and an explicit finite-alphabet machine model. Before September 2026 the certificate type carried an arbitrary encoding, which put every language in NP."
  related_declarations := [
    "Millennium.ClayPVersusNP.Formulations.PositiveBranch",
    "Millennium.ClayPVersusNP.Formulations.ClassEquality",
    "Millennium.ClayPVersusNP.Formulations.NegativeBranch",
    "Millennium.ClayPVersusNP.Formulations.DeterministicSimulation"
  ]

/-- Registry entry for the Riemann Hypothesis. -/
def riemann_hypothesis : ClayProblem where
  short_name := "Riemann"
  title := "Riemann Hypothesis"
  statement := Millennium.ClayRiemannHypothesis
  statement_declaration := "Millennium.ClayRiemannHypothesis"
  prize_theorem_declaration := some "Millennium.clay_prize_riemann_hypothesis"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "The statement is the positive critical-line formulation for every nontrivial zeta zero; it is equivalent to Mathlib's `RiemannHypothesis`."
  formalization_note :=
    "The registered zeta statement is the critical-line formulation; the xi statement and zero correspondence are supporting views."
  related_declarations := [
    "Millennium.ClayRiemannHypothesis",
    "Millennium.ClayRiemannHypothesis.Formulations.XiZeros",
    "Millennium.ClayRiemannHypothesis.Formulations.RealPart"
  ]

/-- Registry entry for Navier-Stokes existence and smoothness. -/
def navier_stokes : ClayProblem where
  short_name := "Navier-Stokes"
  title := "Navier-Stokes existence and smoothness"
  statement := MillenniumNavierStokes.FeffermanA
  statement_declaration := "MillenniumNavierStokes.FeffermanA"
  alternative_statements :=
    [MillenniumNavierStokes.FeffermanB, MillenniumNavierStokes.FeffermanC,
      MillenniumNavierStokes.FeffermanD]
  alternative_statement_declarations :=
    ["MillenniumNavierStokes.FeffermanB", "MillenniumNavierStokes.FeffermanC",
      "MillenniumNavierStokes.FeffermanD"]
  prize_theorem_declaration := none
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove_one_case
  resolution_note :=
    "Fefferman's Clay statement offers four alternatives (A)-(D); a sorry-free proof of any one of them settles the problem. Their disjunction is a classical tautology (zero force plus the Navier-Stokes scaling symmetry) and is therefore not a target."
  formalization_note :=
    "Solution and forcing smoothness are stated on the closed half-space R^3 x [0, infinity), the equations and the derivative bounds on the open half-space t > 0 (ambient derivatives are junk on the boundary), and the pressure-periodicity erratum is included."
  related_declarations := [
    "NavierStokesOnR3.SmoothExistence",
    "NavierStokesPeriodic.SmoothExistence",
    "NavierStokesOnR3.Breakdown",
    "NavierStokesPeriodic.Breakdown"
  ]

/-- Registry entry for the Hodge Conjecture. -/
def hodge_conjecture : ClayProblem where
  short_name := "Hodge"
  title := "Hodge Conjecture"
  statement := MillenniumHodge.ClayHodge.{0, 0, 0}
  statement_declaration := "MillenniumHodge.ClayHodge"
  prize_theorem_declaration := none
  status := ProblemStatus.statement_incomplete
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "Not a valid target. The statement is vacuously true because no SmoothProjectiveVariety has a complex point (PR #9), and it would become false once that is repaired because the cycle-class map is free data (Tests/Hodge/CycleClassUnconstrained.lean)."
  formalization_note :=
    "Axiomatic interface sketch. A faithful statement needs the analytic topology on X(C), singular cohomology with a defined Hodge decomposition and cycle-class map, and the rational-complex comparison isomorphism, none of which exist in Mathlib yet."
  related_declarations := [
    "MillenniumHodge.HodgeTheoryAssignment.ClayStatement",
    "MillenniumHodge.HodgeTheoryRealization",
    "MillenniumHodge.ClayHodge.Formulations.AllCoherentConjectures",
    "MillenniumHodge.HodgeConjecture.Formulations.FixedCycleSpan"
  ]

/-- Registry entry for the Birch and Swinnerton-Dyer Conjecture. -/
def birch_swinnerton_dyer : ClayProblem where
  short_name := "Birch-Swinnerton-Dyer"
  title := "Birch and Swinnerton-Dyer"
  statement := MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer
  statement_declaration :=
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
  prize_theorem_declaration :=
    some "MillenniumBirchSwinnertonDyer.clay_prize_birch_swinnerton_dyer"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "The statement is the Taylor/rank formulation for elliptic curves over Q. It is existential in the analytic continuation, so a proof must also supply the continuation (modularity and the Hasse bound) and a finite rank (Mordell-Weil)."
  formalization_note :=
    "The ordinary LSeriesData contains only the Clay continuation and Euler-product agreement; optional bad-prime comparison data lives in HasseWeilLSeriesData, whose correction factor is required to be analytic at s = 1 only."
  related_declarations := [
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Taylor.Integral",
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Rank.HasseWeil",
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Rank.IncompleteLSeries"
  ]

/-- Registry entry for Yang-Mills existence and mass gap. -/
def yang_mills : ClayProblem where
  short_name := "Yang-Mills"
  title := "Yang-Mills existence and mass gap"
  statement := MillenniumYangMills.ClayYangMills
  statement_declaration := "MillenniumYangMills.ClayYangMills"
  prize_theorem_declaration := none
  status := ProblemStatus.statement_incomplete
  resolution_shape := ResolutionShape.construct_object
  resolution_note :=
    "Not a valid target. The quantum-field-theory data are an axiomatic sketch that is not tied to Yang-Mills theory or to relativity, so the existence statement can be satisfied by a two-dimensional toy model."
  formalization_note :=
    "The gauge field stores connection and curvature independently, the Lie algebra has no bracket, the Poincare group is an arbitrary group unrelated to the Hamiltonian, and the unbounded physical Hamiltonian is tied to a bounded operator's spectrum. The vacuum-uniqueness axiom was contradictory before September 2026."
  related_declarations := [
    "MillenniumYangMills.ClayYangMills.Formulations.FixedGroup",
    "MillenniumYangMills.ClayYangMills.Formulations.PhysicalHamiltonian.Statement",
    "MillenniumYangMills.ClayYangMills.Formulations.LorentzCovariant.Statement"
  ]

/-- Registry entry for the Poincare Conjecture. -/
def poincare : ClayProblem where
  short_name := "Poincare"
  title := "Poincare Conjecture"
  statement := MillenniumPoincare.ClayPoincareConjecture.{0}
  statement_declaration := "MillenniumPoincare.ClayPoincareConjecture"
  prize_theorem_declaration := some "MillenniumPoincare.clay_prize_poincare_conjecture"
  status := ProblemStatus.solved_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "Perelman's theorem proves the topological three-manifold statement; this repository records `ClayPoincareConjecture`, which is equivalent to the shape of Mathlib's `proof_wanted` statement."
  formalization_note :=
    "Closed simply connected three-manifold statement, with equivalent closed-curve and pi_1 wordings."
  related_declarations := [
    "MillenniumPoincare.ClayPoincareConjecture.Formulations.SimplyConnectedClosed3Manifold",
    "MillenniumPoincare.ClayPoincareConjecture.Formulations.ClosedCurves",
    "MillenniumPoincare.ClayPoincareConjecture.Formulations.TrivialPi1"
  ]

/-! ## Derived views and consistency checks -/

/-- The seven Clay Millennium problem registry entries. -/
def all_problems : List ClayProblem :=
  [p_versus_np, riemann_hypothesis, navier_stokes, hodge_conjecture,
    birch_swinnerton_dyer, yang_mills, poincare]

/-- The open Millennium problems whose Lean statements are believed to be faithful. -/
def open_problems : List ClayProblem :=
  all_problems.filter ClayProblem.is_open

/-- The solved Millennium problem registry entries. -/
def solved_problems : List ClayProblem :=
  all_problems.filter ClayProblem.is_solved

/-- The registry entries whose Lean statements are known to be incomplete. -/
def incomplete_problems : List ClayProblem :=
  all_problems.filter ClayProblem.is_incomplete

/-- Count of Clay Millennium problem entries in this registry. -/
theorem all_problems.length_eq : all_problems.length = 7 := by
  decide

/-- Count of open entries with faithful statements. -/
theorem open_problems.length_eq : open_problems.length = 4 := by
  decide

/-- Count of solved entries. -/
theorem solved_problems.length_eq : solved_problems.length = 1 := by
  decide

/-- Count of entries whose statement is incomplete. -/
theorem incomplete_problems.length_eq : incomplete_problems.length = 2 := by
  decide

end MillenniumProblems
