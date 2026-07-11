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

The problem modules define the Clay mathematical outcomes as `Prop`s. This registry records, as
checked Lean metadata, what kind of resolution each problem calls for and which formalization
choices are worth knowing. P versus NP records two mutually exclusive outcome propositions and a
separate explicit resolution type.

If one of the open problems is solved in Lean later, its outcome proposition should stay stable and
the final placeholder should be replaced. The registry can then change `status` without changing
the mathematical outcome being tracked.

The design point is intentional:
* `statement` is the primary mathematical proposition; `alternative_statement` records a second
  decision outcome when needed.
* `prize_theorem_declaration` names the final placeholder body future work should replace.
* `resolution_shape` says what a future solution would have to do.
* `formalization_note` records ordinary modeling choices without changing the proposition.
-/

namespace MillenniumProblems

/-! ## Problem entries -/

/-- Registry entry for P versus NP. -/
def p_versus_np : ClayProblem where
  short_name := "P vs NP"
  title := "P versus NP"
  statement := Millennium.ClayPVersusNP
  statement_declaration := "Millennium.ClayPVersusNP"
  alternative_statement := some Millennium.ClayPVersusNP.Formulations.NegativeBranch
  alternative_statement_declaration :=
    some "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
  prize_theorem_declaration := "Millennium.clay_prize_p_versus_np"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.decide
  resolution_note :=
    "Clay's question is to settle whether P equals NP. Both P = NP and P != NP are checked outcomes, and the final resolution type accepts a proof of either one."
  formalization_note :=
    "Uses Cook's verifier definition and an explicit finite-alphabet machine model. The resolution is a two-constructor Type rather than the excluded-middle proposition P = NP or P != NP."
  related_declarations := [
    "Millennium.ClayPVersusNPResolution",
    "Millennium.ClayPVersusNP.Formulations.PositiveBranch",
    "Millennium.ClayPVersusNP.Formulations.ClassEquality",
    "Millennium.ClayPVersusNP.Formulations.NegativeBranch",
    "Millennium.ClayPVersusNP.Formulations.DeterministicSimulation"
  ]

/-
P vs NP is deliberately marked as `decide`.

The proposition `ClayPVersusNP.Formulations.ClassEquality ∨
¬ ClayPVersusNP.Formulations.ClassEquality` would not represent the prize problem in classical Lean:
it is an instance of excluded middle. The final declaration instead returns the explicit
`ClayPVersusNPResolution` type, whose constructors expose which outcome was proved. The registry
records both outcome propositions.
-/

/-- Registry entry for the Riemann Hypothesis. -/
def riemann_hypothesis : ClayProblem where
  short_name := "Riemann"
  title := "Riemann Hypothesis"
  statement := Millennium.ClayRiemannHypothesis
  statement_declaration := "Millennium.ClayRiemannHypothesis"
  prize_theorem_declaration := "Millennium.clay_prize_riemann_hypothesis"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "The statement is the positive critical-line formulation for every nontrivial zeta zero."
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
  statement := MillenniumNavierStokes.ClayNavierStokes
  statement_declaration := "MillenniumNavierStokes.ClayNavierStokes"
  prize_theorem_declaration := "MillenniumNavierStokes.clay_prize_navier_stokes"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove_one_case
  resolution_note :=
    "The Clay statement is Fefferman's disjunction of cases (A)-(D): smooth existence or breakdown in whole-space or periodic form."
  formalization_note :=
    "The Fefferman cases (A)-(D) are represented directly, with solution and forcing smoothness stated on the Clay half-space R^3 x [0, infinity) and the pressure-periodicity erratum included."
  related_declarations := [
    "NavierStokesOnR3.SmoothExistence",
    "NavierStokesPeriodic.SmoothExistence",
    "NavierStokesOnR3.Breakdown",
    "NavierStokesPeriodic.Breakdown"
  ]

/-
Navier-Stokes differs from the single-sentence conjectures: Fefferman's Clay statement is already
a disjunction of four cases.  The resolution shape records that solving the problem
means proving one branch, not proving four independent theorems.
-/

/-- Registry entry for the Hodge Conjecture. -/
def hodge_conjecture : ClayProblem where
  short_name := "Hodge"
  title := "Hodge Conjecture"
  statement := MillenniumHodge.ClayHodge.{0, 0, 0}
  statement_declaration := "MillenniumHodge.ClayHodge"
  prize_theorem_declaration := "MillenniumHodge.clay_prize_hodge_conjecture"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "Every canonical Hodge-theory realization must satisfy the Clay cycle-class statement; bare coherent synthetic test packages are excluded from the public target."
  formalization_note :=
    "The cycle-class sentence matches the Clay wording. Until native singular/Hodge cohomology is available, canonical realizations explicitly require injective complexification and a spanning Hodge decomposition."
  related_declarations := [
    "MillenniumHodge.HodgeTheoryAssignment.ClayStatement",
    "MillenniumHodge.HodgeTheoryRealization",
    "MillenniumHodge.ClayHodge.Formulations.AllCoherentConjectures",
    "MillenniumHodge.HodgeConjecture.Formulations.FixedCycleSpan"
  ]

/-
The Hodge statement is universe-polymorphic.  The registry instantiates it at `.{0, 0, 0}` because
the metadata table needs one concrete proposition, while the theorem file still exposes the fully
polymorphic declaration for mathematical use.
-/

/-- Registry entry for the Birch and Swinnerton-Dyer Conjecture. -/
def birch_swinnerton_dyer : ClayProblem where
  short_name := "Birch-Swinnerton-Dyer"
  title := "Birch and Swinnerton-Dyer"
  statement := MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer
  statement_declaration :=
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
  prize_theorem_declaration :=
    "MillenniumBirchSwinnertonDyer.clay_prize_birch_swinnerton_dyer"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "The statement is the Taylor/rank formulation for elliptic curves over Q, with L-series data explicit."
  formalization_note :=
    "The ordinary LSeriesData contains only the Clay continuation and Euler-product agreement; optional bad-prime comparison data lives in HasseWeilLSeriesData."
  related_declarations := [
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Taylor.Integral",
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer.Formulations.Rank.HasseWeil"
  ]

/-- Registry entry for Yang-Mills existence and mass gap. -/
def yang_mills : ClayProblem where
  short_name := "Yang-Mills"
  title := "Yang-Mills existence and mass gap"
  statement := MillenniumYangMills.ClayYangMills
  statement_declaration := "MillenniumYangMills.ClayYangMills"
  prize_theorem_declaration := "MillenniumYangMills.clay_prize_yang_mills"
  status := ProblemStatus.open_problem
  resolution_shape := ResolutionShape.construct_object
  resolution_note :=
    "The statement is an existence theorem: for each connected compact simple Lie gauge group, construct a nontrivial quantum Yang-Mills theory on R4 whose Hamiltonian spectrum has a positive finite mass gap."
  formalization_note :=
    "The gauge group is connected and its Lie algebra is identified with the smooth model space. The canonical spectral set equals the theory Hamiltonian spectrum; unbounded and Lorentz-covariant strengthenings remain related declarations."
  related_declarations := [
    "MillenniumYangMills.ClayYangMills.Formulations.FixedGroup",
    "MillenniumYangMills.ClayYangMills.Formulations.PhysicalHamiltonian.Statement",
    "MillenniumYangMills.ClayYangMills.Formulations.LorentzCovariant.Statement"
  ]

/-
The registry uses the canonical Clay Yang-Mills statement.  Stronger physical-Hamiltonian and
Lorentz-covariant formulations remain listed as related declarations.
-/

/-- Registry entry for the Poincare Conjecture. -/
def poincare : ClayProblem where
  short_name := "Poincare"
  title := "Poincare Conjecture"
  statement := MillenniumPoincare.ClayPoincareConjecture.{0}
  statement_declaration := "MillenniumPoincare.ClayPoincareConjecture"
  prize_theorem_declaration := "MillenniumPoincare.clay_prize_poincare_conjecture"
  status := ProblemStatus.solved_problem
  resolution_shape := ResolutionShape.prove
  resolution_note :=
    "Perelman's theorem proves the topological three-manifold statement; this repository records `ClayPoincareConjecture` and equivalent closed-curve/`π₁` wordings."
  formalization_note :=
    "Closed simply connected three-manifold statement, with equivalent closed-curve and `π₁` formulations."
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

/-- The six still-open Millennium problem registry entries. -/
def open_problems : List ClayProblem :=
  all_problems.filter ClayProblem.is_open

/-- The solved Millennium problem registry entries. -/
def solved_problems : List ClayProblem :=
  all_problems.filter ClayProblem.is_solved

/-- Count of Clay Millennium problem entries in this registry. -/
theorem all_problems.length_eq : all_problems.length = 7 := by
  native_decide

/-- Count of still-open Clay Millennium problem entries in this registry. -/
theorem open_problems.length_eq : open_problems.length = 6 := by
  native_decide

/-- Count of solved Clay Millennium problem entries in this registry. -/
theorem solved_problems.length_eq : solved_problems.length = 1 := by
  native_decide

end MillenniumProblems
