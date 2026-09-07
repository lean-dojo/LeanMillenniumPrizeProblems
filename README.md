# Millennium Prize Problems in Lean 4

This repository contains Lean 4 formulations of the seven Millennium Prize Problems described by
the Clay Mathematics Institute. It focuses on the problem statements and the mathematics needed to
express them, not on claiming solutions.

<p align="center">
  <img src="millennium_problems.png" alt="The seven Millennium Prize Problems">
</p>

## Getting started

```bash
lake exe cache get   # Mathlib build cache
lake build           # builds the statements (`Problems`) and the checks (`Tests`)
python3 scripts/clay_refs.py verify
```

The second command checks the Lean development. The third verifies the local copies of the official
Clay PDFs. The same three steps run in CI on every push and pull request.

## The seven problems

| Problem | Lean file | Propositions that count as a solution | Status |
|---|---|---|---|
| P versus NP | `Problems/PVersusNP/Millennium.lean` | `Millennium.ClayPVersusNP` (P = NP) or `Millennium.ClayPVersusNP.Formulations.NegativeBranch` (P ≠ NP) | Open |
| Riemann Hypothesis | `Problems/RiemannHypothesis/Millennium.lean` | `Millennium.ClayRiemannHypothesis` | Open |
| Navier–Stokes | `Problems/NavierStokes/Millennium.lean` | any one of `MillenniumNavierStokes.FeffermanA`, `FeffermanB`, `FeffermanC`, `FeffermanD` | Open |
| Birch and Swinnerton-Dyer | `Problems/BirchSwinnertonDyer/Millennium.lean` | `MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer` | Open |
| Poincaré Conjecture | `Problems/Poincare/Millennium.lean` | `MillenniumPoincare.ClayPoincareConjecture` | Solved by Perelman; Lean proof not included |
| Hodge Conjecture | `Problems/Hodge/Millennium.lean` | none | Statement incomplete, not a valid target (see below) |
| Yang–Mills existence and mass gap | `Problems/YangMills/Millennium.lean` | none | Statement incomplete, not a valid target (see below) |

`Problems/Registry.lean` records the same information as checked Lean metadata, including the
status of each statement.

## How to claim a solution

A solution is a `sorry`-free proof of one of the propositions in the table, using only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`; check with `#print axioms`).

- **Riemann, Birch and Swinnerton-Dyer, Poincaré.** Each file ends with a placeholder theorem
  `clay_prize_*` whose body is `sorry`. Replace the body.
- **P versus NP and Navier–Stokes.** These problems ask *which* of several alternatives holds, so
  the alternatives are exposed as separate propositions and there is no placeholder. There is
  deliberately no aggregate declaration either: the disjunction of the alternatives is a classical
  tautology, and an inductive type with one constructor per alternative is inhabited by classical
  case analysis. Both facts are compiled in `Tests/AggregateTargets.lean`, and the Navier–Stokes
  disjunction is proved outright in `Tests/NavierStokes/AggregateIsTrivial.lean` (zero force plus
  the scaling symmetry of the equations, no fluid dynamics).
- **Hodge and Yang–Mills.** Not valid targets until the statements are rewritten; see the next
  section.

## Known incomplete statements

A review in September 2026 (with an independent contribution by Kevin Buzzard, PR #9) found that
two of the formal statements are interface sketches whose data are not pinned down by the stated
properties. Both files carry a warning at the top, both are marked `statement_incomplete` in the
registry, and their former `sorry` placeholders have been removed.

- **Hodge.** Every `SmoothProjectiveVariety ℂ` in the repository has no complex points, because
  `points` must be in bijection with the plain `Scheme` hom-set `Spec ℂ ⟶ X` and also inject into
  a finite projective space, so `ClayHodge` is vacuously true. Independently, the cycle-class map
  is free data: setting it to zero preserves every "canonical" anchor, so `ClayHodge` would become
  false as soon as the first defect were repaired (`Tests/Hodge/CycleClassUnconstrained.lean`).
  A faithful statement needs the analytic topology on `X(ℂ)`, a defined Hodge decomposition and
  cycle-class map, and the rational–complex comparison isomorphism, none of which exist in Mathlib.
- **Yang–Mills.** The quantum-field-theory data are not tied to Yang–Mills theory or to
  relativity: the gauge field stores connection and curvature independently, the Lie algebra has
  no bracket, the Poincaré group is an arbitrary group unrelated to the Hamiltonian, and the
  "unbounded" physical Hamiltonian is tied to the spectrum of a bounded operator. The existence
  statement can therefore be satisfied by a two-dimensional toy model. (Until September 2026 the
  vacuum-uniqueness axiom was also contradictory, which made the theory structure uninhabited;
  that slip is fixed.)

Contributions that replace these sketches with faithful statements are very welcome; they are
substantial projects, not patches.

## Formalization scope

The statements follow the Clay PDFs included in this repository. Some subjects require explicit
interfaces for mathematics that is not yet available directly in Mathlib:

- Navier–Stokes represents Fefferman's four cases (A)–(D) directly. Fields are smooth on the closed
  half-space `ℝ³ × [0,∞)`; the equations and the derivative bounds are imposed on the open
  half-space `t > 0`, because the ambient derivative used in the equations is not meaningful on the
  boundary. The pressure-periodicity erratum is included.
- P versus NP uses a concrete finite-alphabet Turing-machine model and Cook's verifier definition,
  with certificates that are strings over a finite alphabet.
- Birch and Swinnerton-Dyer packages the analytic continuation of the L-series as explicit data;
  the target is existential in that data, so a proof must also supply the continuation and a finite
  rank.
- Riemann is equivalent to Mathlib's `RiemannHypothesis`; Poincaré is equivalent to the shape of
  Mathlib's `proof_wanted` statement.
- Hodge and Yang–Mills are axiomatic sketches, see above.

The detailed choices and related declarations are listed in `Problems/Registry.lean` and documented
inside the corresponding Lean files.

## Tests

The `Tests` library is built by `lake build` and holds compiled facts about the statements:
sanity checks that must keep holding (equivalences with Mathlib statements, axiom audits,
inhabitation of data types), and regression witnesses that show why certain formulations are not
targets. A regression witness is expected to stop compiling when the statement it exposes is fixed.

## Repository layout

| Path | Contents |
|---|---|
| `Problems/` | The seven statements and their supporting definitions |
| `Problems/Common/` | Definitions shared by several problems |
| `Problems/Registry.lean` | A checked index of the problems, their status, and related declarations |
| `Problems/*/references/clay/` | Local copies of the official Clay PDFs |
| `Tests/` | Compiled sanity checks and regression witnesses |
| `scripts/clay_refs.py` | Downloads or verifies the Clay PDFs |
| `.github/workflows/ci.yml` | Continuous integration: build and PDF verification |

## History of statement fixes

- 2026-04: Navier–Stokes vacuous-domain loophole closed after issue #4.
- 2026-06: Navier–Stokes aggregate disjunction removed after issue #5 (it was reintroduced in
  July and removed again in September).
- 2026-09: independent review. Smoothness order fixed to `C^∞` (PR #7); Yang–Mills locality
  direction fixed (PR #8); Navier–Stokes equations moved to the open half-space; P versus NP
  certificate encoding fixed (every language was in NP); Yang–Mills vacuum-uniqueness axiom fixed;
  Birch–Swinnerton-Dyer auxiliary formulations with empty data types removed or weakened; Hodge
  and Yang–Mills demoted to `statement_incomplete`; `Tests` library and CI added.

## References

- [Clay Mathematics Institute: Millennium Problems](https://www.claymath.org/millennium-problems/)
- [Lean 4](https://leanprover.github.io/)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)

## Contributing

Contributions that improve the accuracy of the statements, replace temporary mathematical
interfaces with native Mathlib constructions, add tests, or provide formal proofs are welcome.
Statement changes should come with a test in `Tests/` showing that the new statement is not
trivially provable or refutable.
