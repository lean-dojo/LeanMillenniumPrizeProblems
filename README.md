# Lean Millennium Prize Problem Statements

This repository formalizes the official Clay Mathematics Institute Millennium Prize Problem
statements in Lean 4. It is not a repository of solutions. The goal is to make each statement
precise, reviewable, machine-checkable, and clear about the formalization choices involved.

<center>
<img src="millennium_problems.png" >
</center>

## Quick Start

- Build everything: `lake build`
- Verify local Clay PDFs: `python3 scripts/clay_refs.py verify`
- Problem statements and proof stubs: see the table below
- Checked registry: `Problems/Registry.lean`

The Clay PDFs are stored under `Problems/<Problem>/references/clay/`.

## What This Repo Provides

The main Lean artifacts are statement declarations and final prize theorems:

```lean
def ClayRiemannHypothesis : Prop := ...
```

A `Prop` is the checked mathematical target. It is not a proof and not a claim that the problem is
solved. Each problem module ends with one intentional theorem named `clay_prize_*`. That theorem
spells out the target proposition directly and its body is the exact place to replace `sorry` if
someone formalizes a solution:

```lean
theorem clay_prize_riemann_hypothesis :
    ∀ s : ℂ,
      riemannZeta s = 0 →
        ¬ (∃ n : ℕ, s = -2 * (n + 1)) →
          s ≠ 1 →
            s.re = 1 / 2 := by
  sorry
```

The seven final theorem `sorry`s are intentional. They are not claims that the open problems are
solved. `Problems/Registry.lean` records the statement declaration, the final theorem, status,
resolution shape, and short formalization notes as checked metadata.

This gives the repository a stable lifecycle:

- before a proof exists, the tracked object is the statement `Prop`;
- when a proof exists, replace the body of the matching final `clay_prize_*` theorem;
- if the formalization improves, update the registry note without changing the public statement or
  final theorem names that downstream files import.

## Final Prize Theorems

Each theorem below is placed at the end of its module under `## Main theorem`.

| Problem | File | Statement | Replace this final theorem body |
|---|---|---|---|
| P vs NP | `Problems/PVersusNP/Millennium.lean` | `Millennium.ClayPVersusNP` | `Millennium.clay_prize_p_versus_np` |
| Riemann Hypothesis | `Problems/RiemannHypothesis/Millennium.lean` | `Millennium.ClayRiemannHypothesis` | `Millennium.clay_prize_riemann_hypothesis` |
| Navier-Stokes | `Problems/NavierStokes/Millennium.lean` | `MillenniumNavierStokes.ClayNavierStokes` | `MillenniumNavierStokes.clay_prize_navier_stokes` |
| Hodge Conjecture | `Problems/Hodge/Millennium.lean` | `MillenniumHodge.ClayHodge` | `MillenniumHodge.clay_prize_hodge_conjecture` |
| Birch-Swinnerton-Dyer | `Problems/BirchSwinnertonDyer/Millennium.lean` | `MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer` | `MillenniumBirchSwinnertonDyer.clay_prize_birch_swinnerton_dyer` |
| Yang-Mills mass gap | `Problems/YangMills/HamiltonianSpectrum.lean` | `MillenniumYangMills.ClayYangMills` | `MillenniumYangMills.clay_prize_yang_mills` |
| Poincare Conjecture | `Problems/Poincare/Millennium.lean` | `MillenniumPoincare.ClayPoincareConjecture` | `MillenniumPoincare.clay_prize_poincare_conjecture` |

For P vs NP, the current public statement is the positive outcome `P = NP`. If the final resolution
is `P ≠ NP`, prove `Millennium.ClayPVersusNP.Formulations.NegativeBranch` and update the registry so the public proof target
points at the negative outcome.

## Status And Resolution

The status column is mathematical status. The resolution shape says what a future proof would need
to do with the checked statement.

| Problem | Headline Lean statement | Status | Resolution shape |
|---|---|---|---|
| P vs NP | `Millennium.ClayPVersusNP` | Open | Decide between alternatives |
| Riemann Hypothesis | `Millennium.ClayRiemannHypothesis` | Open | Prove statement |
| Navier-Stokes | `MillenniumNavierStokes.ClayNavierStokes` | Open | Prove one alternative |
| Hodge Conjecture | `MillenniumHodge.ClayHodge` | Open | Prove statement |
| Birch-Swinnerton-Dyer | `MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer` | Open | Prove statement |
| Yang-Mills mass gap | `MillenniumYangMills.ClayYangMills` | Open | Construct object |
| Poincare Conjecture | `MillenniumPoincare.ClayPoincareConjecture` | Solved | Prove statement |

## Formalization Notes

| Problem | Current read |
|---|---|
| P vs NP | Cook verifier/class-equality statement over the repository's finite-alphabet computation model. |
| Riemann Hypothesis | Zeta critical-line statement; xi-zero material records the equivalent `ξ`-function view. |
| Navier-Stokes | Fefferman alternatives (A)-(D), with solution and forcing smoothness stated on `R^3 x [0, infinity)` and pressure periodicity included. |
| Hodge Conjecture | The cycle-class sentence matches the PDF, with assignment-specific and all-coherent-data variants under `Formulations`. |
| Birch-Swinnerton-Dyer | The Taylor rank/order statement follows the PDF's integral Weierstrass model presentation; analytic L-series data is explicit. |
| Yang-Mills mass gap | The canonical Clay target includes a positive finite mass gap; physical-Hamiltonian and Lorentz-covariant strengthenings live under `ClayYangMills.Formulations`. |
| Poincare Conjecture | Closed simply connected 3-manifold statement, with closed-curve and `π₁` forms proved equivalent. |

## Repository Layout

| Path | Purpose |
|---|---|
| `Problems/` | Lean statements, proof stubs, and supporting formalizations. |
| `Problems/Common/` | Shared infrastructure reused across problem files, such as Euclidean coordinate helpers and registry metadata. |
| `Problems/Registry.lean` | Checked registry of status, resolution shape, and formalization notes. |
| `Problems/*/references/clay/` | Local copies of the official Clay PDFs. |
| `scripts/clay_refs.py` | Clay PDF download and verification helper. |

## Release Checks

Before publishing a release, run:

```bash
python3 scripts/clay_refs.py verify
lake build
rg -n "\b(admit)\b|^\s*(axiom|unsafe)\b" Problems -g '*.lean'
rg -n "\bsorry\b" Problems -g '*.lean'
```

The first `rg` command should report no `admit`, `axiom`, or `unsafe` declarations. The second
should report exactly the seven intentional final theorem `sorry`s listed above.

## References

- Clay Millennium Problems overview: https://www.claymath.org/millennium-problems/
- Lean 4: https://leanprover.github.io/
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/

## Contributing

Contributions are welcome, especially changes that replace explicit background interfaces with
mature Lean developments or keep the checked registry aligned with the statement files.
