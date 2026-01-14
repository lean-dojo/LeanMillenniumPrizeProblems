# Lean Millennium Prize Problem statements

This repository focuses on **formalizing the official Clay Mathematics Institute Millennium Prize
Problem statements** in Lean 4 (Mathlib). It is *not* a repository of solutions; the goal is to
make each problem statement precise and machine-checkable.

<center>
<img src="millennium_problems.png" >
</center>

## Quick Start

- Build everything: `lake build`
- Problem statements live in: `Problems/<Problem>/Millennium.lean`
- Official Clay PDFs live in: `Problems/<Problem>/references/clay/`

To (re)download or verify that the PDFs exist locally, use `scripts/clay_refs.py`
(see `scripts/README.md`).

## Design Goals

- Keep the repository **`sorry`-free** and **free of user `axiom`s**.
- When Mathlib does not yet provide enough foundations (common in analysis/QFT), we avoid “fake”
  placeholders by **parameterizing** statements over explicit *data packages* that record the
  required objects/properties.
- Prefer statements that match the wording of the Clay PDFs, with the PDF stored alongside the
  formalization for easy review.

## Safety Checks

This branch has been checked with [SafeVerify](https://github.com/GasStationManager/SafeVerify) on the compiled
`.olean` files for all modules under `Problems/**` (self-check), replaying declarations in the kernel and
enforcing SafeVerify’s restrictions (no `unsafe`/`partial` declarations and no axioms beyond `propext`,
`Quot.sound`, `Classical.choice`).

## What’s Implemented

Each problem folder contains a `Millennium.lean` that states the Clay problem precisely, plus
supporting files with definitions/lemmas needed to express that statement.

Some “narrative” examples mentioned in the PDFs (e.g. AKS: `PRIME ∈ P`, Cook–Levin: `SAT` is
NP-complete) are not currently formalized as Lean theorems; formalizing them would require major
additional developments in complexity theory within Mathlib.

## Status (per problem)

This repo focuses on *problem statements*, so “status” below refers to how fully each Clay PDF has
been turned into Lean definitions/theorems (not whether the underlying conjecture is proved).

**Legend**
- Status:
  - **Statement**: the Clay statement is expressed as a Lean `Prop` with supporting definitions.
  - **Parameterized**: the statement is expressed, but depends on an explicit “data package” that
    stands in for missing Mathlib foundations (keeps the repo `axiom`-free).
  - **Mathlib**: the statement is already in Mathlib (and may be proved there); this repo restates it.
- Clay fidelity:
  - **Direct**: close translation of the Clay PDF statement (modulo routine formalization choices).
  - **Parameterized**: same mathematical shape as the PDF, but some objects/maps are parameters.
  - **Modeled**: uses a Lean-level proxy for a PDF concept that is not yet formalized (e.g. spectra
    of unbounded operators).

| Problem | Main Lean statement | Location | Status | Clay fidelity |
|---|---|---|---|---|
| P vs NP | `Millennium.PEqualsNP` | `Problems/PvsNP/Millennium.lean` | Statement | Direct |
| Riemann Hypothesis | `Millennium.RiemannHypothesis` | `Problems/RiemannHypothesis/Millennium.lean` | Statement | Direct |
| Navier–Stokes | `MillenniumNavierStokes.NavierStokesMillenniumProblem` | `Problems/NavierStokes/Millennium.lean` | Statement | Direct |
| Hodge Conjecture | `MillenniumHodge.HodgeConjecture` | `Problems/Hodge/Millennium.lean` | Parameterized | Parameterized |
| Birch–Swinnerton–Dyer | `MillenniumBirchSwinnertonDyer.BirchSwinnertonDyerConjecture` | `Problems/BirchSwinnertonDyer/Millennium.lean` | Parameterized | Parameterized |
| Yang–Mills mass gap | `MillenniumYangMills.YangMillsExistenceAndMassGap` | `Problems/YangMills/Millennium.lean` | Parameterized | Modeled |
| Poincaré Conjecture | `MillenniumPoincare.PoincareConjecture3` | `Problems/Poincare/Millennium.lean` | Mathlib | Direct |

<details>
<summary>P vs NP: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/PvsNP/references/clay/pvsnp.pdf`
- What’s formalized:
  - `P`/`NP` as languages over finite alphabets (`List alphabet`), using Cook’s verifier-based `NP`
    definition (`Millennium.InNP`) and deterministic polynomial-time TM2 computability (`Millennium.InP`).
  - Polynomial-time many-one reductions (`Millennium.PolyTimeReducible`) and `NP`-completeness (`Millennium.NPComplete`).
  - Several basic “Cook Proposition 1” implications (closure under reduction, etc.).
- What’s still narrative / external:
  - Concrete `NP`-complete problems (`SAT`, `3SAT`, …) and the Cook–Levin theorem.
  - Worked examples mentioned in the PDF (AKS primality, etc.).
  - Equivalences between different complexity models (e.g. nondeterministic TM vs verifier definition).
</details>

<details>
<summary>Riemann Hypothesis: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/RiemannHypothesis/references/clay/riemann.pdf`
- What’s formalized:
  - The Clay statement as `Millennium.RiemannHypothesis`, with an equivalence lemma to Mathlib’s
    `_root_.RiemannHypothesis`.
  - Several standard narrative facts reused from Mathlib (Dirichlet series/Euler product on `Re(s) > 1`,
    residue at `s = 1`, completed zeta functional equation, Chebyshev functions, …).
- What’s still narrative / external:
  - Most of the “equivalent formulations” and prime-number-theory consequences discussed in the PDF.
</details>

<details>
<summary>Navier–Stokes: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/NavierStokes/references/clay/navierstokes.pdf`
- What’s formalized:
  - Fefferman’s hypotheses and statements (A)–(D), with a single entry point in
    `Problems/NavierStokes/Millennium.lean` and details split across:
    `Problems/NavierStokes/MillenniumRDomain.lean` (A,C) and
    `Problems/NavierStokes/MillenniumBoundedDomain.lean` (B,D + disjunction).
  - A lightweight PDE scaffold (`Problems/NavierStokes/Navierstokes.lean`) for (global) smooth solutions.
- Notable formalization choices:
  - Multi-indices are represented as lists of coordinate directions (slightly stronger than commutative multi-indices).
  - “Smooth” is `ContDiff ℝ ⊤`.
- What’s still narrative / external:
  - The analytic existence/uniqueness/regularity theory itself (this repo only states the problem).
</details>

<details>
<summary>Hodge Conjecture: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/Hodge/references/clay/hodge.pdf`
- What’s formalized:
  - The conjecture statement `MillenniumHodge.HodgeConjecture`, parameterized by `HodgeData`
    (`Problems/Hodge/Variety.lean`) bundling the cycle class map / Hodge decomposition interfaces.
- What’s still missing in Mathlib (hence parameterized here):
  - Construction of singular cohomology for complex varieties, the cycle class map, and the Hodge decomposition
    in the generality used by the Clay write-up.
</details>

<details>
<summary>Birch–Swinnerton–Dyer: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/BirchSwinnertonDyer/references/clay/birchswin.pdf`
- What’s formalized:
  - The rank part as `MillenniumBirchSwinnertonDyer.BirchSwinnertonDyerConjecture`, phrased via
    `analyticOrderAt` at `s = 1`.
  - A refined-formula variant as `MillenniumBirchSwinnertonDyer.RefinedBirchSwinnertonDyerConjecture`
    (still “data-only” for the arithmetic invariants).
- What’s still missing in Mathlib (hence parameterized here):
  - Construction/analytic continuation of the Hasse–Weil `L`-function for elliptic curves; this is abstracted
    as `MillenniumBirchSwinnertonDyer.ClayLSeriesData`.
</details>

<details>
<summary>Yang–Mills: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/YangMills/references/clay/yangmills.pdf`
- What’s formalized:
  - A Lean formulation `MillenniumYangMills.YangMillsExistenceAndMassGap` in terms of a bundled
    `QuantumYangMillsTheory` satisfying Wightman-style axioms (`Problems/YangMills/Quantum.lean`).
- Notable formalization choices (modeling gaps):
  - The Clay “mass gap” is phrased using Mathlib’s `spectrum` of a (bounded) Hamiltonian operator, which is
    a stand-in for the unbounded spectral theory used in physics.
- What’s still narrative / external:
  - Constructing any non-trivial 4D QFT meeting these axioms, and proving the (modeled) mass gap.
</details>

<details>
<summary>Poincaré Conjecture: what’s in Lean vs. still missing</summary>

- Clay PDF: `Problems/Poincare/references/clay/poincare.pdf`
- What’s formalized:
  - The (topological) 3D statement as `MillenniumPoincare.PoincareConjecture3`.
  - Mathlib already contains a proof; this repo mainly provides a Clay-aligned entry point and references.
</details>

## Installation

To install Lean, follow the instructions at [the Lean website](https://leanprover.github.io/).

## Folder Structure

The main code is under `Problems/`. Each subfolder corresponds to one Millennium Prize Problem.

## References

- Clay Millennium Problems overview: https://www.claymath.org/millennium-problems/
- Lean 4: https://leanprover.github.io/
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/

## Contributing

Contributions are welcome — especially improvements that make the formal statements closer to the
Clay PDFs, or that replace “external results” with genuine Lean developments and proofs.
