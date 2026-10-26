# Yang–Mills existence and mass gap: a proposed Lean specification

This repository proposes a precise, machine-checkable statement of the
**Yang–Mills existence and mass-gap problem** in Lean. It contains the
specification, supporting mathematical lemmas and tools for checking a future
proof. **It does not contain an existence proof or an independently validated
formalization of the source problem.** Its fidelity arguments are internal,
AI-assisted assessments. No independent human expert validation is documented.
Whether the combined definitions are too weak or too strong remains a question
for mathematical review.

AI agents contributed substantially to the formulation and implementation;
see the [AI disclosure](#6-ai-disclosure) for their role and the limits of review.

For evaluation, start with the [witness-constraint audit and open review questions](source/WITNESS_AUDIT.md).
It distinguishes checked consequences, structural links and untested
countermodel challenges. File names containing `FINAL` or `READINESS` identify
internal workflow stages, not external certification.

This guide assumes graduate-level mathematics, including some familiarity
with Hilbert spaces and Lie groups. No prior Lean experience is needed to
read the overview. Start with the problem, then read the formal statement
and its requirements before exploring the implementation. The
[document map](source/DOCUMENTATION_GUIDE.md) gives reading routes through the
remaining notes; the [glossary](source/GLOSSARY.md) explains recurring terms
and notation with links to their technical sources.

## 1. What is the mathematical problem?

A Yang–Mills theory describes gauge fields: fields whose mathematical
representation has a local symmetry specified by a **gauge group**. The
challenge is to construct a rigorous quantum field theory (QFT) in four
spacetime dimensions and prove that its vacuum is separated from excited
states by a positive energy gap. The primary statement is Jaffe and Witten,
[*Quantum Yang–Mills Theory*, §4](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf#page=6);
§§1–3 introduce the physical and mathematical background.

In this specification, the **Hamiltonian** is the self-adjoint operator that
generates time evolution. Its vacuum has energy zero. A **mass gap** means
that some interval `(0, Δ)`, with `Δ > 0`, contains no Hamiltonian spectrum.
The spectral mass is the supremum of such gap sizes and must be finite and
positive. The spectrum above the gap may be continuous; an isolated particle
state is not required. See the repository's
[precise spectral interpretation](source/FINAL_FIDELITY_ARGUMENT.md#complete-physical-framework).

The group ranges over compact connected Lie groups with simple nonabelian
Lie algebra. Here “simple” describes the Lie algebra, rather than simplicity
as an abstract group; the
[group-scope discussion](source/CURRENT_JW4_READINESS_CROSSWALK.md#global-groups-and-local-observable-scope)
explains this distinction and the allowed groups.

## 2. How to read the Lean statement

The target is `YangMills.YangMillsExistenceAndMassGap.{u}`, defined in
[YangMillsSpecification.lean](YangMills/YangMillsSpecification.lean):

```lean
def YangMillsExistenceAndMassGap : Prop :=
  ∀ G : CompactSimpleGaugeGroup.{u}, Nonempty (FilteredGeneratedCandidate G)
```

Read this as: **for every allowed gauge group `G`, there exists a candidate
quantum theory satisfying all of the specified requirements for that group.**

| Lean expression | Mathematical meaning |
| --- | --- |
| `def … : Prop :=` | Defines a proposition. This line states the problem; it does not prove it. |
| `∀ G : CompactSimpleGaugeGroup.{u}` | For every group in the specified class. |
| `FilteredGeneratedCandidate G` | A collection of mathematical objects and proofs of their required properties for `G`. |
| `Nonempty (…)` | At least one such collection exists. |
| `.{u}` | A universe parameter, allowing the statement to apply across Lean's hierarchy of type sizes. See [Lean's universe reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/). |

A **witness** is one such collection of objects together with the required
proofs. Defining the type of witnesses does not construct a witness. A future
existence proof must establish `Nonempty` for every allowed `G`.

The candidate's name reflects two design choices: “filtered” means that
observables are organized by dimension bounds, and “generated” means that
the perturbative predictions come from a fixed prescription. Its fields are
listed in [FilteredGeneratedCandidate.lean](YangMills/FilteredGeneratedCandidate.lean).

## 3. What must a candidate contain?

The central requirement is consistency across the whole construction: the
group, action, quantum fields, short-distance predictions, stress tensor and
Hamiltonian must describe the **same theory**. The definitions fix their
relationships; a future proof must satisfy those definitions. This fixes a
formal proposition, but does not establish that its predicates capture
Yang–Mills. The [audit map](source/WITNESS_AUDIT.md#witness-freedom-and-where-it-is-constrained)
shows what the prover supplies and where the constraints are imposed.

1. **A physical quantum field theory.** The specification uses the
   **Wightman framework**: quantum fields on a positive Hilbert space,
   subject to locality, spacetime symmetry, positive energy and vacuum
   conditions. Fields share a dense domain preserved by their action.
   The full hierarchy of vacuum correlation functions—expectation values
   of products of fields—is tied to those fields. The
   [framework comparison](source/CURRENT_JW4_READINESS_CROSSWALK.md#complete-qft-presentation-comparison)
   gives the precise conditions and source references.

2. **Observables belonging to Yang–Mills for the chosen group.**
   A **composite observable** is a local expression built from fields and
   their derivatives. The classical expressions here use curvature and
   covariant derivatives, and are invariant under gauge transformations.
   Their quantum counterparts respect classical identities and derivatives,
   while allowing quantum relations and **operator mixing**: linear
   combinations introduced in defining renormalized observables. Acting
   with these observables on the vacuum generates a dense subspace of the
   physical Hilbert space. See
   [the observable correspondence](source/FINAL_FIDELITY_ARGUMENT.md#same-observables-predictions-and-stress).

3. **The prescribed short-distance behavior.** **Ultraviolet (UV)** means
   short-distance or high-energy behavior. **Renormalization-group (RG)
   flow** describes how parameters and observables change with scale.
   The **operator product expansion (OPE)** describes products of nearby
   observables through local observables and coefficient functions.
   This repository fixes the perturbative coefficients and requires the
   physical theory to match them. Background is provided by
   [Fröb, Holland and Hollands on correlation functions](https://arxiv.org/abs/1511.09425)
   and [Fröb and Holland on the OPE](https://arxiv.org/abs/1603.08012).

4. **A compatible stress tensor and a positive finite mass gap.** The
   **stress-energy tensor** describes local energy and momentum; its
   charges must generate the same translations as the physical theory.
   The gap belongs to that theory's full Hamiltonian. The stress tensor
   also satisfies the specified **trace anomaly**, a quantum correction
   to the classical scaling relation. Both sides are vacuum-centered:
   their actual vacuum expectation values are subtracted, fixing the
   scalar identity contribution. See
   [the stress and trace conditions](source/FINAL_FIDELITY_ARGUMENT.md#same-observables-predictions-and-stress).

### What does “all orders” mean here?

**Perturbation theory** computes coefficients order by order in a coupling
parameter. Here, matching to all orders means that every finite truncation
has a controlled remainder as the running coupling tends to zero. It does
not require the infinite series to converge at a fixed coupling.

Smooth functions with the prescribed expansion are allowed, including
**flat terms**: contributions whose derivatives at zero all vanish and
therefore cannot be detected by the expansion. The fixed auxiliary Gaussian
flow supplies the perturbative predictions; it does not prescribe how to
construct the full quantum theory beyond perturbation theory. These choices
are detailed in the [fidelity argument](source/FINAL_FIDELITY_ARGUMENT.md#actual-yangmills-action-and-prescription).

Consequently, perturbative matching alone does not uniquely identify a
nonperturbative theory. Composite cyclicity excludes an invisible extra sector,
and a checked theorem excludes identically zero stress in a candidate; neither
is a general exclusion theorem for massive free or generalized-free theories.
Such an exclusion for the full target has not been established here. See the
[countermodel review tasks](source/WITNESS_AUDIT.md#countermodel-tests-and-their-present-status).

For readers following the implementation, that argument also covers
**jets** (derivative data), the finite Fourier/Taylor prescription and the
proofs determining smooth insertion responses. The physical stress dictionary
has engineering dimension bound four; its **BRST** response has a separate
bound of five. BRST (Becchi–Rouet–Stora–Tyutin) is the differential encoding
gauge symmetry in the auxiliary formalism; see
[Fröb, Holland and Hollands](https://arxiv.org/abs/1511.09425).
These details are explained in the
[stress discussion](source/FINAL_FIDELITY_ARGUMENT.md#same-observables-predictions-and-stress).

## 4. Build and check the repository

Install Lean using the [official setup guide](https://lean-lang.org/install/)
and have Python 3 available. From the repository root, run:

```sh
lake build
python3 scripts/check_proofs.py
python3 scripts/verify_submission.py --claim specification
```

`lake` is Lean's build tool. The pinned Lean version is in
[lean-toolchain](lean-toolchain), and the pinned mathlib dependency (Lean's
mathematical library) is recorded in [lake-manifest.json](lake-manifest.json).

| Command | What it checks |
| --- | --- |
| `lake build` | Compiles the library and checks its declarations. |
| `python3 scripts/check_proofs.py` | Builds the specification and runs proof-audit regression checks. |
| `python3 scripts/verify_submission.py --claim specification` | Checks specification admission, including the compiled target's exact shape; on success, reports `SPECIFICATION_READY`. |

`SPECIFICATION_READY` is the verifier's internal admission status: its configured
source, build and target-shape checks passed with internal review activation.
It does not certify semantic fidelity, independent expert approval or an existence proof.
Running the verifier with `--claim yangmills` and no submission reports
`PROOF_NOT_SUBMITTED`.

### Submitting a future proof

```sh
python3 scripts/verify_submission.py --claim yangmills --proof-file proof.lean --theorem MyProof.solution
```

The submitted declaration must be an unconditional theorem of the exact
target, with one universe parameter. A separate process inspects the compiled
environment and all axioms on which the proof depends, including dependencies
through other declarations. Only Lean's standard foundations `propext`,
`Classical.choice` and `Quot.sound` are allowed; see
[Lean's axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/).
Fixed-universe, conditional, assumed, wrong-type and `sorry`-based claims
(`sorry` is a placeholder for an unfinished proof) are rejected.

The separate `--claim qft` mode checks only the QFT proposition. The legacy
`--claim clay` spelling is an alias for mathematical proof checking. The
verifier always reports `clay_certificate=false`, even after a future accepted
exact-target proof. See the [certification contract](CERTIFICATION.md).

## 5. Reading path and review limits

For a closer mathematical review, read these in order:

1. [Witness audit](source/WITNESS_AUDIT.md): constraints, evidence limits and
   concrete unresolved review tasks.
2. [Internal fidelity argument](source/FINAL_FIDELITY_ARGUMENT.md): why the
   proposed definitions are intended to capture the source problem.
3. [Internal source crosswalk](source/CURRENT_JW4_READINESS_CROSSWALK.md):
   how each source requirement maps to the formal construction.
4. [Internal adversarial review](source/FINAL_ADVERSARIAL_REVIEW.md): challenges
   to the specification and their recorded resolutions.
5. [Statement policy](source/STATEMENT_POLICY.md) and
   [certification contract](CERTIFICATION.md): the scope of claims and checks.

The [source registry](source/requirements.json) records citations and source
identity; [provenance classifications](source/FORMALIZATION_LAYERS.md)
distinguish literal source requirements from interpretive choices. Earlier
review files preserve historical findings. Use the current documents above
for the repository's readiness assessment.

The previously unavailable sources were supplied on 22 October 2026.
[Streater–Wightman Chapter 3](source/SOURCE_ANALYSIS.md#direct-streaterwightman-reading-22-october-2026),
“Fields and Vacuum Expectation Values,” pp.96–133, has now been read and
compared with the Wightman definitions using the **2000 reissue**, rather than
the cited 1964 printing. A [scoped reading of OS II](source/SOURCE_ANALYSIS.md#direct-os-ii-reading-22-october-2026)
also records its corrected reconstruction conditions. These readings close
the access gaps, not the fidelity question: the source record lists remaining
convention and equivalence obligations and the limits of review.

Lean's **kernel** is the core proof checker. Kernel acceptance establishes a
proof relative to the formal statement and its foundations. Fidelity to the
source prose and external mathematical acceptance are separate judgments;
a successful build or an agent review does not establish either.

The artifact's present use is as an inspectable proposal for constructive and
axiomatic QFT specialists and Lean formalizers to criticize or revise. Repository
age, commit count, stars, model settings and documentation volume are not evidence
of mathematical correctness. Clay eligibility is a separate process: its
[official rules](https://www.claymath.org/millennium-problems/rules/) require
publication in a qualifying outlet, at least two years since publication, and
general acceptance in the global mathematics community before consideration.

## 6. AI disclosure

AI agents contributed to the mathematical formulation, Lean implementation,
verification tooling and documentation. Their contribution includes substantive
choices about how to express the source problem, not just code completion or
copy-editing.

### Recorded models and development phases

The following attribution comes from the local Codex session and turn metadata
for this repository, inspected on 22 October 2026. Model names are the exact
identifiers recorded there; reasoning effort is a session setting.

| Development phase | Recorded dates | Recorded model | Reasoning effort |
| --- | --- | --- | --- |
| Initial Lean Yang–Mills statement | 16 October 2026 | `gpt-6-astra` | `low` |
| Specification completion and admission work | 19–20 October 2026 | `gpt-6-astra` | `medium` |
| Pedagogical documentation revision and disclosure | 21–22 October 2026 | `gpt-6-astra` | `medium` |

These records identify the coordinating sessions. The development reports also
record delegated implementation and review agents, but the inspected records
do not establish a complete model roster for those agents. We therefore do not
attribute every delegated contribution to this model or claim that reviews used
different model families. The repository does not contain a complete per-file
or per-line model-attribution log.

Separately, the user attributed the structural critique supplied on 22 October
2026 to **Claude Sonnet 5.5**, with **medium** reasoning effort. This attribution
is user-reported, not verified from session metadata. That review covered the
README and `FilteredGeneratedCandidate.lean`; the reviewer explicitly did not
audit the imported definitions or establish their correctness. The
[witness-constraint audit](source/WITNESS_AUDIT.md) responds to that critique.
This is a reported review by another model family, not human expert validation.

### Coverage of AI contributions

AI assistance extended across the following areas. The links identify the
relevant artifacts and development records; they are not claims that every
line in a linked file was AI-generated.

| Area | AI-assisted work | Coverage and evidence |
| --- | --- | --- |
| Source interpretation and specification design | Analyzing the Jaffe–Witten requirements, choosing formal presentations, identifying missing conditions and assembling the all-group target. | [Source analysis](source/SOURCE_ANALYSIS.md), [fidelity argument](source/FINAL_FIDELITY_ARGUMENT.md), [target definition](YangMills/YangMillsSpecification.lean). |
| Mathematical implementation and supporting proofs | Writing and revising Lean definitions and lemmas for the physical QFT and spectrum, classical observables, perturbative flow, BRST/BV symmetry, OPE/RG matching and stress tensor. | [QFT review](source/QFT_REVIEW.md), [flow implementation](source/FLOW_IMPLEMENTATION.md), [same-action proofs](source/SAME_ACTION_IDENTITY_REVIEW.md), [assembled candidate](YangMills/FilteredGeneratedCandidate.lean). |
| Adversarial mathematical review | Testing proposed conditions for inconsistent conventions, unjustified restrictions, unrelated-theory loopholes and missing links between mathematical objects; proposing and inspecting repairs. | [Central review](source/CENTRAL_ADVERSARIAL_REVIEW.md), [local Ward review](source/LOCAL_WARD_ADVERSARIAL_REVIEW.md), [final review](source/FINAL_ADVERSARIAL_REVIEW.md). |
| Verification tooling and execution | Developing proof-admission checks and regression tests, running builds and axiom audits, and recording rejection cases and results. | [Verifier](scripts/verify_submission.py), [compiled-environment inspector](scripts/InspectProof.lean), [verification record](source/VERIFICATION_RECORD.md). |
| Documentation | Drafting source comparisons and review reports, then revising all 37 existing Markdown files for graduate-level readability and adding a glossary and reading guide. | [Glossary](source/GLOSSARY.md), [reading guide](source/DOCUMENTATION_GUIDE.md), and the Markdown review collection in `source/`. |

This is a description of work areas, not a measured percentage of AI authorship
or a claim of exhaustive mathematical review. It does not attribute Lean,
mathlib or the cited mathematical literature to these agents.

### What the review and checks establish

“Independent review” in the development records refers to a separate agent
review role within the workflow. It should not be read as independent human
expert review, review by a different model family, or external endorsement.
AI-generated interpretations and reviews can be mistaken; agreement between
agents does not establish fidelity to the source problem.

Lean checks formal declarations and proofs against their stated definitions
and foundations. It does not certify that those definitions faithfully capture
the prose problem. The [verification record](source/VERIFICATION_RECORD.md)
reports the checks performed and their limits. This repository presents a
proposed specification and supporting proofs, not a Yang–Mills existence
proof, and makes no claim of external mathematical acceptance.
