# A reading guide to the specification and reviews

Start with the [README](../README.md) for the problem and the Lean statement.
Use the [glossary](GLOSSARY.md) when a physics, analysis or formalization term
is unfamiliar. The routes below assume graduate mathematics but do not
require reading every implementation report before understanding the target.

The documents serve different purposes. **Current documents** state the
repository's present claims and checking rules. **Historical reviews** explain
how definitions changed and why particular conditions were adopted. Their
original “incomplete” or “admission closed” conclusions remain evidence about
the reviewed snapshots, not new objections to the current specification.

## Route 1: Understand the current claim

Begin with the [witness audit and open validation questions](WITNESS_AUDIT.md),
then read these in order before interpreting the implementation history.
“Current” means current internal policy, not independently validated fidelity.

| Document | Question it answers |
| --- | --- |
| [Final fidelity argument](FINAL_FIDELITY_ARGUMENT.md) | Why is this proposed formal statement intended to capture the source problem? |
| [Current source crosswalk](CURRENT_JW4_READINESS_CROSSWALK.md) | Where does each source requirement appear in the formal construction? |
| [Requirements](REQUIREMENTS.md) | Which clauses are required, and which are interpretive guidance? |
| [Formalization layers](FORMALIZATION_LAYERS.md) | Which choices are literal source wording, delegated standards or interpretations? |
| [Statement policy](STATEMENT_POLICY.md) | What may the repository claim, and what must remain separate? |
| [Certification contract](../CERTIFICATION.md) | What must a future proof submission satisfy? |
| [Verification record](VERIFICATION_RECORD.md) | Which checks were actually run and what did they report? |
| [Final adversarial review](FINAL_ADVERSARIAL_REVIEW.md) | Which mathematical failure mechanisms were investigated and resolved? |
| [Final admission review](FINAL_ADMISSION_ADVERSARIAL_REVIEW.md) | How were the theorem-shape and axiom checks tested? |

The last two documents preserve staged findings and subsequent repairs.
Read their current disposition before the original conditional conclusions.
None of these documents supplies a Yang–Mills existence proof or external
acceptance.

## Route 2: Learn the physical and mathematical objects

These are historical development notes. Their explanations remain useful;
consult Route 1 for the present status of any obligation they list.

| Document | Read it to understand |
| --- | --- |
| [Source analysis](SOURCE_ANALYSIS.md) | The original source clauses, interpretive choices and source-access limits. |
| [QFT review](QFT_REVIEW.md) | Fields, domains, translations, spectrum and the physical mass gap. |
| [Yang–Mills observable review](YANG_MILLS_REVIEW.md) | Curvature polynomials, gauge invariance and equality on smooth connections. |
| [Composite and stress review](COMPOSITE_STRESS_REVIEW.md) | The map to quantum observables and the tensor whose charges generate translations. |
| [Kernel and cohomology review](KERNEL_BV_COHOMOLOGY_REVIEW.md) | Full correlation distributions and the algebraic quotient of quantum observables. |
| [Canonical trace and carrier review](CANONICAL_TRACE_QFT_REVIEW.md) | Vacuum centering and transport between Hilbert-space presentations. |

## Route 3: Follow the perturbative prescription

The logical progression is action → amplitudes → normalized insertions →
coefficients → physical matching. This is a reading order, not a claim that
each historical file represents the final implementation.

| Document | Main step |
| --- | --- |
| [Perturbative prescription](PERTURBATIVE_PRESCRIPTION.md) | Introduces the equations and source conventions for the whole route. |
| [Bare implementation](PERTURBATIVE_IMPLEMENTATION.md) | Builds action vertices, covariance, contractions and bare insertions. |
| [BRST/BV interface](BRST_BV_INTERFACE.md) | Encodes gauge symmetry, antifields, contact brackets and Ward identities. |
| [Flow implementation](FLOW_IMPLEMENTATION.md) | Fixes graded flow equations and normalization boundaries. |
| [Same-action identities](SAME_ACTION_IDENTITY_REVIEW.md) | Derives symmetry coordinates and connects source insertions by Legendre inversion. |
| [Central bridges](CENTRAL_BRIDGES_REVIEW.md) | Links action, insertion inverse, mixing classes and classical dilation. |
| [Classical basis and BV descent](CLASSICAL_BASIS_BV_DESCENT_REVIEW.md) | Constructs finite classical bases and operations modulo divergences. |
| [Master equation and filtered transport](FILTERED_CME_REVIEW.md) | Relates the action's master equation to broader scale-dependent quantum data. |
| [Fixed-flow uniqueness](FIXED_FLOW_UNIQUENESS_REVIEW.md) | Shows what the fixed equations and boundary data determine. |
| [Differential and OPE transport](ACTUAL_DIFFERENTIAL_OPE_REVIEW.md) | Connects interacting symmetry, integrated responses and coefficient scaling. |
| [Smoothness-order correction](SMOOTH_ORDER_REVIEW.md) | Explains why smooth and analytic hypotheses must be distinguished. |
| [Smooth insertion determinacy](SMOOTH_CANONICAL_INSERTION_REVIEW.md) | Reconstructs amplitudes from canonical data without assuming analyticity. |

## Route 4: Study failure cases and design decisions

These reviews are useful after Routes 1–3: they explain why apparently simpler
conditions can admit unrelated data or impose unjustified extra restrictions.

| Document | Main question |
| --- | --- |
| [Initial adversarial review](ADVERSARIAL_REVIEW.md) | Can a free theory or arbitrary coefficient table pass the early target? |
| [Central adversarial review](CENTRAL_ADVERSARIAL_REVIEW.md) | Are stress, dimensions, running couplings and tensor continuation linked correctly? |
| [Flow adversarial review](FLOW_ADVERSARIAL_REVIEW.md) | Are derivatives, graded signs, extraction and collision limits well-defined? |
| [BV/contact interface review](BV_CONTACT_INTERFACE_REVIEW.md) | Do continuum recovery and local contact data use the same flow? |
| [Local Ward review](LOCAL_WARD_ADVERSARIAL_REVIEW.md) | Can arbitrary spectator dependence hide in distributions at coincidence? |
| [Scale/word interface review](SCALE_WORD_INTERFACE_REVIEW.md) | Do scale equations constrain the actual fields and their vacuum correlations? |
| [Intermediate specification review](SPECIFICATION_REVIEW.md) | Which central links existed before the full renormalized prescription? |
| [Flow specification review](FLOW_SPECIFICATION_REVIEW.md) | How were the flow, Ward, contact and physical-matching components assembled? |
| [Assembled-scope review](ASSEMBLED_SCOPE_REVIEW.md) | Which comparison results are needed to state the problem, and which belong to proving existence? |

## How to read technical evidence

A declaration name identifies a precise Lean definition or theorem. A build
result checks the recorded implementation; it does not by itself establish
agreement with the prose source. Historical file hashes, line numbers and
scratch paths identify the reviewed snapshot and are retained for provenance.
They need not match current line numbers or refer to files distributed with
this checkout.

The abbreviations FH, FHH, IZ, OS and numbered references such as [45] are
explained in the [source-abbreviation table](GLOSSARY.md#notation-and-source-abbreviations).
The [source registry](requirements.json) records the pinned problem statement.
For the distinction between a formal definition, a future proof and external
acceptance, return to the [certification contract](../CERTIFICATION.md).
