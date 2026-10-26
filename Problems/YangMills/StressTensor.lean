import Problems.YangMills.CompositeFields
import Problems.YangMills.Nontriviality

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Same-theory conserved stress tensor and physical translation charges

This fixes a concrete stress-tensor interpretation; it is not a proof that
such a tensor exists in Yang--Mills. Operators are dimension-four renormalized composites under the *same*
correspondence. Their leading perturbative symbol must separately be linked
to the classical stress tensor by the fixed perturbative prescription; exact
equality to the classical traceless polynomial would forbid the trace anomaly. Symmetry, tensor covariance, distributional conservation, and
weak spatially smeared charge limits are fixed statements.

No sharp-time restriction of an operator-valued distribution is used. The
charge limits use Schwartz time smearing with unit integral and spatial
cutoffs tending to one, and hold on a common core for the actual translation
generators. Core density is in the graph topology, not just Hilbert norm.
-/
noncomputable section
open MeasureTheory Filter
namespace YangMills

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Coordinate derivative as an actual continuous map of Schwartz spaces. -/
def partialTest (μ : Fin 4) : TestFunction →L[ℂ] TestFunction :=
  LineDeriv.lineDerivOpCLM (V := Spacetime) ℂ TestFunction (Pi.single μ 1)

@[simp] theorem partialTest_apply (μ : Fin 4) (f : TestFunction) (x : Spacetime) :
    partialTest μ f x = fderiv ℝ f x (Pi.single μ 1) := rfl

/-- The diagonal entries of the fixed (+---) metric. -/
def metricSign (μ : Fin 4) : ℝ := if μ = 0 then 1 else -1

/-- Contravariant classical Yang--Mills stress tensor, with the same
curvature as the action and invariant form B. The signs make T00 positive
for the (+---) convention. The positive coupling fixes its normalization. -/
def classicalStress {G : CompactSimpleGaugeGroup} (B : InvariantForm G)
    (coupling : ℝ) (A : Connection G) (x : Spacetime) (μ ν : Fin 4) : ℝ :=
  coupling⁻¹ ^ 2 *
    (-(metricSign μ * metricSign ν) *
        ∑ ρ : Fin 4, metricSign ρ * B.bilinear (A.curvature x μ ρ) (A.curvature x ν ρ) +
      (if μ = ν then metricSign μ / 4 else 0) *
        ∑ ρ : Fin 4, ∑ σ : Fin 4,
          metricSign ρ * metricSign σ * B.bilinear (A.curvature x ρ σ) (A.curvature x ρ σ))

/-- Momentum operators are not a freely chosen convenient spectrum. Their
full domains/actions must be exactly those of Q's coordinate translations. -/
structure TranslationGenerators (Q : WightmanData H) where
  operator : Fin 4 → DenselyDefinedOperator H

namespace TranslationGenerators
variable {Q : WightmanData H}

structure Compatible (P : TranslationGenerators Q) : Prop where
  /-- The time component is literally the Hamiltonian already used for the gap. -/
  time : P.operator 0 = Q.hamiltonian
  selfAdjoint : ∀ μ, (P.operator μ).IsSelfAdjoint
  domain : ∀ μ v,
    (∃ w : H, HasDerivAt
      (fun t : ℝ => Q.unitary (PoincareTransform.translate (Pi.single μ t)) v) w 0) ↔
      v ∈ (P.operator μ).domain
  action : ∀ μ (v : (P.operator μ).domain), HasDerivAt
    (fun t : ℝ => Q.unitary (PoincareTransform.translate (Pi.single μ t)) (v : H))
    (Complex.I • (P.operator μ).toLinearMap v) 0

end TranslationGenerators

abbrev SpatialTestFunction := SchwartzMap (Fin 3 → ℝ) ℂ
abbrev TemporalTestFunction := SchwartzMap ℝ ℂ

/-- Profiles are witness data but their meanings are pointwise fixed below.
Existence of admissible profiles is required, preventing vacuous universal
quantification over a possibly empty class of cutoffs. -/
structure ChargeSmearing where
  temporal : TemporalTestFunction
  spatial : SpatialTestFunction
  test : ℝ → TestFunction

namespace ChargeSmearing

structure Admissible (s : ChargeSmearing) : Prop where
  temporal_real : ∀ t, (s.temporal t).im = 0
  spatial_real : ∀ x, (s.spatial x).im = 0
  temporal_compact : IsCompact (tsupport s.temporal)
  spatial_compact : IsCompact (tsupport s.spatial)
  unit_integral : (∫ t : ℝ, s.temporal t) = 1
  equals_one : ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1 → s.spatial x = 1
  /-- No totalized-integral loophole in the normalized time smearing. -/
  temporal_integrable : Integrable s.temporal
  /-- Unnormalized spatial cutoff; it tends to one rather than a delta.
  The value at nonpositive radius is irrelevant to the atTop limit. -/
  factorization : ∀ R : ℝ, 0 < R → ∀ x : Spacetime,
    s.test R x = s.temporal (x 0) * s.spatial (fun i : Fin 3 => x i.succ / R)

end ChargeSmearing

/-- Tensor data use the exact composite correspondence C and physical Q.
The labels belong to the same G-dependent composite algebra. Their
physical stress-tensor meaning is fixed by covariance, conservation and
normalization to actual translations, rather than a trace-anomaly-breaking
equality to the classical traceless expression. -/
structure StressTensorData (Q : WightmanData H) (G : CompactSimpleGaugeGroup)
    (C : RenormalizedCompositeMap Q G) where
  traceForm : InvariantForm G
  coupling : {g : ℝ // 0 < g}
  scale : RenormalizationScale
  label : Fin 4 → Fin 4 → CurvatureJetPolynomial.invariantAlgebra G
  translations : TranslationGenerators Q
  /-- The core is contained in Q's original common operator domain. -/
  chargeCore : Submodule ℂ Q.domain
  smearing : ChargeSmearing

namespace StressTensorData

variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
  {C : RenormalizedCompositeMap Q G}

/-- Actual stress-tensor operator-valued distribution on Q's common domain. -/
def field (T : StressTensorData Q G C) (μ ν : Fin 4) :
    TestFunction →ₗ[ℂ] Q.domain →ₗ[ℂ] Q.domain :=
  C.field T.scale (T.label μ ν)

/-- Fixed stress-tensor obligations, including its identity as Q's generator.
Improvement and finite mixing remain possible through C; trace zero is
intentionally not required (the quantum trace anomaly is not excluded). -/
structure Compatible (T : StressTensorData Q G C) : Prop where
  correspondence : C.Compatible
  generators : T.translations.Compatible
  admissible_smearing : T.smearing.Admissible
  dimension_four : ∀ μ ν,
    intrinsicEngineeringDimension (T.label μ ν) ≤ 4
  symmetry : ∀ μ ν f v, T.field μ ν f v = T.field ν μ f v
  /-- Distributional divergence is zero: derivatives act on Schwartz tests,
  so this never multiplies unsmeared field distributions. -/
  conservation : ∀ ν f v, ∑ μ : Fin 4, T.field μ ν (partialTest μ f) v = 0
  /-- Rank-two contravariant tensor transformation, in the convention
  U(g) T(x) U(g)^-1 = Lambda^-1 T(g.x) Lambda^-T. -/
  covariance : ∀ g μ ν f v,
    Q.domainAction g (T.field μ ν f v) =
      ∑ ρ : Fin 4, ∑ σ : Fin 4,
        (((g.lorentz.linear.symm (Pi.single ρ 1) μ) *
          (g.lorentz.linear.symm (Pi.single σ 1) ν) : ℝ) : ℂ) •
          T.field ρ σ (Q.pullback g f) (Q.domainAction g v)
  core_domain : ∀ μ (v : T.chargeCore),
    ((v : Q.domain) : H) ∈ (T.translations.operator μ).domain
  /-- Graph approximation makes the core determine the entire physical
  operator. Density only in Hilbert norm would not exclude a restriction. -/
  graph_core : ∀ μ (v : (T.translations.operator μ).domain),
    ∃ sequence : ℕ → T.chargeCore,
      Tendsto (fun n => ((sequence n : Q.domain) : H)) atTop (nhds (v : H)) ∧
      Tendsto (fun n => (T.translations.operator μ).toLinearMap
        ⟨((sequence n : Q.domain) : H), core_domain μ (sequence n)⟩)
        atTop (nhds ((T.translations.operator μ).toLinearMap v))
  /-- Weak global charges reproduce the *actual* translation operators,
  with metric signs required by U(a)=exp(i P dot a).
  in particular the Hamiltonian whose spectrum defines the mass. -/
  charge_limit : ∀ μ (u : T.chargeCore) (v : Q.domain),
    Tendsto (fun R : ℝ =>
      inner ℂ (v : H) (T.field 0 μ (T.smearing.test R) (u : Q.domain) : H))
      atTop (nhds (inner ℂ (v : H)
        ((metricSign μ : ℂ) • (T.translations.operator μ).toLinearMap
          ⟨((u : Q.domain) : H), core_domain μ u⟩)))

/-- Zero stress cannot be disconnected from nonzero physical momentum:
weak charge normalization and a graph core force every generator to be zero. -/
theorem zero_tensor_implies_zero_generators (T : StressTensorData Q G C)
    (hT : T.Compatible) (hQ : WightmanAxioms H Q)
    (hzero : ∀ μ ν f v, T.field μ ν f v = 0) :
    ∀ μ (v : (T.translations.operator μ).domain),
      (T.translations.operator μ).toLinearMap v = 0 := by
  have hcore : ∀ μ (u : T.chargeCore),
      (T.translations.operator μ).toLinearMap
        ⟨((u : Q.domain) : H), hT.core_domain μ u⟩ = 0 := by
    intro μ u
    let y : H := (metricSign μ : ℂ) • (T.translations.operator μ).toLinearMap
      ⟨((u : Q.domain) : H), hT.core_domain μ u⟩
    have hclosed : IsClosed {v : H | inner ℂ v y = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hsub : (Q.domain : Set H) ⊆ {v : H | inner ℂ v y = 0} := by
      intro v hv
      have hlim := hT.charge_limit μ u ⟨v, hv⟩
      have heq : (fun R : ℝ =>
          inner ℂ v (T.field 0 μ (T.smearing.test R) (u : Q.domain) : H)) =
          (fun _ => (0 : ℂ)) := by
        funext R
        rw [hzero]
        simp
      rw [heq] at hlim
      exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
    have hy : y = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp
      (hclosed.closure_subset_iff.mpr hsub (hQ.dense_domain y))
    by_cases hμ : μ = 0
    · simpa [y, metricSign, hμ] using hy
    · simpa [y, metricSign, hμ] using hy
  intro μ v
  obtain ⟨sequence, _, hsequence⟩ := hT.graph_core μ v
  have heq : (fun n => (T.translations.operator μ).toLinearMap
      ⟨((sequence n : Q.domain) : H), hT.core_domain μ (sequence n)⟩) =
      (fun _ => (0 : H)) := funext (fun n => hcore μ (sequence n))
  rw [heq] at hsequence
  exact (tendsto_nhds_unique tendsto_const_nhds hsequence).symm

/-- In a theory with the required positive finite physical mass, an
identically zero stress tensor cannot satisfy the same-generator conditions. -/
theorem not_zero_tensor_of_massGap (T : StressTensorData Q G C)
    (hT : T.Compatible) (hQ : GappedWightmanTheory H Q) :
    ¬ (∀ μ ν f v, T.field μ ν f v = 0) := by
  intro hzero
  have hPzero := T.zero_tensor_implies_zero_generators hT hQ.axioms hzero 0
  have hHzero : ∀ v : Q.hamiltonian.domain, Q.hamiltonian.toLinearMap v = 0 := by
    have heq : T.translations.operator 0 = Q.hamiltonian := hT.generators.time
    exact heq ▸ hPzero
  have hdom : ∀ v : H, v ∈ Q.hamiltonian.domain := by
    intro v
    obtain ⟨hv, _⟩ := (hQ.axioms.selfAdjoint v 0).mp (by
      intro u
      simp [hHzero])
    exact hv
  apply no_finite_mass_without_positive_energy Q.hamiltonian.realSpectrum _ hQ.massGap
  intro E hE
  apply le_of_not_gt
  intro hpos
  exact hE (Q.hamiltonian.zero_inResolvent hdom hHzero (E : ℂ)
    (by exact_mod_cast ne_of_gt hpos))

/-- Fixed Lorentzian curvature-square scalar, in the same convention as
`classicalStress`; the label below must represent this quantity on actual
connections. -/
def classicalCurvatureSquare (B : InvariantForm G) (A : Connection G)
    (x : Spacetime) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4,
    metricSign ρ * metricSign σ * B.bilinear (A.curvature x ρ σ) (A.curvature x ρ σ)

/-- The concrete trace-anomaly equation in the convention
L = -B(F,F)/(4 g^2). This is a relation to a supplied beta-function value,
NOT a definition of the Yang--Mills beta function. A complete specification
must compute that value from its fixed group-dependent prescription rather
than quantify over it as freely selected "predictions". -/
def HasTraceAnomaly (T : StressTensorData Q G C) (betaValue : ℝ) (curvatureSquare : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  (∀ (A : Connection G) x,
    (curvatureSquare : CurvatureJetPolynomial G).onConnection A x =
      classicalCurvatureSquare T.traceForm A x) ∧
  (∀ f v,
    ∑ μ : Fin 4, (metricSign μ : ℂ) • T.field μ μ f v =
      ((betaValue / (2 * T.coupling.val ^ 3) : ℝ) : ℂ) • C.field T.scale curvatureSquare f v)

end StressTensorData
end YangMills
