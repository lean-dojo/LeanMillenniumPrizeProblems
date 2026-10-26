import Problems.YangMills.AmputatedLegendre
import Problems.YangMills.WardContinuum

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Concrete connected-source / 1PI endpoint scheme transport

The functional pullback of a 1PI action is not the pullback of a CAC
interaction. Fixed formulas below restore the free action, retain the free
antifield source shift, and use inverse source factors for connected W.
Only bare-UV and physical-IR endpoints admit the simple field-change formula;
no such equality is asserted at an arbitrary positive IR regulator.
-/
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.Legendre
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.FieldParameter
variable {G : CompactSimpleGaugeGroup}

/-- S0^UV of FHH(290): kinetic part has R_UV^-1, free antifield
couplings are unweighted. It uses the exact fixed shifted-B/free-BV vertices. -/
def regulatedFreeAction (UV : ℝ) : OrderedAmplitude G :=
  fun legs q =>
    (if h : legs.length = 2 then
      if legs.all (fun K => K.isLeft) then
        ((exponentialRegulator UV (q ⟨0, by omega⟩) : ℂ)⁻¹)
      else 1
    else 1) * freeVertexAmplitude G legs q

def withFreeAction (A : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV => A g loop Λ UV + if loop = 0 then regulatedFreeAction UV else 0

/-- Correct 1PI INTERACTION pullback; the full fixed free action is added
before substitution and subtracted afterwards. This includes quadratic
covariance and free BV source compensation, not merely z^n on interaction L. -/
def regulatedCompensated1PIPullback (change : FiniteParameterChange) (mu : ℝ)
    (A : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV => change.functionalPullback mu (withFreeAction A) g loop Λ UV -
    if loop = 0 then regulatedFreeAction UV else 0

/-- Local free BV action, used by the actual local UV counterterms. -/
def withLocalFreeAction (A : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV => A g loop Λ UV + if loop = 0 then freeVertexAmplitude G else 0

/-- Local 1PI compensation. Using S0^UV here instead would introduce
nonlocal cutoff quadratics incompatible with the local UV boundary scheme. -/
def compensated1PIPullback (change : FiniteParameterChange) (mu : ℝ)
    (A : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV => change.functionalPullback mu (withLocalFreeAction A) g loop Λ UV -
    if loop = 0 then freeVertexAmplitude G else 0

/-- FIXED cutoff artifact separating regulated and local free compensation:
change*(S0^UV-S0)-(S0^UV-S0). It is an actual quadratic Fourier expression,
not freely selected irrelevant counterterm/error data. Its removal needs the
UV estimates; vanishing cannot be inferred merely from its formal name. -/
def freeCovarianceArtifact (change : FiniteParameterChange) (mu : ℝ) : ℝ → FlowFamily G :=
  fun g loop Λ UV =>
    change.functionalPullback mu
      (fun _ l _ cutoff => if l = 0 then regulatedFreeAction cutoff - freeVertexAmplitude G else 0)
      g loop Λ UV -
      if loop = 0 then regulatedFreeAction UV - freeVertexAmplitude G else 0

/-- J_eff=J-d_phi S0_antifield, in the source convention of FHH(71).
The Hessian comes from the actual free action; no new shift operator is data. -/
def effectiveSourceKernel (M : BasicField G) (target : ExternalLeg G) (p : Spacetime) : ℂ :=
  match target with
  | .inl N => if M = N then 1 else 0
  | .inr N => -freeVertexAmplitude G [.inl M, .inr N]
      (fun i => if i.val = 0 then -p else p)

/-- Linear Fourier symbol from the original unshifted sources/antifields
to the amputated field variables and unchanged antifield spectators. -/
def sourceToAmputated (s : CutoffScales) (root target : ExternalLeg G) (p : Spacetime) : ℂ :=
  match root with
  | .inr M => if target = .inr M then 1 else 0
  | .inl M => ∑ N : BasicField G,
      (basicCovariance s M N p : ℂ) * effectiveSourceKernel N target p

/-- Actual coefficient pullback by a fixed linear momentum symbol. -/
def linearSymbolPullback (symbol : ExternalLeg G → ExternalLeg G → Spacetime → ℂ)
    (A : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => ∑ roots : Fin legs.length → ExternalLeg G,
    (∏ i, symbol (roots i) (legs.get i) (q i)) *
      A (rootLegs roots) (fun i => q ⟨i.val, by simpa [rootLegs] using i.isLt⟩)

/-- Free connected source quadratic, including all free-antifield shifts.
The parity sign converts the Gaussian graded pairing to ordered LEFT source
coefficients; odd sources use the right dual convention J=delta_L S0.
The background's last external momentum is dependent, as in FHH(87). -/
def freeSourceQuadratic (s : CutoffScales) : OrderedAmplitude G :=
  fun legs q => if h : legs.length = 2 then
    let p := q ⟨0, by omega⟩
    let a := legs.get ⟨0, by omega⟩
    let b := legs.get ⟨1, by omega⟩
    ∑ M : BasicField G, ∑ N : BasicField G,
      effectiveSourceKernel M a p * rightDerivativeSign false (.inl M) *
        (basicCovariance s M N p : ℂ) *
        effectiveSourceKernel N b (-p)
  else 0

/-- Raw connected W computed from actual engine L, retaining every
antifield-only coefficient. Free Gaussian pairing has its fixed graded sign. -/
def rawConnectedSource (A : ℝ → FlowFamily G) (g : ℝ) (loop : ℕ)
    (s : CutoffScales) : OrderedAmplitude G :=
  (if loop = 0 then freeSourceQuadratic s else 0) -
    linearSymbolPullback (sourceToAmputated s) (A g loop s.infrared s.ultraviolet)

/-- Projection to the complete source-J-independent antifield sector. -/
def antifieldOnlyPart (A : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => if legs.any (fun K => K.isLeft) then 0 else A legs q

/-- Computed I=-W_raw(0,antifield), not arbitrary normalization data.
Equivalently I=L(C H antifield,antifield)-<H antifield,C H antifield>/2,
with H and the graded Gaussian term explicitly fixed above. -/
def sourceNormalizationI (A : ℝ → FlowFamily G) (g : ℝ) (loop : ℕ)
    (s : CutoffScales) : OrderedAmplitude G :=
  -antifieldOnlyPart (rawConnectedSource A g loop s)

/-- Normalized W=W_raw-W_raw(0,antifield)=W_raw+I. This operation is
EXPLICIT; it never silently discards the normalization from Γ or BV identities. -/
def normalizedConnectedSource (A : ℝ → FlowFamily G) (g : ℝ) (loop : ℕ)
    (s : CutoffScales) : OrderedAmplitude G :=
  rawConnectedSource A g loop s + sourceNormalizationI A g loop s

/-- Legendre transformation after source normalization changes Γ by -I.
The raw Γ remains the default for BV/CS identities; a normalized Γ must carry
this exact computed correction in its Ward equation. -/
def sourceNormalizedGamma (A : ℝ → FlowFamily G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop legs q => actualGamma A s order loop legs q -
    (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
      (fun g : ℝ => sourceNormalizationI A g loop s legs q) 0

def rawConnectedSourceFamily (A : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV => if h : 0 < Λ ∧ Λ ≤ UV then
    rawConnectedSource A g loop ⟨Λ, UV, h.1, h.2⟩ else 0

def connectedSourceFamily (A : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV => if h : 0 < Λ ∧ Λ ≤ UV then
    normalizedConnectedSource A g loop ⟨Λ, UV, h.1, h.2⟩ else 0

theorem rawGamma_eq_normalized_add_I (A : ℝ → FlowFamily G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    actualGamma A s order loop legs q = sourceNormalizedGamma A s order loop legs q +
      (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
        (fun g : ℝ => sourceNormalizationI A g loop s legs q) 0 := by
  unfold sourceNormalizedGamma
  exact (sub_add_cancel _ _).symm

/-- Under S_new(phi,phi*)=S_old(R phi,R^-T phi*), connected sources
transform by R^-T on J AND on antifields. This differs from positive
external field factors on the full 1PI functional. -/
def inverseSourceScale (z : BasicScales) : ExternalLeg G → ℝ
  | .inl K => (basicScale z K)⁻¹
  | .inr K => (basicScale z K)⁻¹

def inverseSourceFactor (z : BasicScales) (legs : List (ExternalLeg G)) : ℂ :=
  (legs.map fun K => (inverseSourceScale z K : ℂ)).prod

/-- Formal hbar pullback with the source-dual factors. -/
def sourcePullback (change : FiniteParameterChange) (mu : ℝ)
    (W : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV legs q => ∑ r : Fin (loop + 1),
    (Nat.factorial (loop - r.val) : ℂ)⁻¹ * iteratedDeriv (loop - r.val)
      (fun h : ℝ => inverseSourceFactor (change.fields mu h g) legs *
        W (change.coupling mu h g) r.val Λ UV legs q) 0

/-- Coupling coefficients of any actual flow expression. -/
def flowCouplingJet (A : ℝ → FlowFamily G) (order loop : ℕ)
    (Λ UV : ℝ) : OrderedAmplitude G :=
  fun legs q => (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => A g loop Λ UV legs q) 0

/-- Finite g polynomial of the ACTUAL computed Γ coefficients. Only this
finite polynomial is used to evaluate a formal germ through a given order;
there is no infinite analytic resummation. -/
def gammaTruncation (A : ℝ → FlowFamily G) (bound : ℕ) : ℝ → FlowFamily G :=
  fun g loop Λ UV legs q => if h : 0 < Λ ∧ Λ ≤ UV then
    ∑ order ∈ Finset.range (bound + 1), (g : ℂ) ^ order *
      actualGamma A ⟨Λ, UV, h.1, h.2⟩ order loop legs q
  else 0

/-- Difference of RAW connected-source coefficients, retaining computed I.
Pure-antifield information is therefore not lost in endpoint transport. -/
def connectedEndpointDifference (change : FiniteParameterChange) (mu : ℝ)
    (old new : ℝ → FlowFamily G) (order loop : ℕ) (Λ UV : ℝ) : OrderedAmplitude G :=
  flowCouplingJet (rawConnectedSourceFamily new) order loop Λ UV -
    flowCouplingJet (sourcePullback change mu (rawConnectedSourceFamily old)) order loop Λ UV

/-- Actual computed Γ difference, with the fixed free quadratic/source
compensation included BEFORE taking the coupling coefficient. -/
def gammaEndpointDifference (change : FiniteParameterChange) (mu : ℝ)
    (old new : ℝ → FlowFamily G) (order loop : ℕ) (Λ UV : ℝ) : OrderedAmplitude G :=
  flowCouplingJet (gammaTruncation new order) order loop Λ UV -
    flowCouplingJet (compensated1PIPullback change mu (gammaTruncation old order))
      order loop Λ UV

/-- Pair an actual background coefficient with its restored conservation
delta, using the same reduced-momentum convention as WardContinuum. -/
def endpointIntegrand (A : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 0 legs) (q : Fin (legs.length - 1) → Spacetime) : ℂ :=
  let balanced := balancedFromReduced legs q
  A legs balanced * test ((fun i : Fin 0 => Fin.elim0 i), balanced)

/-- Weak UV limits of the COMPUTED differences, unique on the tested compact
region when the conditions below hold. They are not additional predictions. -/
structure CACEndpointDifferences (G : CompactSimpleGaugeGroup) where
  connected : ℝ → ℕ → ℕ → ℝ → (legs : List (ExternalLeg G)) → JointMomentumDistribution 0 legs
  gamma : ℝ → ℕ → ℕ → ℝ → (legs : List (ExternalLeg G)) → JointMomentumDistribution 0 legs

/-- Concrete same-theory CAC transport. Both families satisfy the SAME
fixed covariance flow and local UV boundary equations. The prescribed local
bare pullback has the explicit freeCovarianceArtifact relative to a fully
regulated change of variables. Endpoint equality is UV FIRST, then IR;
there is no incorrect exact finite-cutoff source/Γ equivalence assertion. -/
structure CACSchemeTransportConditions {B : InvariantForm G} (e : ColorFrame B)
    (oldScheme newScheme : LocalMarginalData G) (old new : ScaleCouplingFamily G)
    (change : FiniteParameterChange) (difference : CACEndpointDifferences G) : Prop where
  old_flow : CoefficientFlowConditions e oldScheme old
  new_flow : CoefficientFlowConditions e newScheme new
  bare_boundary : ∀ mu UV order loop legs q, 0 < mu → mu < UV → BalancedMomenta legs q →
    flowCouplingJet (new mu) order loop UV UV legs q =
      flowCouplingJet (compensated1PIPullback change mu (old mu)) order loop UV UV legs q
  legendre_old : ∀ mu (s : CutoffScales), 0 < mu →
    AmputatedLegendreEquations (flowJet (old mu) s) s
  legendre_new : ∀ mu (s : CutoffScales), 0 < mu →
    AmputatedLegendreEquations (flowJet (new mu) s) s
  connected_integrable : ∀ mu UV order loop Λ legs (test : JointMomentumTest 0 legs),
    0 < mu → mu < UV → 0 < Λ → Λ ≤ UV → HasCompactSupport test →
    NonexceptionalSupport .single test → MeasureTheory.Integrable
      (endpointIntegrand (connectedEndpointDifference change mu (old mu) (new mu)
        order loop Λ UV) legs test)
  gamma_integrable : ∀ mu UV order loop Λ legs (test : JointMomentumTest 0 legs),
    0 < mu → mu < UV → 0 < Λ → Λ ≤ UV → HasCompactSupport test →
    NonexceptionalSupport .single test → MeasureTheory.Integrable
      (endpointIntegrand (gammaEndpointDifference change mu (old mu) (new mu)
        order loop Λ UV) legs test)
  connected_uv : ∀ mu order loop Λ legs (test : JointMomentumTest 0 legs),
    0 < mu → 0 < Λ → HasCompactSupport test → NonexceptionalSupport .single test →
    Filter.Tendsto (fun UV : ℝ => ∫ q,
      endpointIntegrand (connectedEndpointDifference change mu (old mu) (new mu)
        order loop Λ UV) legs test q)
      Filter.atTop (nhds (difference.connected mu order loop Λ legs test))
  gamma_uv : ∀ mu order loop Λ legs (test : JointMomentumTest 0 legs),
    0 < mu → 0 < Λ → HasCompactSupport test → NonexceptionalSupport .single test →
    Filter.Tendsto (fun UV : ℝ => ∫ q,
      endpointIntegrand (gammaEndpointDifference change mu (old mu) (new mu)
        order loop Λ UV) legs test q)
      Filter.atTop (nhds (difference.gamma mu order loop Λ legs test))
  connected_ir : ∀ mu order loop legs (test : JointMomentumTest 0 legs),
    0 < mu → HasCompactSupport test → NonexceptionalSupport .single test →
    Filter.Tendsto (fun Λ : ℝ => difference.connected mu order loop Λ legs test)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  gamma_ir : ∀ mu order loop legs (test : JointMomentumTest 0 legs),
    0 < mu → HasCompactSupport test → NonexceptionalSupport .single test →
    Filter.Tendsto (fun Λ : ℝ => difference.gamma mu order loop Λ legs test)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)


theorem compensated1PIPullback_tree (change : FiniteParameterChange) (mu : ℝ)
    (hmu : 0 < mu) (A : ℝ → FlowFamily G) (g : ℝ) :
    compensated1PIPullback change mu A g 0 = A g 0 := by
  funext Λ UV legs q
  change change.functionalPullback mu (withLocalFreeAction A) g 0 Λ UV legs q -
    freeVertexAmplitude G legs q = _
  rw [change.functionalPullback_tree mu hmu]
  simp [withLocalFreeAction]

theorem sourceNormalizationI_basic (A : ℝ → FlowFamily G) (g : ℝ) (loop : ℕ)
    (s : CutoffScales) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (h : legs.any (fun K => K.isLeft) = true) : sourceNormalizationI A g loop s legs q = 0 := by
  simp [sourceNormalizationI, antifieldOnlyPart, h]

theorem normalizedConnectedSource_basic (A : ℝ → FlowFamily G) (g : ℝ) (loop : ℕ)
    (s : CutoffScales) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (h : legs.any (fun K => K.isLeft) = true) :
    normalizedConnectedSource A g loop s legs q = rawConnectedSource A g loop s legs q := by
  simp [normalizedConnectedSource, sourceNormalizationI_basic A g loop s legs q h]

theorem normalizedConnectedSource_antifieldOnly (A : ℝ → FlowFamily G) (g : ℝ) (loop : ℕ)
    (s : CutoffScales) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (h : legs.any (fun K => K.isLeft) = false) : normalizedConnectedSource A g loop s legs q = 0 := by
  simp [normalizedConnectedSource, sourceNormalizationI, antifieldOnlyPart, h]

end YangMills.Legendre
