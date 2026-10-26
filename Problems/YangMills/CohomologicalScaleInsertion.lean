import Problems.YangMills.AmputatedLegendre
import Problems.YangMills.FiniteWardRestoration
import Problems.YangMills.QuantumObservableLift

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Same-prescription cohomological Callan--Symanzik equations

IZ printed pp.649--651, (13-66)--(13-74), distinguishes the actual scale
insertion from a merely named beta function. In a gauge theory gauge-parameter
transport must also be accounted for. IZ pp.601--603, (12-163)--(12-168),
classifies local ST cocycles into coupling and canonical/exact directions.
These equations below are concrete classification/normalization TARGETS for
the same computed flow and its directional Legendre insertions. Existence,
cohomological uniqueness and the gauge-parameter classification are not proved.
No multiplicative Ward decomposition of a finite-cutoff bare action is assumed.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
open scoped BigOperators
namespace YangMills.ScaleInsertion
open YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.Legendre YangMills.FieldParameter
variable {G : CompactSimpleGaugeGroup}

/-- Formal hbar and coupling orders remain independent. -/
abbrev ScalarCoefficients := ℕ → ℕ → ℝ

/-- Exact finite bigraded Cauchy multiplication. -/
def scalarAction (c : ScalarCoefficients) (A : FormalAmplitude G) : FormalAmplitude G :=
  fun order loop legs q => ∑ a : Fin (order+1), ∑ l : Fin (loop+1),
    (c a.val l.val : ℂ) * A (order-a.val) (loop-l.val) legs q

/-- g derivative of a formal coupling series, including its actual factor. -/
def couplingDerivative (A : FormalAmplitude G) : FormalAmplitude G :=
  fun order loop legs q => (order+1 : ℂ) * A (order+1) loop legs q

/-- The full endpoint action includes the SAME fixed quadratic master
polynomial, not only the interaction part of the amputated transform.
Its use inside physical equations below is through UV-then-IR limits. -/
def fullGamma (A : ℝ → FlowFamily G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop legs q => actualGamma A s order loop legs q +
    if order = 0 ∧ loop = 0 then freeVertexAmplitude G legs q else 0

/-- Actual subtraction-scale derivative at fixed external momenta, cutoffs
and renormalized coupling coefficient. Smoothness is required below. -/
def scaleDerivative (A : ℝ → FormalAmplitude G) (μ : ℝ) : FormalAmplitude G :=
  fun order loop legs q => (μ : ℂ) * deriv (fun ν => A ν order loop legs q) μ

/-- Infinitesimal field/source rescaling. Inverse-dual antifields have the
opposite weight, exactly as in the proved finite master-action pullback. -/
def eulerWeight (weights : BasicScales) : ExternalLeg G → ℝ
  | .inl K => basicScale weights K
  | .inr K => -basicScale weights K

def eulerAction (weights : BasicScales) (A : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => ((legs.map (eulerWeight weights)).sum : ℂ) * A legs q

abbrev FieldCoefficients := ℕ → ℕ → BasicScales

def fieldAction (c : FieldCoefficients) (A : FormalAmplitude G) : FormalAmplitude G :=
  fun order loop legs q => ∑ a : Fin (order+1), ∑ l : Fin (loop+1),
    eulerAction (c a.val l.val) (A (order-a.val) (loop-l.val)) legs q

/-- Coupling-adic inversion of the background mean-field map for a local
insertion. At fixed Phi the Legendre derivative is I(phi(Phi)); the implicit
field variation cancels. The roots below ALWAYS belong to the background,
so an insertion's independent external momenta are never forced balanced. -/
def insertionGammaCoeff (F I : FormalAmplitude G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop legs q => I order loop legs q -
    ∑ k : Fin (legs.length + 1), ∑ assignment : Fin legs.length → Fin k.val,
    ∑ roots : Fin k.val → ExternalLeg G,
    ∑ gOrders : Fin (k.val + 1) → Fin (order + 1),
    ∑ hOrders : Fin (k.val + 1) → Fin (loop + 1),
      if _h : (gOrders 0).val < order then
        substitutionSummand
          (fun r l ls ps => if _hr : r < order then insertionGammaCoeff F I s r l ls ps else 0)
          F s order loop legs q k.val assignment roots gOrders hOrders
      else 0
termination_by order => order

/-- The recursion has the fixed insertion's actual leading coupling jet;
no normalization value can be independently chosen at this order. -/
theorem insertionGammaCoeff_zero (F I : FormalAmplitude G) (s : CutoffScales)
    (loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    insertionGammaCoeff F I s 0 loop legs q = I 0 loop legs q := by
  rw [insertionGammaCoeff]
  simp

/-- Computed fixed-mean-field directional Legendre insertion. No separately
supplied 1PI insertion is allowed. -/
def directionalGamma (A I : ℝ → FlowFamily G) (s : CutoffScales) : FormalAmplitude G :=
  insertionGammaCoeff (flowJet A s) (flowJet I s) s

/-- Exact local-insertion Legendre identity on ALL independent momenta.
This must be established for the fixed recursion; it is not a candidate
insertion chosen to make a CS relation true. -/
def DirectionalLegendreCompatible (A I : ℝ → FlowFamily G) (s : CutoffScales) : Prop :=
  meanFieldCompose (directionalGamma A I s) (flowJet A s) s = flowJet I s

/-- Finite renormalized local primitive. offset=2 is the action graph
power; offset=0 is the source-normalized composite graph power. -/
structure LocalScalePrimitive (G : CompactSimpleGaugeGroup) (degree offset : ℕ) where
  coefficient : ℝ → ℝ → ℕ → LocalMonomial G →₀ ℂ
  support : ∀ μ g loop m, coefficient μ g loop m ≠ 0 →
    m.Admissible ∧ m.dimension + 1 ≤ degree ∧ m.ghostNumber = -1 ∧ m.parity = true
  smooth : ∀ loop m, ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => coefficient z.1 z.2 loop m) (Set.Ioi 0 ×ˢ Set.univ)
  classical : ∀ μ g, 0 < μ → coefficient μ g 0 = 0
  graph_power : ∀ μ g loop m, coefficient μ g loop m =
    if offset ≤ m.legs.length + 2*loop then
      (g : ℂ) ^ (m.legs.length + 2*loop-offset) * coefficient μ 1 loop m else 0

/-- Q is computed from the SAME classical master action and transported
insertion anomaly. This uses the raw finite generated coefficient, whose
physical meaning still requires the parent's actual Ward-limit conditions. -/
def quantumExactInsertion {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (L : ℝ → ℝ → InsertedFlowFamily G) {degree offset : ℕ}
    (primitive : LocalScalePrimitive G degree offset) (μ g : ℝ) (x : Spacetime) : FlowFamily G :=
  fun loop Λ UV legs q => ∑ a : Fin (loop+1), ∑ b : Fin (loop-a.val+1),
    (primitive.coefficient μ g a.val).sum (fun input c =>
      ∑ output ∈ monomialsBelow G (input.dimension+2),
        c * generatedQuantumWardCoefficient e g (anomaly μ g) b.val UV input output *
          L μ g [⟨output, x⟩] (loop-a.val-b.val) Λ UV legs q)

/-- Actual same-flow physical quantum-exact 1PI insertion approximants. -/
def quantumExactGamma {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    {degree offset : ℕ} (primitive : LocalScalePrimitive G degree offset)
    (μ : ℝ) (s : CutoffScales) (x : Spacetime) : FormalAmplitude G :=
  directionalGamma (A μ) (fun g => quantumExactInsertion e anomaly L primitive μ g x) s

/-- Every ordered amplitude is tested; a finite collection of projector
coordinates cannot conceal a nonzero scale anomaly. -/
def weakPairingIntegrand (R : ℝ → ℝ → FormalAmplitude G)
    (order loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 0 legs) (q : Fin (legs.length-1) → Spacetime) : ℂ :=
  R Λ UV order loop legs (balancedFromReduced legs q) *
    test ((fun i : Fin 0 => Fin.elim0 i), balancedFromReduced legs q)

def weakPairing (R : ℝ → ℝ → FormalAmplitude G) (order loop : ℕ)
    (Λ UV : ℝ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 0 legs) : ℂ :=
  ∫ q, weakPairingIntegrand R order loop Λ UV legs test q

def WeakEndpointZero (R : ℝ → ℝ → FormalAmplitude G) : Prop :=
  ∀ order loop legs (test : JointMomentumTest 0 legs), HasCompactSupport test →
    NonexceptionalSupport .wardSingle test →
    (∀ Λ, 0 < Λ → ∀ᶠ UV in atTop,
      Λ ≤ UV ∧ Integrable (weakPairingIntegrand R order loop Λ UV legs test)) ∧
    ∃ limit : ℝ → ℂ,
      (∀ Λ, 0 < Λ → Tendsto (fun UV => weakPairing R order loop Λ UV legs test)
        atTop (nhds (limit Λ))) ∧
      Tendsto limit (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- The action CS residual is COMPUTED from the same Γ, not a separate
scale-anomaly family. Field/EOM directions include inverse-dual sources. -/
def actionResidual {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (primitive : LocalScalePrimitive G 4 2) (μ : ℝ) (s : CutoffScales) : FormalAmplitude G :=
  scaleDerivative (fun ν => fullGamma (A ν) s) μ +
    scalarAction beta (couplingDerivative (fullGamma (A μ) s)) -
    fieldAction fields (fullGamma (A μ) s) - quantumExactGamma e anomaly A L primitive μ s 0

/-- Concrete CS authorization target. Gauge-parameter transport can only
be represented here by its actual generated-Q gauge-fermion insertion;
showing that this suffices is a classification proof, not an assumed slogan. -/
structure ActionCSConditions {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (primitive : LocalScalePrimitive G 4 2) : Prop where
  beta_classical : ∀ order, beta order 0 = 0
  beta_free : ∀ loop order, order < 3 → beta order loop = 0
  field_classical : ∀ order, fields order 0 = ⟨0,0,0,0⟩
  gamma_scale_smooth : ∀ order loop s legs,
    ContDiffOn ℝ ∞
      (fun z : ℝ × (Fin legs.length → Spacetime) => fullGamma (A z.1) s order loop legs z.2)
      (Set.Ioo 0 s.ultraviolet ×ˢ Set.univ)
  same_background : ∀ μ g, A μ g = L μ g []
  legendre : ∀ μ s, 0 < μ → μ < s.ultraviolet →
    AmputatedLegendreEquations (flowJet (A μ) s) s
  exact_directional : ∀ μ s, 0 < μ → μ < s.ultraviolet →
    DirectionalLegendreCompatible (A μ) (fun g => quantumExactInsertion e anomaly L primitive μ g 0) s
  equation : ∀ μ, 0 < μ → WeakEndpointZero (fun Λ UV =>
    if h : 0 < Λ ∧ Λ ≤ UV then
      actionResidual e anomaly A L beta fields primitive μ ⟨Λ,UV,h.1,h.2⟩ else 0)

/-- The scale insertion itself is fixed before any cohomological split. -/
def actualScaleInsertion (A : ScaleCouplingFamily G) (μ : ℝ)
    (s : CutoffScales) : FormalAmplitude G :=
  scaleDerivative (fun ν => fullGamma (A ν) s) μ

/-- Pure algebra: imposing the computed residual's vanishing is exactly
its concrete coupling/field/quantum-exact decomposition, coefficient by
coefficient. Physical authorization additionally requires the weak endpoint
and same-theory Ward hypotheses above and in the parent bundle. -/
theorem actionResidual_eq {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (primitive : LocalScalePrimitive G 4 2) (μ : ℝ) (s : CutoffScales) :
    actionResidual e anomaly A L beta fields primitive μ s =
      actualScaleInsertion A μ s + scalarAction beta (couplingDerivative (fullGamma (A μ) s)) -
        fieldAction fields (fullGamma (A μ) s) - quantumExactGamma e anomaly A L primitive μ s 0 := rfl

/-- Same corrected local observable, transformed by the background mean map.
All subtraction-scale dependence of its dictionary is differentiated too. -/
def liftedGamma (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (lift : ℝ → QuantumObservableLift G) (μ : ℝ) (s : CutoffScales)
    (p : InvariantInsertionLabel G) (x : Spacetime) : FormalAmplitude G :=
  directionalGamma (A μ) (fun g => (lift μ).finiteInsertion (L μ g) g p x) s

/-- Finite local operator mixing, with intrinsic engineering filtration.
Dimensionful lower-degree mixing is allowed; no chosen oversized label bound
can weaken the condition. The real coefficients preserve Hermitian labels. -/
structure CompositeMixing (G : CompactSimpleGaugeGroup) where
  coefficient : ℝ → ℕ → ℕ → InvariantInsertionLabel G → InvariantInsertionLabel G →₀ ℝ
  filtered : ∀ μ order loop p q, coefficient μ order loop p q ≠ 0 →
    intrinsicEngineeringDimension q ≤ intrinsicEngineeringDimension p
  smooth : ∀ order loop p q,
    ContDiffOn ℝ ∞ (fun μ => coefficient μ order loop p q) (Set.Ioi 0)
  classical : ∀ μ order p, 0 < μ → coefficient μ order 0 p = 0
  unit : ∀ μ order loop, 0 < μ → coefficient μ order loop 1 = 0
  linear_add : ∀ μ order loop p q,
    coefficient μ order loop (p+q) = coefficient μ order loop p + coefficient μ order loop q
  linear_smul : ∀ μ order loop (c : ℝ) p,
    coefficient μ order loop (c • p) = c • coefficient μ order loop p

def mixingAction (mixing : CompositeMixing G) (μ : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G)
    (p : InvariantInsertionLabel G) : FormalAmplitude G :=
  fun order loop legs q => ∑ a : Fin (order+1), ∑ l : Fin (loop+1),
    (mixing.coefficient μ a.val l.val p).sum (fun output c =>
      (c : ℂ) * J output (order-a.val) (loop-l.val) legs q)

/-- Composite convention: D O_p = -gamma_p^q O_q modulo generated-Q
exact terms. This fixes the PLUS sign of mixing in the residual below. -/
def compositeResidual {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (lift : ℝ → QuantumObservableLift G) (beta : ScalarCoefficients)
    (fields : FieldCoefficients) (mixing : CompositeMixing G)
    (primitive : (p : InvariantInsertionLabel G) →
      LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (μ : ℝ) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime) :
    FormalAmplitude G :=
  scaleDerivative (fun ν => liftedGamma A L lift ν s p x) μ +
    scalarAction beta (couplingDerivative (liftedGamma A L lift μ s p x)) -
    fieldAction fields (liftedGamma A L lift μ s p x) +
    mixingAction mixing μ (fun output => liftedGamma A L lift μ s output x) p -
    quantumExactGamma e anomaly A L (primitive p) μ s x

/-- The composite equation uses all independent external momenta AND the
insertion position, with no erroneous momentum delta at a local insertion. -/
def localPairingIntegrand (R : ℝ → ℝ → Spacetime → FormalAmplitude G)
    (order loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs)
    (xq : (Fin 1 → Spacetime) × (Fin legs.length → Spacetime)) : ℂ :=
  R Λ UV (xq.1 0) order loop legs xq.2 * test xq

def localPairing (R : ℝ → ℝ → Spacetime → FormalAmplitude G)
    (order loop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs) : ℂ :=
  ∫ xq, localPairingIntegrand R order loop Λ UV legs test xq

def WeakLocalEndpointZero (R : ℝ → ℝ → Spacetime → FormalAmplitude G) : Prop :=
  ∀ order loop legs (test : JointMomentumTest 1 legs), HasCompactSupport test →
    NonexceptionalSupport .single test →
    (∀ Λ, 0 < Λ → ∀ᶠ UV in atTop,
      Λ ≤ UV ∧ Integrable (localPairingIntegrand R order loop Λ UV legs test)) ∧
    ∃ limit : ℝ → ℂ,
      (∀ Λ, 0 < Λ → Tendsto (fun UV => localPairing R order loop Λ UV legs test)
        atTop (nhds (limit Λ))) ∧
      Tendsto limit (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- Composite CS authorization for the SAME beta, field weights, actual
flow, generated Q and corrected dictionary at ALL subtraction scales. No
bijection between classical and quantum cohomology is presumed. -/
structure CompositeCSConditions {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G)
    (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (Q : ℝ → QuantumWardLimit G) (lift : ℝ → QuantumObservableLift G)
    (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (actionPrimitive : LocalScalePrimitive G 4 2) (mixing : CompositeMixing G)
    (primitive : (p : InvariantInsertionLabel G) →
      LocalScalePrimitive G (intrinsicEngineeringDimension p) 0) : Prop where
  action : ActionCSConditions e anomaly A L beta fields actionPrimitive
  same_dictionary : ∀ μ, 0 < μ → (lift μ).Compatible e (anomaly μ) (Q μ)
  lifted_scale_smooth : ∀ s p order loop legs,
    ContDiffOn ℝ ∞
      (fun z : ℝ × (Spacetime × (Fin legs.length → Spacetime)) =>
        liftedGamma A L lift z.1 s p z.2.1 order loop legs z.2.2)
      (Set.Ioo 0 s.ultraviolet ×ˢ Set.univ)
  lifted_directional : ∀ μ s p x, 0 < μ → μ < s.ultraviolet →
    DirectionalLegendreCompatible (A μ) (fun g => (lift μ).finiteInsertion (L μ g) g p x) s
  exact_directional : ∀ μ s p x, 0 < μ → μ < s.ultraviolet →
    DirectionalLegendreCompatible (A μ)
      (fun g => quantumExactInsertion e anomaly L (primitive p) μ g x) s
  equation : ∀ μ p, 0 < μ → WeakLocalEndpointZero (fun Λ UV x =>
    if h : 0 < Λ ∧ Λ ≤ UV then
      compositeResidual e anomaly A L lift beta fields mixing primitive μ
        ⟨Λ,UV,h.1,h.2⟩ p x else 0)

end YangMills.ScaleInsertion
