import Problems.YangMills.FullBV
import Problems.YangMills.ActionProbeSupport
import Problems.YangMills.WardRenormalizationBinding

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Actual field/parameter changes behind multiplicative normalization

IZ (12-163)--(12-168), printed pp.602--603, writes local ST counterterms as
coupling variations and canonical field/source variations, plus gauge-fixing
exact terms. Here all pullbacks use the actual G master-action vertices.
The ordered coefficient identity below proves that this is field substitution
also for ghosts and antifields, rather than evaluation in commuting ghosts.
Classification of every admissible cocycle into these directions, and the
same-flow finite scheme comparison, remain supporting theorems.
-/
noncomputable section
open scoped ContDiff
open scoped BigOperators
namespace YangMills.FieldParameter
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Uniform in color and vector index; arbitrary color matrices would not
be the field renormalizations of the fixed actual group. -/
structure BasicScales where
  gauge : ℝ
  ghost : ℝ
  antighost : ℝ
  auxiliary : ℝ

def basicScale (z : BasicScales) : BasicField G → ℝ
  | .gauge _ _ => z.gauge
  | .ghost _ => z.ghost
  | .antighost _ => z.antighost
  | .auxiliary _ => z.auxiliary

/-- Antifields transform by the inverse dual scaling of the corresponding
field, as required for a canonical BV change. -/
def externalScale (z : BasicScales) : ExternalLeg G → ℝ
  | .inl K => basicScale z K
  | .inr K => (basicScale z K)⁻¹

def InvertibleScales (z : BasicScales) : Prop :=
  z.gauge ≠ 0 ∧ z.ghost ≠ 0 ∧ z.antighost ≠ 0 ∧ z.auxiliary ≠ 0

theorem externalScale_pair (z : BasicScales) (hz : InvertibleScales z) (K : BasicField G) :
    externalScale z (.inl K) * externalScale z (.inr K) = 1 := by
  cases K with
  | gauge μ a => exact mul_inv_cancel₀ hz.1
  | ghost a => exact mul_inv_cancel₀ hz.2.1
  | antighost a => exact mul_inv_cancel₀ hz.2.2.1
  | auxiliary a => exact mul_inv_cancel₀ hz.2.2.2

@[simp] theorem externalScale_one (K : ExternalLeg G) :
    externalScale ⟨1,1,1,1⟩ K = 1 := by
  cases K with
  | inl K => cases K <;> simp [externalScale, basicScale]
  | inr K => cases K <;> simp [externalScale, basicScale]

def scaleVertex (z : BasicScales) (v : LocalVertex G) : LocalVertex G :=
  { v with coefficient := v.coefficient *
      (v.legs.map (fun j => (externalScale z j.field : ℂ))).prod }

def externalFactor (z : BasicScales) (legs : List (ExternalLeg G)) : ℂ :=
  (legs.map (fun K => (externalScale z K : ℂ))).prod

@[simp] theorem externalFactor_one (legs : List (ExternalLeg G)) :
    externalFactor ⟨1,1,1,1⟩ legs = 1 := by
  simp [externalFactor]

/-- Exact ordered field-substitution identity, including all Grassmann
signs and multiplicity factors inherited from the actual coefficient engine. -/
theorem scaleVertex_amplitude (z : BasicScales) (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    localVertexAmplitude (scaleVertex z v) g legs q =
      externalFactor z legs * localVertexAmplitude v g legs q := by
  by_cases hd : localMonomialDerivative v.legs (List.ofFn (fun i => (legs.get i, q i))) = 0
  · simp only [localVertexAmplitude, scaleVertex, hd, mul_zero]
  · have hp := WardAction.localDerivative_support v.legs _ hd
    have he : (List.ofFn (fun i => (legs.get i, q i))).map Prod.fst = legs := by
      simp only [List.map_ofFn, Function.comp_def, List.ofFn_get]
    rw [he] at hp
    have hh := (hp.map (fun K => (externalScale z K : ℂ))).prod_eq
    simp only [List.map_map, Function.comp_def] at hh
    simp only [localVertexAmplitude, scaleVertex, externalFactor]
    rw [hh]
    ring

theorem scalePolynomial_amplitude (z : BasicScales) (terms : List (LocalVertex G))
    (g : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    localPolynomialAmplitude (terms.map (scaleVertex z)) g legs q =
      externalFactor z legs * localPolynomialAmplitude terms g legs q := by
  induction terms with
  | nil => simp [localPolynomialAmplitude]
  | cons v terms ih =>
    change localVertexAmplitude (scaleVertex z v) g legs q +
      localPolynomialAmplitude (terms.map (scaleVertex z)) g legs q =
        externalFactor z legs *
          (localVertexAmplitude v g legs q + localPolynomialAmplitude terms g legs q)
    rw [scaleVertex_amplitude, ih, mul_add]

/-- Full same-G BV action under a finite field/source substitution and a
coupling change. No new vertex list or independent color tensor is supplied. -/
def pulledMasterDensity {B : InvariantForm G} (e : ColorFrame B)
    (z : BasicScales) (coupling : ℝ) : FullBV.JetAlgebra G :=
  FullBV.densityOfVertices coupling
    ((freeActionVertices G ++ treeActionVertices e).map (scaleVertex z))

def pulledMasterAmplitude {B : InvariantForm G} (e : ColorFrame B)
    (z : BasicScales) (coupling : ℝ) : OrderedAmplitude G :=
  localPolynomialAmplitude
    ((freeActionVertices G ++ treeActionVertices e).map (scaleVertex z)) coupling

theorem pulledMasterAmplitude_eq {B : InvariantForm G} (e : ColorFrame B)
    (z : BasicScales) (coupling : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) :
    pulledMasterAmplitude e z coupling legs q = externalFactor z legs *
      localPolynomialAmplitude (freeActionVertices G ++ treeActionVertices e) coupling legs q :=
  scalePolynomial_amplitude z _ coupling legs q

/-- Coefficientwise g derivative of an actual source vertex. -/
def differentiateCouplingVertex (v : LocalVertex G) : LocalVertex G :=
  { v with
    coefficient := v.coefficient * (v.couplingOrder : ℂ)
    couplingOrder := v.couplingOrder - 1 }

theorem vertexCoupling_hasDerivAt (v : LocalVertex G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (g : ℝ) :
    HasDerivAt (fun x : ℝ => localVertexAmplitude v x legs q)
      (localVertexAmplitude (differentiateCouplingVertex v) g legs q) g := by
  have hc : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) g := by
    simpa using! (Complex.ofRealCLM.hasFDerivAt (x := g)).hasDerivAt
  have hh := (HasDerivAt.const_mul v.coefficient (hc.pow v.couplingOrder)).mul_const
    (localMonomialDerivative v.legs (List.ofFn (fun i => (legs.get i, q i))))
  simpa [localVertexAmplitude, differentiateCouplingVertex, mul_assoc] using! hh

theorem polynomialCoupling_hasDerivAt (terms : List (LocalVertex G))
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (g : ℝ) :
    HasDerivAt (fun x : ℝ => localPolynomialAmplitude terms x legs q)
      (localPolynomialAmplitude (terms.map differentiateCouplingVertex) g legs q) g := by
  induction terms with
  | nil => simpa [localPolynomialAmplitude] using! (hasDerivAt_const g (0 : ℂ))
  | cons v terms ih =>
    simpa [localPolynomialAmplitude] using! (vertexCoupling_hasDerivAt v legs q g).add ih

/-- Actual derivative of the finite polynomial coupling powers in S.
This does not ask for a norm/topology on the infinite superjet algebra. -/
def couplingVariationDensity {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) : FullBV.JetAlgebra G :=
  FullBV.densityOfVertices g
    ((freeActionVertices G ++ treeActionVertices e).map differentiateCouplingVertex)

/-- Finite-dimensional canonical field/source generator. It has ghost
number -1 and engineering degree three; its ST image is the corresponding
field-renormalization direction in the integrated action. -/
def rescalingGenerator (weights : BasicScales) : FullBV.JetAlgebra G :=
  ∑ K : BasicField G, (basicScale weights K : ℂ) •
    (FullBV.jet ⟨.inl K, 0⟩ * FullBV.jet ⟨.inr K, 0⟩)

def canonicalRescalingCounterterm {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (weights : BasicScales) : FullBV.JetAlgebra G :=
  FullBV.classicalSTDensity e g (rescalingGenerator weights)

/-- Power-counting restricted local gauge fermions/canonical generators.
Ghosts and antifields remain actual exterior-valued jet variables. -/
structure LocalGenerator {B : InvariantForm G} (e : ColorFrame B) where
  terms : List (LocalVertex G)
  dimension : ∀ v ∈ terms, v.degree = 3
  ghost : ∀ v ∈ terms, v.ghostNumber = -1
  odd : ∀ v ∈ terms, v.parity = true
  color : LocalColorInvariant e terms
  euclidean : LocalEuclideanInvariant terms

/-- A precise classification TARGET, rather than an asserted cohomology
classification theorem. All terms are actual same-action density operations. -/
def IsParametricCounterterm {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : FullBV.JetAlgebra G) (couplingChange : ℝ) (weights : BasicScales)
    (gaugeFermion : LocalGenerator e) : Prop :=
  FullBV.localClass P = FullBV.localClass
    ((couplingChange * g : ℂ) • couplingVariationDensity e g +
      canonicalRescalingCounterterm e g weights +
      FullBV.classicalSTDensity e g (FullBV.densityOfVertices g gaugeFermion.terms))

/-- Finite RENORMALIZED parameter germs. The second argument is a formal
hbar variable, kept separate from g. There is no UV-cutoff argument. -/
structure FiniteParameterChange where
  couplingFactor : ℝ → ℝ → ℝ → ℝ
  fields : ℝ → ℝ → ℝ → BasicScales
  coupling_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × ℝ) => couplingFactor z.1 z.2.1 z.2.2) (Set.Ioi 0 ×ˢ Set.univ)
  gauge_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × ℝ) => (fields z.1 z.2.1 z.2.2).gauge) (Set.Ioi 0 ×ˢ Set.univ)
  ghost_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × ℝ) => (fields z.1 z.2.1 z.2.2).ghost) (Set.Ioi 0 ×ˢ Set.univ)
  antighost_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × ℝ) => (fields z.1 z.2.1 z.2.2).antighost) (Set.Ioi 0 ×ˢ Set.univ)
  auxiliary_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × ℝ) => (fields z.1 z.2.1 z.2.2).auxiliary) (Set.Ioi 0 ×ˢ Set.univ)
  coupling_classical : ∀ μ g, 0 < μ → couplingFactor μ 0 g = 1
  fields_classical : ∀ μ g, 0 < μ → fields μ 0 g = ⟨1,1,1,1⟩
  coupling_free : ∀ μ h, 0 < μ → couplingFactor μ h 0 = 1
  fields_free : ∀ μ h, 0 < μ → fields μ h 0 = ⟨1,1,1,1⟩
  invertible_germ : ∀ μ, 0 < μ → ∃ r : ℝ, 0 < r ∧
    ∀ h g, |h| + |g| < r → InvertibleScales (fields μ h g)

def FiniteParameterChange.coupling (change : FiniteParameterChange) (μ h g : ℝ) : ℝ :=
  g * change.couplingFactor μ h g

/-- Exact finite Cauchy/Taylor formula for an ORDERED-FUNCTIONAL coordinate
pullback, such as the 1PI action. This is NOT a CAC scheme transport: that
requires the source/Gaussian/Legendre conversion and quadratic compensation.
The hbar series is never resummed at hbar=1. -/
def FiniteParameterChange.functionalPullback (change : FiniteParameterChange) (μ : ℝ)
    (L : ℝ → FlowFamily G) : ℝ → FlowFamily G :=
  fun g loop Λ UV legs q => ∑ r : Fin (loop+1),
    (Nat.factorial (loop-r.val) : ℂ)⁻¹ *
      iteratedDeriv (loop-r.val) (fun h : ℝ =>
        externalFactor (change.fields μ h g) legs *
          L (change.coupling μ h g) r.val Λ UV legs q) 0

/-- The ordered-functional pullback preserves its classical input.
This does not identify it with a connected-amputated physical scheme map. -/
theorem FiniteParameterChange.functionalPullback_tree (change : FiniteParameterChange)
    (μ : ℝ) (hμ : 0 < μ) (L : ℝ → FlowFamily G) (g : ℝ) :
    change.functionalPullback μ L g 0 = L g 0 := by
  funext Λ UV legs q
  simp [FiniteParameterChange.functionalPullback,
    FiniteParameterChange.coupling, change.coupling_classical μ g hμ,
    change.fields_classical μ g hμ]

/-- The scale-transport expression at fixed hbar. Physical equality with
another engine's beta requires the SAME-theory comparison and dictionary. -/
def FiniteParameterChange.transportedBeta (change : FiniteParameterChange)
    (beta : ℝ → ℝ → ℝ → ℝ) (μ h g : ℝ) : ℝ :=
  μ * deriv (fun s => change.coupling s h g) μ +
    deriv (fun x => change.coupling μ h x) g * beta μ h g

end YangMills.FieldParameter
