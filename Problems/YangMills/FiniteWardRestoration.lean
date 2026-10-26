import Problems.YangMills.InsertionWardTransport
import Problems.YangMills.WardRenormalizationBinding

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Finite cohomological Ward-restoration steps of the same flow

FHH 1511.09425, (354)--(359), printed pp.68--69, subtracts a finite local
primitive at the first nonvanishing loop order and then re-solves the flow.
The anomaly has dimension five and ghost number one; its primitive has
dimension four and ghost number zero (the sentence below (356) has a typo).
This module keeps the regulated defect, its primitive and the UV boundary
shift explicit. It does not assert finite-cutoff Ward closure or the
classification theorem needed for multiplicative bare parameters.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
open scoped BigOperators
namespace YangMills.FiniteWard
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Engineering compensation for a finite local action density. -/
def dimensionCompensate (μ : ℝ) (terms : List (LocalVertex G)) : List (LocalVertex G) :=
  terms.map (fun v => { v with coefficient := (μ : ℂ) ^ (4-v.degree) * v.coefficient })

/-- A finite local action correction obeys the same actual group/O(4)
symmetries and marginal power counting as the source boundary problem. -/
structure FilteredCorrection {B : InvariantForm G} (e : ColorFrame B) (order : ℕ) where
  terms : List (LocalVertex G)
  dimension : ∀ v ∈ terms, v.degree ≤ 4
  nonvacuum : ∀ v ∈ terms, v.legs ≠ []
  ghost : ∀ v ∈ terms, v.ghostNumber = 0
  even : ∀ v ∈ terms, v.parity = false
  coupling : ∀ v ∈ terms, v.couplingOrder + 2 = v.legs.length + 2 * order
  color : ∀ μ, LocalColorInvariant e (dimensionCompensate μ terms)
  euclidean : ∀ μ, LocalEuclideanInvariant (dimensionCompensate μ terms)

/-- Explicit engineering-dimension compensation. The dimensionless finite
coefficient may depend smoothly on mu; relevant monomials are NOT excluded. -/
def FilteredCorrection.atScale {B : InvariantForm G} {e : ColorFrame B} {k : ℕ}
    (B0 : FilteredCorrection e k) (μ : ℝ) : List (LocalVertex G) :=
  dimensionCompensate μ B0.terms

def correctionDensity {B : InvariantForm G} {e : ColorFrame B} {k : ℕ}
    (B0 : FilteredCorrection e k) (μ g : ℝ) : FullBV.JetAlgebra G :=
  FullBV.densityOfVertices g (B0.atScale μ)

/-- The cohomological anomaly to be cancelled is COMPUTED with the same
master action and its full BV bracket; it is not a freely supplied tensor. -/
def primitiveAnomalyDensity {B : InvariantForm G} (e : ColorFrame B) {k : ℕ}
    (B0 : FilteredCorrection e k) (μ g : ℝ) : FullBV.JetAlgebra G :=
  FullBV.classicalSTDensity e g (correctionDensity B0 μ g)

/-- Loopwise finite bare boundary shift. Its auxiliary values away from
Lambda=Lambda0 are not asserted to solve any flow equation. -/
def boundaryShift (L : FlowFamily G) (order : ℕ) (P : OrderedAmplitude G) : FlowFamily G :=
  fun loop Λ Λ0 legs q => L loop Λ Λ0 legs q - if loop = order then P legs q else 0

/-- Source (357), to the order under consideration. Higher loop boundaries
remain available for the later recursive steps. The AFTER family must
separately solve the same actual coefficient flow. -/
def UVBoundaryStep (before after : FlowFamily G) (order : ℕ)
    (P : OrderedAmplitude G) : Prop :=
  ∀ loop, loop ≤ order → ∀ UV : ℝ, 0 < UV → ∀ legs q,
    after loop UV UV legs q = boundaryShift before order P loop UV UV legs q

/-- This is the actual source action anomaly boundary problem; no anomaly
UV seed is selected independently of the background. -/
structure ActionAnomalyFlow (background anomaly : FlowFamily G) : Prop where
  bare_integrable : BVContractionIntegrability background
  ultraviolet : ∀ loop UV, 0 < UV → anomaly loop UV UV = bareActionWardDefect background loop UV
  smooth : ∀ loop Λ UV legs, 0 < Λ → Λ ≤ UV → ContDiff ℝ ∞ (anomaly loop Λ UV legs)
  jets_continuous : ∀ loop UV legs (directions : List (Fin legs.length × Fin 4)) q,
    ContinuousOn (fun Λ : ℝ => momentumJet directions (anomaly loop Λ UV legs) q) (Set.Ioc 0 UV)
  integrable : ∀ loop Λ UV legs q, 0 < Λ → Λ < UV →
    Integrable (linearFlowIntegrand anomaly loop Λ UV legs q)
  flow : ∀ loop Λ UV legs q, 0 < Λ → Λ < UV →
    HasDerivAt (fun scale : ℝ => anomaly loop scale UV legs q)
      (insertionHomogeneousRHS background anomaly loop Λ UV legs q) Λ

theorem regulatedFreeWardAmplitude_add (UV : ℝ) (F H : OrderedAmplitude G) :
    regulatedFreeWardAmplitude UV (F + H) =
      regulatedFreeWardAmplitude UV F + regulatedFreeWardAmplitude UV H := by
  funext legs q
  simp only [regulatedFreeWardAmplitude, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem regulatedBVSplit_add_left (parity : Bool) (F H K : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) :
    regulatedBVSplit parity (F + H) K loop leftLoop Λ UV legs q s =
      regulatedBVSplit parity F K loop leftLoop Λ UV legs q s +
      regulatedBVSplit parity H K loop leftLoop Λ UV legs q s := by
  simp only [regulatedBVSplit, Pi.add_apply, mul_add, add_mul, add_sub_add_comm,
    Finset.sum_add_distrib]

theorem regulatedBVSplit_add_right (parity : Bool) (F H K : FlowFamily G)
    (loop leftLoop : ℕ) (Λ UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) :
    regulatedBVSplit parity F (H + K) loop leftLoop Λ UV legs q s =
      regulatedBVSplit parity F H loop leftLoop Λ UV legs q s +
      regulatedBVSplit parity F K loop leftLoop Λ UV legs q s := by
  simp only [regulatedBVSplit, Pi.add_apply, mul_add, add_sub_add_comm,
    Finset.sum_add_distrib]


theorem regulatedBVBracket_add_left (parity : Bool) (F H K : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) :
    regulatedBVBracket parity (F + H) K loop Λ UV =
      regulatedBVBracket parity F K loop Λ UV + regulatedBVBracket parity H K loop Λ UV := by
  funext legs q
  simp only [regulatedBVBracket, regulatedBVSplit_add_left, Finset.sum_add_distrib, Pi.add_apply]

theorem regulatedBVBracket_add_right (parity : Bool) (F H K : FlowFamily G)
    (loop : ℕ) (Λ UV : ℝ) :
    regulatedBVBracket parity F (H + K) loop Λ UV =
      regulatedBVBracket parity F H loop Λ UV + regulatedBVBracket parity F K loop Λ UV := by
  funext legs q
  simp only [regulatedBVBracket, regulatedBVSplit_add_right, Finset.sum_add_distrib, Pi.add_apply]

theorem regulatedBVLaplacianIntegrand_add (parity : Bool) (UV : ℝ)
    (F H : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) :
    regulatedBVLaplacianIntegrand parity UV (F + H) legs q p =
      regulatedBVLaplacianIntegrand parity UV F legs q p +
      regulatedBVLaplacianIntegrand parity UV H legs q p := by
  simp only [regulatedBVLaplacianIntegrand, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]

/-- Genuine additivity of the regulated BV integral. -/
theorem regulatedBVLaplacian_add (parity : Bool) (UV : ℝ)
    (F H : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime)
    (hF : Integrable (regulatedBVLaplacianIntegrand parity UV F legs q))
    (hH : Integrable (regulatedBVLaplacianIntegrand parity UV H legs q)) :
    regulatedBVLaplacian parity UV (F + H) legs q =
      regulatedBVLaplacian parity UV F legs q + regulatedBVLaplacian parity UV H legs q := by
  unfold regulatedBVLaplacian
  simp only [regulatedBVLaplacianIntegrand_add]
  exact integral_add hF hH

/-- Exact finite-cutoff change of the SAME bare Ward defect. Quadratic and
hbar-Delta terms are retained; no unregulated/classical replacement is made. -/
theorem bareActionWardDefect_add (L D : FlowFamily G) (loop : ℕ) (UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hUV : 0 < UV) (hq : BalancedMomenta legs q)
    (hL : BVContractionIntegrability L) (hD : BVContractionIntegrability D) :
    bareActionWardDefect (L + D) loop UV legs q =
      bareActionWardDefect L loop UV legs q +
        regulatedFreeWardAmplitude UV (D loop UV UV) legs q +
        (1/2 : ℂ) * (regulatedBVBracket false L D loop UV UV legs q +
          regulatedBVBracket false D L loop UV UV legs q +
          regulatedBVBracket false D D loop UV UV legs q) +
        (if loop = 0 then 0 else
          regulatedBVLaplacian false UV (D (loop-1) UV UV) legs q) := by
  unfold bareActionWardDefect
  rw [regulatedBVBracket_add_left, regulatedBVBracket_add_right,
    regulatedBVBracket_add_right]
  have hf := regulatedFreeWardAmplitude_add UV (L loop UV UV) (D loop UV UV)
  change regulatedFreeWardAmplitude UV ((L+D) loop UV UV) = _ at hf
  rw [hf]
  by_cases hl : loop = 0
  · simp only [hl, ↓reduceIte, Pi.add_apply]
    ring
  · have hd := regulatedBVLaplacian_add false UV (L (loop-1) UV UV)
      (D (loop-1) UV UV) legs q (hL.laplacian _ UV legs q hUV hq)
      (hD.laplacian _ UV legs q hUV hq)
    change regulatedBVLaplacian false UV ((L+D) (loop-1) UV UV) legs q = _ at hd
    simp only [hl, ↓reduceIte]
    rw [hd]
    simp only [Pi.add_apply]
    ring

/-- A bare defect at loop n depends only on the UV action prefix through
n. Thus a finite order-n restoration cannot be evaded by changing later loops. -/
theorem bareActionWardDefect_congr_prefix (L H : FlowFamily G) (loop : ℕ) (UV : ℝ)
    (h : ∀ j, j ≤ loop → L j UV UV = H j UV UV) :
    bareActionWardDefect L loop UV = bareActionWardDefect H loop UV := by
  have hb : regulatedBVBracket false L L loop UV UV =
      regulatedBVBracket false H H loop UV UV := by
    funext legs q
    unfold regulatedBVBracket
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro s _
    unfold regulatedBVSplit
    rw [h l.val (by omega), h (loop-l.val) (Nat.sub_le _ _)]
  unfold bareActionWardDefect
  rw [h loop (Nat.le_refl _), hb, h (loop-1) (Nat.sub_le _ _)]

/-- Actual coupling Taylor coefficient paired against a compact balanced
momentum test. In particular the conservation delta is retained. -/
def balancedPairingIntegrand (F : ℝ → FlowFamily G) (order loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 0 legs)
    (q : Fin (legs.length - 1) → Spacetime) : ℂ :=
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    F g loop Λ UV legs (balancedFromReduced legs q)) 0) *
    test ((fun i : Fin 0 => Fin.elim0 i), balancedFromReduced legs q)

def balancedPairing (F : ℝ → FlowFamily G) (order loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 0 legs) : ℂ :=
  ∫ q, balancedPairingIntegrand F order loop Λ UV legs test q

/-- Ordered weak UV/IR vanishing on ALL nonexceptional compact tests.
The intermediate UV limit is fixed by its defining convergence. -/
def UVIRVanishes (F : ℝ → FlowFamily G) (loop : ℕ) : Prop :=
  ∀ order legs (test : JointMomentumTest 0 legs), HasCompactSupport test →
    NonexceptionalSupport .wardSingle test →
    (∀ Λ, 0 < Λ → ∀ᶠ UV in atTop,
      Λ ≤ UV ∧ Integrable (balancedPairingIntegrand F order loop Λ UV legs test)) ∧
    ∃ limit : ℝ → ℂ,
      (∀ Λ, 0 < Λ → Tendsto (fun UV => balancedPairing F order loop Λ UV legs test)
        atTop (nhds (limit Λ))) ∧
      Tendsto limit (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- At the first nonzero anomaly order only the tree insertion of s B0
contributes. Its density uses the actual same-G master action. -/
def leadingPrimitiveInsertion {B : InvariantForm G} (e : ColorFrame B)
    (L : ℝ → InsertedFlowFamily G) (μ : ℝ) {k : ℕ} (B0 : FilteredCorrection e k) :
    ℝ → FlowFamily G :=
  fun g loop Λ UV => if loop = k then
    boundedDensityInsertion (L g) 6 (primitiveAnomalyDensity e B0 μ g) 0 0 Λ UV else 0

/-- Source (355)--(356) against the anomaly of the same bare regulated
defect. No independent local anomaly coefficients are chosen. -/
def IsLeadingPrimitive {B : InvariantForm G} (e : ColorFrame B)
    (L : ℝ → InsertedFlowFamily G) (anomaly : ℝ → FlowFamily G)
    (μ : ℝ) {k : ℕ} (B0 : FilteredCorrection e k) : Prop :=
  0 < k ∧ (∀ loop, loop < k → UVIRVanishes anomaly loop) ∧
    UVIRVanishes (anomaly - leadingPrimitiveInsertion e L μ B0) k

/-- Source (357) with the actual UV shift. Vanishing of the NEXT Ward order
is a theorem to prove from these data, not an assumed conclusion. -/
structure RestorationStep {B : InvariantForm G} (e : ColorFrame B)
    (before after : ScaleCouplingFamily G)
    (L : ℝ → ℝ → InsertedFlowFamily G)
    (anomaly : ℝ → ℝ → FlowFamily G) (order : ℕ) where
  correction : ℝ → FilteredCorrection e order
  correction_smooth : ∀ legs, ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × (Fin legs.length → Spacetime)) =>
      localPolynomialAmplitude ((correction z.1).atScale z.1) z.2.1 legs z.2.2)
    (Set.Ioi 0 ×ˢ Set.univ)
  same_background : ∀ μ g, before μ g = L μ g []
  same_lower_orders : ∀ μ g loop, loop < order → before μ g loop = after μ g loop
  anomaly_flow : ∀ μ g, 0 < μ → ActionAnomalyFlow (before μ g) (anomaly μ g)
  anomaly_joint_smooth : ∀ μ loop Λ UV legs, 0 < μ → 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (fun z : ℝ × (Fin legs.length → Spacetime) => anomaly μ z.1 loop Λ UV legs z.2)
  primitive : ∀ μ, 0 < μ → IsLeadingPrimitive e (L μ) (anomaly μ) μ (correction μ)
  boundary : ∀ μ g, 0 < μ → UVBoundaryStep (before μ g) (after μ g) order
    (localPolynomialAmplitude ((correction μ).atScale μ) g)

/-- The AFTER anomaly seed is the actual shifted regulated defect, to the
order under construction. No independent anomaly seed can be selected. -/
theorem RestorationStep.bare_defect {B : InvariantForm G} {e : ColorFrame B}
    {before after : ScaleCouplingFamily G} {L : ℝ → ℝ → InsertedFlowFamily G}
    {anomaly : ℝ → ℝ → FlowFamily G} {order : ℕ}
    (step : RestorationStep e before after L anomaly order)
    (μ g UV : ℝ) (hμ : 0 < μ) (hUV : 0 < UV) :
    bareActionWardDefect (after μ g) order UV =
      bareActionWardDefect (boundaryShift (before μ g) order
        (localPolynomialAmplitude ((step.correction μ).atScale μ) g)) order UV := by
  apply bareActionWardDefect_congr_prefix
  intro j hj
  funext legs q
  exact step.boundary μ g hμ j hj UV hUV legs q

/-- A filtered finite renormalization prescription can normalize relevant
jets at mu too (FHH discussion preceding (94)); it must not retain the
premature relevant-IR-zero condition after a relevant finite Ward shift. -/
def filteredNormalization {B : InvariantForm G} (e : ColorFrame B)
    (scheme : (loop : ℕ) → FilteredCorrection e loop) (μ : ℝ) (loop : ℕ) (g : ℝ) :
    OrderedAmplitude G :=
  if loop = 0 then treeVertexAmplitude e g else
    localPolynomialAmplitude ((scheme loop).atScale μ) g

/-- Same fixed differential flow, statistics and irrelevant UV boundary,
with explicit relevant/marginal finite normalization at the subtraction scale.
This does not assert existence or physical masslessness of these solutions. -/
structure FilteredCoefficientFlowConditions {B : InvariantForm G} (e : ColorFrame B)
    (scheme : ℝ → (loop : ℕ) → FilteredCorrection e loop)
    (A : ScaleCouplingFamily G) : Prop where
  momentum_smooth : ∀ μ g loop Λ Λ0 legs,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ ≤ Λ0 →
      ContDiff ℝ ∞ (A μ g loop Λ Λ0 legs)
  coupling_smooth : ∀ μ loop Λ Λ0 legs q,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ ≤ Λ0 →
      ContDiff ℝ ∞ (fun g : ℝ => A μ g loop Λ Λ0 legs q)
  joint_coupling_momentum_smooth : ∀ μ loop Λ Λ0 legs,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ ≤ Λ0 →
      ContDiff ℝ ∞ (fun z : ℝ × (Fin legs.length → Spacetime) =>
        A μ z.1 loop Λ Λ0 legs z.2)
  positive_scale_jet_continuity : ∀ μ g loop Λ0 legs
      (directions : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ Λ0 →
      ContinuousOn (fun Λ : ℝ => momentumJet directions (A μ g loop Λ Λ0 legs) q)
        (Set.Ioc 0 Λ0)
  reduced_extension : ∀ μ g loop Λ Λ0 legs q,
    A μ g loop Λ Λ0 legs q = A μ g loop Λ Λ0 legs (conservingMomenta legs q)
  statistics : ∀ μ g loop Λ Λ0 legs q,
    (totalGhostNumber legs ≠ 0 ∨ oddCount legs % 2 ≠ 0) → A μ g loop Λ Λ0 legs q = 0
  graded_symmetry : ∀ μ g loop Λ Λ0 legs q (π : Equiv.Perm (Fin legs.length)),
    BalancedMomenta legs q →
    A μ g loop Λ Λ0 (permutedLegs legs π) (permutedMomenta legs π q) =
      permutationSign legs π * A μ g loop Λ Λ0 legs q
  vacuum_subtraction : ∀ μ g loop Λ Λ0 q, A μ g loop Λ Λ0 [] q = 0
  no_free_interaction : ∀ μ g Λ Λ0 legs q,
    legs.length ≤ 2 → A μ g 0 Λ Λ0 legs q = 0
  loop_integrable : ∀ μ g loop Λ Λ0 legs q,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ < Λ0 → BalancedMomenta legs q →
      Integrable (linearFlowIntegrand (A μ g) loop Λ Λ0 legs q)
  flow : ∀ μ g loop Λ Λ0 legs q,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ < Λ0 → legs ≠ [] → BalancedMomenta legs q →
      HasDerivAt (fun scale : ℝ => A μ g loop scale Λ0 legs q)
        (backgroundFlowRHS (A μ g) loop Λ Λ0 legs q) Λ
  irrelevant_uv : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      4 < totalDimension legs + directions.length →
      momentumJet directions (A μ g loop Λ0 Λ0 legs) q = 0
  normalization_smooth : ∀ loop legs, ContDiffOn ℝ ∞
    (fun z : ℝ × (ℝ × (Fin legs.length → Spacetime)) =>
      filteredNormalization e (scheme z.1) z.1 loop z.2.1 legs z.2.2)
    (Set.Ioi 0 ×ˢ Set.univ)
  finite_normalization : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      totalDimension legs + directions.length ≤ 4 →
      marginalJet (A μ g) loop μ Λ0 legs directions =
        momentumJet directions
          (fun q => filteredNormalization e (scheme μ) μ loop g legs (conservingMomenta legs q)) 0

/-- A coherent tower, rather than an unrelated full scheme at each order.
Stage n+1 preserves every loop coefficient through n. -/
structure RestorationTower {B : InvariantForm G} (e : ColorFrame B) where
  scheme : ℕ → ℝ → (loop : ℕ) → FilteredCorrection e loop
  background : ℕ → ScaleCouplingFamily G
  inserted : ℕ → ℝ → ℝ → InsertedFlowFamily G
  oversubtracted : ℕ → ℝ → ℝ → OversubtractedFamily G
  anomaly : ℕ → ℝ → ℝ → FlowFamily G
  coefficient_flow : ∀ n, FilteredCoefficientFlowConditions e (scheme n) (background n)
  insertion_flow : ∀ n μ, 0 < μ → CoupledInsertionFlowConditions (background n μ)
    (inserted n μ) (oversubtracted n μ) μ
  step : ∀ n, RestorationStep e (background n) (background (n+1))
    (inserted n) (anomaly n) (n+1)

/-- Loop l is read from stage l. No infinite sum is taken. -/
def RestorationTower.diagonal {B : InvariantForm G} {e : ColorFrame B}
    (T : RestorationTower e) : ScaleCouplingFamily G :=
  fun μ g loop => T.background loop μ g loop

theorem RestorationTower.prefix {B : InvariantForm G} {e : ColorFrame B}
    (T : RestorationTower e) (a b loop : ℕ) (hab : a ≤ b) (hla : loop ≤ a)
    (μ g : ℝ) : T.background a μ g loop = T.background b μ g loop := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ n han ih =>
    rw [ih]
    exact (T.step n).same_lower_orders μ g loop (by omega)

theorem RestorationTower.diagonal_eq {B : InvariantForm G} {e : ColorFrame B}
    (T : RestorationTower e) (n loop : ℕ) (hl : loop ≤ n) (μ g : ℝ) :
    T.diagonal μ g loop = T.background n μ g loop :=
  T.prefix loop n loop hl (Nat.le_refl _) μ g

end YangMills.FiniteWard
