import Problems.YangMills.FreeWardExtraction
import Problems.YangMills.OversubtractedFlow

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Same-flow joint weak UV/IR limits for quantum Ward identities

The distribution variables include ALL insertion positions and ALL external
momenta. This is necessary for contact terms: pointwise values at distinct
insertion positions cannot represent derivatives of coincidence delta functions.
Only compact Schwartz tests are observed; global tempered growth is not imposed.
IR limits and restored identities are tested only inside the source
nonexceptional external-momentum region. Values outside this region remain
unidentified until an additional distributional extension is constructed.
Bulk limits are coefficientwise in actual g derivatives and hbar loop order,
with UV removed first and the positive IR cutoff then sent to zero. Insertion
contact extensions still need the explicit local counterterm prescription.
-/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

abbrev JointMomentumTest (arity : ℕ) (legs : List (ExternalLeg G)) :=
  SchwartzMap ((Fin arity → Spacetime) × (Fin legs.length → Spacetime)) ℂ
abbrev JointMomentumDistribution (arity : ℕ) (legs : List (ExternalLeg G)) :=
  JointMomentumTest arity legs →ₗ[ℂ] ℂ

/-- Local distribution continuity on every compact configuration/momentum
support. In particular exceptional momenta and contact diagonals are included. -/
def IsJointLocalDistribution {arity : ℕ} {legs : List (ExternalLeg G)}
    (T : JointMomentumDistribution arity legs) : Prop :=
  ∀ K : Set ((Fin arity → Spacetime) × (Fin legs.length → Spacetime)), IsCompact K →
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : JointMomentumTest arity legs,
      tsupport f ⊆ K →
      ‖T f‖ ≤ C * ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j f

inductive ContinuumKind where
  | single
  | oversubtracted (degree : ℕ)
  | disconnected (degree : ℕ)
  | wardSingle
  | wardDisconnected (degree : ℕ)
  deriving DecidableEq

def ContinuumKind.isBackgroundBranch : ContinuumKind → Bool
  | .single | .wardSingle => true
  | _ => false

/-- The single/background branch is used only at arity zero or one.
Multiple insertions are fixed by G_D=product(single L)-hbar F_D; an unrelated
free multiple-insertion connected family cannot enter the Ward calculation. -/
def finiteContinuumFamily (kind : ContinuumKind) (L : InsertedFlowFamily G)
    (F : OversubtractedFamily G) (input : List (PositionedInsertion G)) : FlowFamily G :=
  match kind with
  | .single => if input.length ≤ 1 then L input else 0
  | .oversubtracted D => if input.isEmpty then 0 else F D input
  | .disconnected D => if input.isEmpty then flowUnit else disconnectedFunctional L F D input
  | .wardSingle => fun loop Λ Λ0 =>
      freeWardAmplitude ((if input.length ≤ 1 then L input else 0) loop Λ Λ0)
  | .wardDisconnected D => fun loop Λ Λ0 =>
      freeWardAmplitude ((if input.isEmpty then flowUnit else
        disconnectedFunctional L F D input) loop Λ Λ0)

def positionedInputs {arity : ℕ} (labels : Fin arity → LocalMonomial G)
    (positions : Fin arity → Spacetime) : List (PositionedInsertion G) :=
  List.ofFn (fun i => ⟨labels i, positions i⟩)

/-- Coupling coefficients are genuine derivatives of the same finite flow
family, BEFORE the limits. The two formal indices are not conflated. -/
def finiteJointIntegrand (kind : ContinuumKind) (L : ℝ → InsertedFlowFamily G)
    (F : ℝ → OversubtractedFamily G) (order loop : ℕ) (Λ Λ0 : ℝ)
    {arity : ℕ} (labels : Fin arity → LocalMonomial G) (legs : List (ExternalLeg G))
    (test : JointMomentumTest arity legs)
    (xq : (Fin arity → Spacetime) × (Fin legs.length → Spacetime)) : ℂ :=
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    finiteContinuumFamily kind (L g) (F g) (positionedInputs labels xq.1)
      loop Λ Λ0 legs xq.2) 0) * test xq

/-- Restore the overall conservation delta for the background: the
last momentum is dependent, while inserted amplitudes use all momenta. -/
def balancedFromReduced (legs : List (ExternalLeg G))
    (q : Fin (legs.length - 1) → Spacetime) : Fin legs.length → Spacetime :=
  fun i => if h : i.val + 1 < legs.length then q ⟨i.val, by omega⟩
    else -(∑ j : Fin (legs.length - 1), q j)

def finiteBackgroundIntegrand (kind : ContinuumKind) (L : ℝ → InsertedFlowFamily G)
    (F : ℝ → OversubtractedFamily G) (order loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 0 legs)
    (q : Fin (legs.length - 1) → Spacetime) : ℂ :=
  let balanced := balancedFromReduced legs q
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    finiteContinuumFamily kind (L g) (F g) [] loop Λ Λ0 legs balanced) 0) *
      test ((fun i : Fin 0 => Fin.elim0 i), balanced)

def finiteJointPairing (kind : ContinuumKind) (L : ℝ → InsertedFlowFamily G)
    (F : ℝ → OversubtractedFamily G) (order loop : ℕ) (Λ Λ0 : ℝ)
    {arity : ℕ} (labels : Fin arity → LocalMonomial G) (legs : List (ExternalLeg G))
    (test : JointMomentumTest arity legs) : ℂ :=
  if h : arity = 0 ∧ kind.isBackgroundBranch = true then
    ∫ q, finiteBackgroundIntegrand kind L F order loop Λ Λ0 legs
      (by simpa only [h.1] using test) q
  else ∫ xq, finiteJointIntegrand kind L F order loop Λ Λ0 labels legs test xq

/-- Bulk observations avoid insertion coincidences, but do not avoid any
external momenta. Local contact extensions require additional finite local
counterterm/Taylor conditions; bulk limits must not silently fix them. -/
def OffInsertionDiagonals {arity : ℕ} {legs : List (ExternalLeg G)}
    (test : JointMomentumTest arity legs) : Prop :=
  ∀ xq ∈ tsupport test, ∀ i j : Fin arity, i ≠ j → xq.1 i ≠ xq.1 j

/-- Source η/barη nonexceptionality: insertion amplitudes have no
momentum-conservation constraint, so EVERY nonempty subsum must be nonzero.
Background amplitudes omit their dependent last momentum in η (eqs.25–28).
The vacuum η()=0 and one-leg η(q)=|q| conventions are explicit. -/
def NonexceptionalMomenta (background : Bool) {n : ℕ}
    (q : Fin n → Spacetime) : Prop :=
  if background then
    if n = 0 then False else
    if n = 1 then ∀ i : Fin n, q i ≠ 0 else
      ∀ S : Finset (Fin n), S.Nonempty →
        (∀ i ∈ S, i.val + 1 < n) → ∑ i ∈ S, q i ≠ 0
  else ∀ S : Finset (Fin n), S.Nonempty → ∑ i ∈ S, q i ≠ 0

/-- Only compact supports wholly inside the source nonexceptional open
region are used in the IR removal. No extension across its complement is
silently inferred. -/
def NonexceptionalSupport {arity : ℕ} {legs : List (ExternalLeg G)}
    (kind : ContinuumKind) (test : JointMomentumTest arity legs) : Prop :=
  ∀ xq ∈ tsupport test,
    NonexceptionalMomenta (arity == 0 && kind.isBackgroundBranch) xq.2

/-- Both levels of limits are mathematical objects; the compatibility
conditions below identify bulk/nonexceptional compact-test values with the
same finite-cutoff flow calculation. Contact and exceptional extensions are
not fixed by this module and must not be read as physical predictions. -/
structure WardContinuumData (G : CompactSimpleGaugeGroup) where
  ultraviolet : ContinuumKind → ℕ → ℕ → ℝ → {arity : ℕ} →
    (Fin arity → LocalMonomial G) → (legs : List (ExternalLeg G)) →
      JointMomentumDistribution arity legs
  physical : ContinuumKind → ℕ → ℕ → {arity : ℕ} →
    (Fin arity → LocalMonomial G) → (legs : List (ExternalLeg G)) →
      JointMomentumDistribution arity legs

namespace WardContinuumData

structure BulkCompatible (W : WardContinuumData G) (L : ℝ → InsertedFlowFamily G)
    (F : ℝ → OversubtractedFamily G) : Prop where
  coupling_momentum_smooth : ∀ kind input loop Λ Λ0, 0 < Λ → Λ ≤ Λ0 →
    ∀ legs, ContDiff ℝ ∞ (fun z : ℝ × (Fin legs.length → Spacetime) =>
      finiteContinuumFamily kind (L z.1) (F z.1) input loop Λ Λ0 legs z.2)
  finite_integrable : ∀ kind order loop Λ Λ0, 0 < Λ → Λ ≤ Λ0 →
    ∀ {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs
      (test : JointMomentumTest arity legs), HasCompactSupport test →
      Integrable (finiteJointIntegrand kind L F order loop Λ Λ0 labels legs test)
  background_integrable : ∀ kind order loop Λ Λ0, 0 < Λ → Λ ≤ Λ0 →
    kind.isBackgroundBranch = true → ∀ legs (test : JointMomentumTest 0 legs),
      HasCompactSupport test →
      Integrable (finiteBackgroundIntegrand kind L F order loop Λ Λ0 legs test)
  ultraviolet_local : ∀ kind order loop Λ, 0 < Λ →
    ∀ {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs,
      IsJointLocalDistribution (W.ultraviolet kind order loop Λ labels legs)
  physical_local : ∀ kind order loop {arity : ℕ}
      (labels : Fin arity → LocalMonomial G) legs,
    IsJointLocalDistribution (W.physical kind order loop labels legs)
  ultraviolet_limit : ∀ kind order loop Λ, 0 < Λ →
    ∀ {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs
      (test : JointMomentumTest arity legs), HasCompactSupport test → OffInsertionDiagonals test →
      Tendsto (fun Λ0 : ℝ => finiteJointPairing kind L F order loop Λ Λ0 labels legs test)
        atTop (nhds (W.ultraviolet kind order loop Λ labels legs test))
  infrared_limit : ∀ kind order loop {arity : ℕ}
      (labels : Fin arity → LocalMonomial G) legs (test : JointMomentumTest arity legs),
    HasCompactSupport test → OffInsertionDiagonals test → NonexceptionalSupport kind test →
      Tendsto (fun Λ : ℝ => W.ultraviolet kind order loop Λ labels legs test)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W.physical kind order loop labels legs test))

end WardContinuumData

/-- A compact probe merely chooses coordinates in the SAME distribution
space. Invertibility plus the full Ward identity, not the selected probes
alone, identifies local quantum Ward coefficients. -/
structure WardProbe (G : CompactSimpleGaugeGroup) where
  legs : List (ExternalLeg G)
  test : JointMomentumTest 1 legs
  compact : HasCompactSupport test
  nonexceptional : NonexceptionalSupport .single test

abbrev BigradedMatrix (rows cols : ℕ) :=
  ℕ → ℕ → Matrix (Fin rows) (Fin cols) ℂ

def continuumNormalizationMatrix {n : ℕ} (W : WardContinuumData G)
    (labels : Fin n → LocalMonomial G) (probes : Fin n → WardProbe G) :
    BigradedMatrix n n :=
  fun order loop row col =>
    W.physical .single order loop (fun _ : Fin 1 => labels col)
      (probes row).legs (probes row).test

def continuumWardMatrix {rows cols : ℕ} (W : WardContinuumData G)
    (inputs : Fin cols → LocalMonomial G)
    (probes : Fin rows → WardProbe G) : BigradedMatrix rows cols :=
  fun order loop row col =>
    W.physical .wardSingle order loop (fun _ : Fin 1 => inputs col)
      (probes row).legs (probes row).test

/-- Triangular inverse in TOTAL formal degree, with separate g/hbar indices.
Every recursive term has strictly smaller total degree. -/
def inverseBigradedMatrix {n : ℕ} (Z : BigradedMatrix n n) (order loop : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  if order = 0 ∧ loop = 0 then (Z 0 0)⁻¹ else
    -(Z 0 0)⁻¹ * ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
      if h : a.val = 0 ∧ b.val = 0 then 0 else
        Z a.val b.val * inverseBigradedMatrix Z (order - a.val) (loop - b.val)
termination_by order + loop
decreasing_by
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- Exhaustive finite slices and probes are witness coordinate choices.
Their values are actual compact tests; they never supply a quantum
 differential or contact coefficients. -/
structure WardCoordinateData (G : CompactSimpleGaugeGroup) where
  slice : (D : ℕ) → ExhaustiveMonomialSlice G D
  probe : (D : ℕ) → Fin (slice D).count → WardProbe G

/-- Rectangular D→D+1 coordinate extraction Z_{D+1}^{-1}W.
The source Ward action and all normalization entries come from W's
same-flow physical weak limits. -/
def continuumWardCoordinates (W : WardContinuumData G) (E : WardCoordinateData G)
    (D order loop : ℕ) :
    Matrix (Fin (E.slice (D + 1)).count) (Fin (E.slice D).count) ℂ :=
  ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
    inverseBigradedMatrix
      (continuumNormalizationMatrix W (E.slice (D + 1)).label (E.probe (D + 1))) a.val b.val *
      continuumWardMatrix W (E.slice D).label
        (E.probe (D + 1)) (order - a.val) (loop - b.val)

/-- No singular totalized inverse can be used to erase a Ward defect. -/
def WardCoordinateNonsingular (W : WardContinuumData G) (E : WardCoordinateData G) : Prop :=
  ∀ D, (continuumNormalizationMatrix W (E.slice D).label (E.probe D) 0 0).det ≠ 0

/-- Full single-insertion Ward identity on every compact joint test. This
checks the generated rectangular coordinates throughout the nonexceptional
region, beyond the selected probe set. Extension to exceptional momenta is
separate distributional work. -/
def RestoredSingleWardIdentity (W : WardContinuumData G) (E : WardCoordinateData G) : Prop :=
  WardCoordinateNonsingular W E ∧ ∀ D order loop col legs
      (test : JointMomentumTest 1 legs), HasCompactSupport test →
      NonexceptionalSupport .single test →
    W.physical .wardSingle order loop (fun _ : Fin 1 => (E.slice D).label col) legs test =
      ∑ row : Fin (E.slice (D + 1)).count,
        ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
          continuumWardCoordinates W E D a.val b.val row col *
            W.physical .single (order - a.val) (loop - b.val)
              (fun _ : Fin 1 => (E.slice (D + 1)).label row) legs test

/-- The action Ward identity is imposed on the SAME background branch,
not an unrelated abstract action. It is a fixed equation to establish. -/
def RestoredActionWardIdentity (W : WardContinuumData G) : Prop :=
  ∀ order loop legs (test : JointMomentumTest 0 legs), HasCompactSupport test →
    NonexceptionalSupport .wardSingle test →
    W.physical .wardSingle order loop (fun i : Fin 0 => Fin.elim0 i) legs test = 0

end YangMills.PerturbativeFlow
