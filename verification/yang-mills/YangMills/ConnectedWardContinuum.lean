import YangMills.ConnectedInsertionFlow
import YangMills.WardContinuum

/-!
# Same-flow connected Ward distributions

The full Ward hierarchy (FHH288) acts on connected insertion amplitudes,
not only their single-insertion restriction. This module identifies every
bulk value with the SAME connected flow, whose cumulants are linked to G_0.
Contact extensions are local distributions constrained separately by full
Ward/contact identities; no nonexistent raw UV limit on coincident tests is
required. Infrared removal remains on the source nonexceptional region.
-/
noncomputable section
open scoped ContDiff
open Filter MeasureTheory
namespace YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

def connectedWardFamily (ward : Bool) (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) : FlowFamily G :=
  fun loop Λ UV => if ward then freeWardAmplitude (L input loop Λ UV)
    else L input loop Λ UV

def connectedJointIntegrand (ward : Bool) (L : ℝ → InsertedFlowFamily G)
    (order loop : ℕ) (Λ UV : ℝ) {arity : ℕ} (labels : Fin arity → LocalMonomial G)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest arity legs)
    (xq : (Fin arity → Spacetime) × (Fin legs.length → Spacetime)) : ℂ :=
  ((Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ =>
    connectedWardFamily ward (L g) (positionedInputs labels xq.1) loop Λ UV legs xq.2) 0) * test xq

/-- The empty-list background retains its overall momentum delta, using
all n-1 independent momenta; inserted branches use all n external momenta. -/
def connectedJointPairing (ward : Bool) (L : ℝ → InsertedFlowFamily G)
    (order loop : ℕ) (Λ UV : ℝ) {arity : ℕ} (labels : Fin arity → LocalMonomial G)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest arity legs) : ℂ :=
  if arity = 0 then
    finiteJointPairing (if ward then .wardSingle else .single) L (fun _ _ _ _ _ _ _ _ => (0 : ℂ))
      order loop Λ UV labels legs test
  else ∫ xq, connectedJointIntegrand ward L order loop Λ UV labels legs test xq

structure ConnectedWardData (G : CompactSimpleGaugeGroup) where
  ultraviolet : Bool → ℕ → ℕ → ℝ → {arity : ℕ} →
    (Fin arity → LocalMonomial G) → (legs : List (ExternalLeg G)) →
      JointMomentumDistribution arity legs
  physical : Bool → ℕ → ℕ → {arity : ℕ} →
    (Fin arity → LocalMonomial G) → (legs : List (ExternalLeg G)) →
      JointMomentumDistribution arity legs

/-- Exact actual-flow identification in the bulk and agreement with the
previous same-engine W data in the background/single sectors. Full-diagonal
values still require the local extension and Ward prescriptions; this is
not, by itself, an admissible contact-extension theorem. -/
structure ConnectedWardData.Compatible (C : ConnectedWardData G) (W : WardContinuumData G)
    (L : ℝ → InsertedFlowFamily G) (F : ℝ → OversubtractedFamily G) : Prop where
  connected_flow : CoupledConnectedInsertionFlowConditions L F
  joint_smooth : ∀ (ward : Bool) input loop Λ UV legs, 0 < Λ → Λ ≤ UV →
    ContDiff ℝ ∞ (fun gq : ℝ × (Fin legs.length → Spacetime) =>
      connectedWardFamily ward (L gq.1) input loop Λ UV legs gq.2)
  finite_integrable : ∀ (ward : Bool) order loop Λ UV, 0 < Λ → Λ ≤ UV →
    ∀ {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs
      (test : JointMomentumTest arity legs), HasCompactSupport test →
      Integrable (connectedJointIntegrand ward L order loop Λ UV labels legs test)
  background_integrable : ∀ (ward : Bool) order loop Λ UV, 0 < Λ → Λ ≤ UV →
    ∀ legs (test : JointMomentumTest 0 legs), HasCompactSupport test →
      Integrable (finiteBackgroundIntegrand (if ward then .wardSingle else .single)
        L (fun _ _ _ _ _ _ _ _ => (0 : ℂ)) order loop Λ UV legs test)
  ultraviolet_local : ∀ (ward : Bool) order loop Λ, 0 < Λ →
    ∀ {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs,
      IsJointLocalDistribution (C.ultraviolet ward order loop Λ labels legs)
  ward_empty_external : ∀ order loop {arity : ℕ} (labels : Fin arity → LocalMonomial G),
    C.physical true order loop labels [] = 0
  physical_local : ∀ (ward : Bool) order loop {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs,
    IsJointLocalDistribution (C.physical ward order loop labels legs)
  ultraviolet_limit : ∀ (ward : Bool) order loop Λ, 0 < Λ →
    ∀ {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs
      (test : JointMomentumTest arity legs), HasCompactSupport test → OffInsertionDiagonals test →
      Tendsto (fun UV : ℝ => connectedJointPairing ward L order loop Λ UV labels legs test)
        atTop (nhds (C.ultraviolet ward order loop Λ labels legs test))
  infrared_limit : ∀ (ward : Bool) order loop {arity : ℕ} (labels : Fin arity → LocalMonomial G) legs
      (test : JointMomentumTest arity legs), HasCompactSupport test → OffInsertionDiagonals test →
      NonexceptionalSupport (if ward then .wardSingle else .single) test →
      Tendsto (fun Λ : ℝ => C.ultraviolet ward order loop Λ labels legs test)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (C.physical ward order loop labels legs test))
  ultraviolet_single_same : ∀ (ward : Bool) order loop Λ, 0 < Λ → ∀ {arity : ℕ}, arity ≤ 1 →
    ∀ (labels : Fin arity → LocalMonomial G) legs,
      C.ultraviolet ward order loop Λ labels legs =
        W.ultraviolet (if ward then .wardSingle else .single) order loop Λ labels legs
  physical_single_same : ∀ (ward : Bool) order loop {arity : ℕ}, arity ≤ 1 →
    ∀ (labels : Fin arity → LocalMonomial G) legs,
      C.physical ward order loop labels legs =
        W.physical (if ward then .wardSingle else .single) order loop labels legs

end YangMills.PerturbativeFlow
