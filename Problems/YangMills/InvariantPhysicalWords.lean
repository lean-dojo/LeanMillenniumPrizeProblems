import Problems.YangMills.QuantumOutputRecovery

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Generated invariant-state tests for the physical Ward quotient

Null-state statements must use invariant physical spectators, not arbitrary
external gauge/ghost legs. These word distributions are built from the SAME
continuum G_0 and corrected observable dictionary, with no elementary external
legs. The exact-insertion word uses the same generated Q, at the first point.
Only separated insertion supports are declared null; contact Ward terms must
be retained at coincidences. Deriving that identity from the full multiple
Ward system and identifying its physical reconstruction remain obligations.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Genuine coupling coefficient of the physical local dictionary. Smoothness
is supplied by QuantumObservableLift.Compatible before this is used. -/
def physicalLiftCouplingCoefficient (lift : QuantumObservableLift G)
    (p : InvariantInsertionLabel G) (order loop : ℕ) (m : LocalMonomial G) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => lift.physicalCoefficient g p loop m) 0

/-- Finite multilinear expansion through the very same continuum G_0.
Indices record the original position slots, so recursive expansion cannot
reorder fields or alter the contact convention. All invariant lifts are even. -/
def physicalLiftedWordExpansion {arity : ℕ} (W : WardContinuumData G)
    (lift : QuantumObservableLift G) :
    List (Fin arity × InvariantInsertionLabel G) → ℕ → ℕ →
      (Fin arity → LocalMonomial G) →
        JointMomentumDistribution arity ([] : List (ExternalLeg G))
  | [], order, loop, current => W.physical (.disconnected 0) order loop current []
  | (i, p) :: rest, order, loop, current =>
      ∑ m ∈ monomialsBelow G (intrinsicEngineeringDimension p + 1),
        ∑ a : Fin (order + 1), ∑ l : Fin (loop + 1),
          physicalLiftCouplingCoefficient lift p a.val l.val m •
            physicalLiftedWordExpansion W lift rest (order - a.val) (loop - l.val)
              (Function.update current i m)

/-- Vacuum words made entirely of the same corrected invariant insertions.
No unrelated physical correlations or independent state tests are introduced. -/
def physicalInvariantWord {arity : ℕ} (W : WardContinuumData G)
    (lift : QuantumObservableLift G) (labels : Fin arity → InvariantInsertionLabel G)
    (order loop : ℕ) : JointMomentumDistribution arity ([] : List (ExternalLeg G)) :=
  physicalLiftedWordExpansion W lift (List.ofFn fun i => (i, labels i)) order loop (fun _ => 0)

/-- A generated Q-image at the first point, with corrected invariant
spectators at all subsequent points. The finite output cutoff is fixed by
Q's engineering degree +1, not an arbitrarily supplied projection bound. -/
def physicalExactInvariantWord {n : ℕ} (W : WardContinuumData G)
    (Q : QuantumWardLimit G) (lift : QuantumObservableLift G)
    (primitive : LocalMonomial G) (spectators : Fin n → InvariantInsertionLabel G)
    (order loop : ℕ) : JointMomentumDistribution (n + 1) ([] : List (ExternalLeg G)) :=
  ∑ output ∈ monomialsBelow G (primitive.dimension + 2),
    ∑ a : Fin (order + 1), ∑ l : Fin (loop + 1),
      quantumWardCouplingCoefficient Q a.val l.val primitive output •
        physicalLiftedWordExpansion W lift
          (List.ofFn fun i : Fin n => (i.succ, spectators i)) (order - a.val) (loop - l.val)
          (Function.update (fun _ => 0) 0 output)

/-- Correct domain for a physical exact-state null identity: invariant
spectators, no gauge/ghost external legs, and no insertion coincidences.
This is a concrete generated distribution equation, not an assertion that
Q-images vanish on arbitrary gauge-fixed elementary-leg amplitudes. -/
def InvariantPhysicalNullIdentity (W : WardContinuumData G)
    (Q : QuantumWardLimit G) (lift : QuantumObservableLift G) : Prop :=
  Q.Filtered ∧ Q.CouplingSmooth ∧
  ∀ (primitive : LocalMonomial G), primitive.Admissible →
    primitive.ghostNumber = -1 → primitive.parity = true →
    ∀ n (spectators : Fin n → InvariantInsertionLabel G) order loop
      (test : JointMomentumTest (n + 1) ([] : List (ExternalLeg G))),
      HasCompactSupport test → OffInsertionDiagonals test →
      physicalExactInvariantWord W Q lift primitive spectators order loop test = 0

end YangMills.PerturbativeFlow
