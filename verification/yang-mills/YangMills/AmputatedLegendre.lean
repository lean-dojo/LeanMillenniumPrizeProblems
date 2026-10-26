import YangMills.FieldParameterTransport
import YangMills.RegulatedBVFlow

/-!
# Graded amputated Legendre transform of the actual connected flow

FHH 1511.09425 (71)--(74): after its fixed free-antifield source shift,
W(J)=<J,CJ>/2-L(CJ). Therefore Phi=phi-C dL and
Gamma_int(Phi)=L(phi)-<d_R L,C d_L L>/2.
All Fourier contractions and ordered partitions below are fixed operations
on the actual flow coefficients. Gamma is recursively determined in coupling
order, not supplied as a candidate family. Equivalence to the functional
Legendre transform still needs the stated algebraic/regularity proofs.
-/
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.Legendre
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

abbrev FormalAmplitude (G : CompactSimpleGaugeGroup) := ℕ → ℕ → OrderedAmplitude G

/-- Coupling jets of the same finite CAC calculation, before any limits. -/
def flowJet (A : ℝ → FlowFamily G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop legs q => (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => A g loop s.infrared s.ultraviolet legs q) 0

/-- Coefficient of the identity map on fields AND antifield spectators. -/
def identityRoot (root : ExternalLeg G) (legs : List (ExternalLeg G)) : ℂ :=
  if legs = [root] then 1 else 0

/-- Phi=phi-C d_L L. Antifields are unchanged spectators. The actual fixed
covariance includes antisymmetric ghost entries and shifted auxiliary B. -/
def meanFieldRoot (F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (root : ExternalLeg G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : ℂ :=
  (if order = 0 ∧ loop = 0 then identityRoot root legs else 0) -
    match root with
    | .inr _ => 0
    | .inl M => ∑ N : BasicField G,
        (basicCovariance s M N (∑ i, q i) : ℂ) *
          F order loop (.inl N :: legs)
            (prependMomenta (.inl N) (-(∑ i, q i)) q)

/-- The fixed quadratic subtraction <d_R L,C d_L L>/2. Right/left
conversion is made before external differentiation, with its intrinsic
functional parity (the background action is even). -/
def gradientQuadratic (F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) : OrderedAmplitude G :=
  fun legs q => (1 / 2 : ℂ) *
    ∑ a : Fin (order + 1), ∑ l : Fin (loop + 1),
    ∑ subset ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
      splitSign legs subset * ∑ M : BasicField G, ∑ N : BasicField G,
        rightDerivativeSign false (.inl M) *
        F a.val l.val (.inl M :: selectedLegs legs subset)
          (prependMomenta (.inl M) (-selectedMomentum legs subset q)
            (selectedMomenta legs subset q)) *
        (basicCovariance s M N (selectedMomentum legs subset q) : ℂ) *
        F (order - a.val) (loop - l.val)
          (.inl N :: selectedLegs legs (complementIndices legs subset))
          (prependMomenta (.inl N) (selectedMomentum legs subset q)
            (selectedMomenta legs (complementIndices legs subset) q))

def legendreTarget (F : FormalAmplitude G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop => F order loop - gradientQuadratic F s order loop

/-- Labelled nonempty blocks retain the original order inside each block.
All k! block labellings are used; the global 1/k! compensates for them. -/
def partitionBlock {n k : ℕ} (assignment : Fin n → Fin k) (block : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun i => assignment i = block

def partitionSign (legs : List (ExternalLeg G)) {k : ℕ}
    (assignment : Fin legs.length → Fin k) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin legs.length, ∑ j : Fin legs.length,
    if i < j ∧ assignment j < assignment i ∧
      (legs.get i).parity = true ∧ (legs.get j).parity = true then 1 else 0)

def rootLegs {k : ℕ} (roots : Fin k → ExternalLeg G) : List (ExternalLeg G) := List.ofFn roots

def rootMomenta (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    {k : ℕ} (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) :
    Fin (rootLegs roots).length → Spacetime :=
  fun i => selectedMomentum legs (partitionBlock assignment
    ⟨i.val, by simpa [rootLegs] using i.isLt⟩) q

/-- Explicit ordered graded Faà di Bruno summand. Coupling and loop counts
are independent finite Cauchy assignments to the outer vertex and its roots. -/
def substitutionSummand (outer : FormalAmplitude G) (F : FormalAmplitude G)
    (s : CutoffScales) (order loop : ℕ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (k : ℕ)
    (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (gOrders : Fin (k + 1) → Fin (order + 1))
    (hOrders : Fin (k + 1) → Fin (loop + 1)) : ℂ :=
  if (∀ b, (partitionBlock assignment b).Nonempty) ∧
      (∑ b, (gOrders b).val) = order ∧ (∑ b, (hOrders b).val) = loop then
    (Nat.factorial k : ℂ)⁻¹ * partitionSign legs assignment *
      outer (gOrders 0).val (hOrders 0).val (rootLegs roots)
        (rootMomenta legs q assignment roots) *
      ∏ b : Fin k, meanFieldRoot F s (gOrders b.succ).val (hOrders b.succ).val
        (roots b) (selectedLegs legs (partitionBlock assignment b))
        (selectedMomenta legs (partitionBlock assignment b) q)
  else 0

/-- Full finite formal composition with the mean-field map, when its
constant field term vanishes. No arbitrary substitution operator is used. -/
def meanFieldCompose (outer F : FormalAmplitude G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop legs q => ∑ k : Fin (legs.length + 1),
    ∑ assignment : Fin legs.length → Fin k.val,
    ∑ roots : Fin k.val → ExternalLeg G,
    ∑ gOrders : Fin (k.val + 1) → Fin (order + 1),
    ∑ hOrders : Fin (k.val + 1) → Fin (loop + 1),
      substitutionSummand outer F s order loop legs q k.val assignment roots gOrders hOrders

/-- Deterministic coupling-adic Legendre inversion. At g=0 the mean-field
map must be identity; then the omitted outer-order=order term is exactly the
unknown coefficient itself, and all other terms have lower coupling order. -/
def gammaCoeff (F : FormalAmplitude G) (s : CutoffScales) : FormalAmplitude G :=
  fun order loop legs q => legendreTarget F s order loop legs q -
    ∑ k : Fin (legs.length + 1), ∑ assignment : Fin legs.length → Fin k.val,
    ∑ roots : Fin k.val → ExternalLeg G,
    ∑ gOrders : Fin (k.val + 1) → Fin (order + 1),
    ∑ hOrders : Fin (k.val + 1) → Fin (loop + 1),
      if _h : (gOrders 0).val < order then
        substitutionSummand
          (fun r l ls ps => if _hr : r < order then gammaCoeff F s r l ls ps else 0)
          F s order loop legs q k.val assignment roots gOrders hOrders
      else 0
termination_by order => order

def actualGamma (A : ℝ → FlowFamily G) (s : CutoffScales) : FormalAmplitude G :=
  gammaCoeff (flowJet A s) s

/-- Concrete source-fidelity checks on the computed transform. They do not
assert existence of a nonperturbative Legendre transform or resum a series. -/
def AmputatedLegendreEquations (F : FormalAmplitude G) (s : CutoffScales) : Prop :=
  (∀ order loop root, meanFieldRoot F s order loop root [] (fun i => Fin.elim0 i) = 0) ∧
  (∀ loop legs q, F 0 loop legs q = 0) ∧
  ∀ order loop legs q, BalancedMomenta legs q →
    meanFieldCompose (gammaCoeff F s) F s order loop legs q =
      legendreTarget F s order loop legs q

end YangMills.Legendre
