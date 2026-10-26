import YangMills.ActionProbeNorms
import YangMills.FormalRenormalization

/-!
# Actual local-action coordinates and the formal bare-coupling formula

The arguments of the IZ bare-coupling formula below are the coordinates
computed from the very same UV action jets, including S0. No independent
normalization series are supplied. These algebraic operations do not assert
that the raw finite-cutoff action is multiplicatively Ward closed. In
particular, `projectedBetaAtCutoff` is a diagnostic expression until an
actual admissible finite Ward transport (or the corresponding physical
scale-insertion theorem) identifies these coordinates with bare parameters.
Nonexceptional continuum Ward identities alone do not prove that statement.
-/
noncomputable section
namespace YangMills.WardAction
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- IZ g0=g Z1 Z3^(-3/2), applied to the fixed actual action projectors. -/
def projectedBareCoupling {B : InvariantForm G} (e : ColorFrame B)
    (A : ScaleCouplingFamily G) (Λ0 μ : ℝ) : Series :=
  FormalRG.bareCoupling (Z1 e A μ Λ0) (Z3 e A μ Λ0)

/-- Actual scale derivatives of those very coordinates. Merely defining
this expression does not authorize its physical interpretation as beta. -/
def projectedBetaAtCutoff {B : InvariantForm G} (e : ColorFrame B)
    (A : ScaleCouplingFamily G) (Λ0 μ : ℝ) : Series :=
  FormalRG.betaAtCutoff (projectedBareCoupling e A Λ0) μ

/-- Full physical-sector action equality forces the arguments of the bare
formula to be exactly the displayed multiplicative normalization series.
The finite-cutoff equality is a hypothesis, not a claimed Ward theorem. -/
theorem projectedBareCoupling_eq_of_decomposition {B : InvariantForm G}
    (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ)
    (z : Sector → Series)
    (h : ∀ n, PhysicalActionDecomposition e (uvActionCoefficient A μ Λ0 n)
      (fun s => if couplingOffset s ≤ n then
        PowerSeries.coeff (n - couplingOffset s) (z s) else 0)) :
    projectedBareCoupling e A Λ0 μ = FormalRG.bareCoupling
      (z .cubic) (z .gluonKinetic) := by
  unfold projectedBareCoupling Z1 Z3
  rw [normalizationSeries_eq_of_decomposition e A μ Λ0 z h .cubic,
    normalizationSeries_eq_of_decomposition e A μ Λ0 z h .gluonKinetic]

/-- The actual coupling derivative denominator is a unit with constant 1
once the full same-action decomposition has the canonical cubic tree value.
This closes a second totalized-inverse escape without postulating a beta. -/
theorem projectedBareCoupling_derivative_constant {B : InvariantForm G}
    (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ)
    (z : Sector → Series)
    (h : ∀ n, PhysicalActionDecomposition e (uvActionCoefficient A μ Λ0 n)
      (fun s => if couplingOffset s ≤ n then
        PowerSeries.coeff (n - couplingOffset s) (z s) else 0))
    (htree : PowerSeries.constantCoeff (z .cubic) = 1) :
    PowerSeries.constantCoeff
      (PowerSeries.derivative ℝ (projectedBareCoupling e A Λ0 μ)) = 1 := by
  rw [projectedBareCoupling_eq_of_decomposition e A μ Λ0 z h]
  exact FormalRG.bareCoupling_derivative_constant _ _ htree


/-- The wavefunction square-root branch is valid for the actual Z3, rather
than merely a formal constant-one recursion unrelated to its constant term. -/
theorem projectedWavefunctionRoot_square {B : InvariantForm G}
    (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ)
    (z : Sector → Series)
    (h : ∀ n, PhysicalActionDecomposition e (uvActionCoefficient A μ Λ0 n)
      (fun s => if couplingOffset s ≤ n then
        PowerSeries.coeff (n - couplingOffset s) (z s) else 0))
    (htree : PowerSeries.constantCoeff (z .gluonKinetic) = 1) :
    FormalRG.unitSqrt (Z3 e A μ Λ0) * FormalRG.unitSqrt (Z3 e A μ Λ0) =
      Z3 e A μ Λ0 := by
  apply FormalRG.unitSqrt_square
  unfold Z3
  rw [normalizationSeries_eq_of_decomposition e A μ Λ0 z h .gluonKinetic]
  exact htree

end YangMills.WardAction
