import Mathlib.Analysis.Distribution.TemperedDistribution
import Problems.YangMills.PerturbativeYangMills
import Problems.YangMills.InvariantJetPolynomials
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Monad

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed finite-cutoff kernels and subtraction operations

The exponential flow cutoff follows Fröb--Holland arXiv:1603.08012,
equations (2.13)--(2.17), in Feynman gauge. The color metric and ghost
vertices are those of the actual G and invariant form.

These definitions fix actual kernels and a Taylor subtraction, rather than
letting a candidate choose coefficients. They do not constitute an all-order
renormalized Yang--Mills coefficient system. In particular, a primitive ghost
loop is not the sum of gauge/ghost/counterterm graphs, and the subtraction
does not prove the Slavnov--Taylor identity or an ultraviolet limit.
-/
noncomputable section
open MeasureTheory Module
namespace YangMills.Perturbative

variable {G : CompactSimpleGaugeGroup}

/-- A coordinate choice for contractions, explicitly compatible with the
same invariant form used in the Yang--Mills action and its interaction vertices. -/
structure ColorFrame (B : InvariantForm G) where
  basis : Basis (Fin G.dimension) ℝ G.Algebra
  orthonormal : ∀ a b, B.bilinear (basis a) (basis b) = if a = b then 1 else 0

def structureConstant {B : InvariantForm G} (e : ColorFrame B)
    (a b c : Fin G.dimension) : ℝ := threeColor B (e.basis a) (e.basis b) (e.basis c)

/-- The contraction coordinates are those of the actual chosen basis,
not coefficients of an independent abstract color representation. -/
theorem color_coordinate {B : InvariantForm G} (e : ColorFrame B)
    (c : Fin G.dimension) (X : G.Algebra) :
    B.bilinear (e.basis c) X = e.basis.repr X c := by
  conv_lhs => rw [← e.basis.sum_repr X]
  rw [map_sum]
  simp [map_smul, e.orthonormal]

theorem bracket_coordinates {B : InvariantForm G} (e : ColorFrame B)
    (c : Fin G.dimension) (X Y : G.Algebra) :
    e.basis.repr ⁅X, Y⁆ c = ∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
      structureConstant e c a b * e.basis.repr X a * e.basis.repr Y b := by
  rw [← color_coordinate]
  conv_lhs => rw [← e.basis.sum_repr X, ← e.basis.sum_repr Y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [structureConstant, threeColor]
  ring

def adjointCasimir {B : InvariantForm G} (e : ColorFrame B) : ℝ :=
  (∑ a : Fin G.dimension, ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    (structureConstant e a b c) ^ 2) / G.dimension

/-- The first two pure-Yang--Mills beta coefficients with the given kinetic
normalization. This is only the universal two-loop truncation, not an
unconstrained replacement for the complete perturbative coefficient system. -/
def betaTwoLoop {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : ℝ :=
  -((11 / 3 : ℝ) * adjointCasimir e / (4 * Real.pi) ^ 2) * g ^ 3 -
    ((34 / 3 : ℝ) * (adjointCasimir e) ^ 2 / (4 * Real.pi) ^ 4) * g ^ 5

/-- Strictly positive finite flow scales. The endpoint p=0 of the covariance
is handled by its continuous extension; no 0/0 value is silently used. -/
structure CutoffScales where
  infrared : ℝ
  ultraviolet : ℝ
  infrared_pos : 0 < infrared
  ordered : infrared ≤ ultraviolet

def euclideanSquare (p : Spacetime) : ℝ := ∑ μ : Fin 4, (p μ) ^ 2

def exponentialRegulator (scale : ℝ) (p : Spacetime) : ℝ :=
  Real.exp (-euclideanSquare p / scale ^ 2)

def flowCovariance (s : CutoffScales) (p : Spacetime) : ℝ :=
  if euclideanSquare p = 0 then s.infrared⁻¹ ^ 2 - s.ultraviolet⁻¹ ^ 2
  else (exponentialRegulator s.ultraviolet p - exponentialRegulator s.infrared p) /
    euclideanSquare p

/-- Explicit Λ derivative kernel of the exponential covariance, including
its p=0 continuation. Establishing this derivative identity analytically is
still separate from defining its unambiguous right-hand side. -/
def flowDerivativeKernel (scale : ℝ) (p : Spacetime) : ℝ :=
  -2 / scale ^ 3 * exponentialRegulator scale p

@[simp] theorem euclideanSquare_zero : euclideanSquare 0 = 0 := by
  simp [euclideanSquare]

@[simp] theorem flowCovariance_zero (s : CutoffScales) :
    flowCovariance s 0 = s.infrared⁻¹ ^ 2 - s.ultraviolet⁻¹ ^ 2 := by
  simp [flowCovariance]

theorem euclideanSquare_nonnegative (p : Spacetime) : 0 ≤ euclideanSquare p := by
  exact Finset.sum_nonneg (fun μ _ => sq_nonneg (p μ))

inductive BasicField (G : CompactSimpleGaugeGroup) where
  | gauge (μ : Fin 4) (a : Fin G.dimension)
  | antighost (a : Fin G.dimension)
  | ghost (a : Fin G.dimension)
  | auxiliary (a : Fin G.dimension)
  deriving DecidableEq

def BasicField.dimension : BasicField G → ℕ
  | .auxiliary _ => 2
  | _ => 1

def BasicField.fermionic : BasicField G → Bool
  | .antighost _ | .ghost _ => true
  | _ => false

/-- The fixed graded covariance in the ordering (A,cbar,c,B), ξ=1.
The opposite ghost orientations have opposite signs. -/
def basicCovariance (s : CutoffScales) (K L : BasicField G) (p : Spacetime) : ℝ :=
  match K, L with
  | .gauge μ a, .gauge ν b => if a = b ∧ μ = ν then flowCovariance s p else 0
  | .antighost a, .ghost b => if a = b then -flowCovariance s p else 0
  | .ghost a, .antighost b => if a = b then flowCovariance s p else 0
  | .auxiliary a, .auxiliary b =>
      if a = b then euclideanSquare p * flowCovariance s p else 0
  | _, _ => 0

/-- Every ghost loop color factor is computed from the action's bracket.
There is no independent vertex or selected color coefficient. -/
def ghostLoopColor {B : InvariantForm G} (e : ColorFrame B)
    (a b : Fin G.dimension) : ℝ :=
  ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
    structureConstant e a c d * structureConstant e b c d

def ghostBubbleKernel {B : InvariantForm G} (e : ColorFrame B) (s : CutoffScales)
    (a b : Fin G.dimension) (μ ν : Fin 4) (p k : Spacetime) : ℝ :=
  -ghostLoopColor e a b * k μ * (k + p) ν * flowCovariance s k *
    flowCovariance s (k + p) / (2 * Real.pi) ^ 4

/-- A completely specified Taylor counterterm in the external momentum.
The n-th derivative is the standard continuous multilinear Frechet derivative.
Use only on kernels with the corresponding differentiability proved; no
claim about its order or renormalization follows from this definition alone. -/
def momentumTaylor (degree : ℕ) (base : Spacetime) (f : Spacetime → ℝ)
    (p : Spacetime) : ℝ :=
  ∑ n ∈ Finset.range (degree + 1),
    (Nat.factorial n : ℝ)⁻¹ * iteratedFDeriv ℝ n f base (fun _ => p - base)

/-- Degree-two Taylor subtraction for this fixed primitive two-point kernel.
This is the BPHZ primitive subtraction at a specified base momentum, not a
claim that independent graph subtractions already obey Yang--Mills Ward identities. -/
def subtractedGhostBubbleKernel {B : InvariantForm G} (e : ColorFrame B)
    (s : CutoffScales) (base : Spacetime) (a b : Fin G.dimension) (μ ν : Fin 4)
    (p k : Spacetime) : ℝ :=
  ghostBubbleKernel e s a b μ ν p k -
    momentumTaylor 2 base (fun q => ghostBubbleKernel e s a b μ ν q k) p

/-- Integration of the fixed subtracted kernel requires its actual
integrability. Lean's totalized integral cannot discharge that obligation. -/
def subtractedGhostBubbleAmplitude {B : InvariantForm G} (e : ColorFrame B)
    (s : CutoffScales) (base : Spacetime) (a b : Fin G.dimension) (μ ν : Fin 4)
    (p : Spacetime)
    (_finite : Integrable (fun k => subtractedGhostBubbleKernel e s base a b μ ν p k)) : ℝ :=
  ∫ k : Spacetime, subtractedGhostBubbleKernel e s base a b μ ν p k

/-- A field insertion with an explicitly ordered list of derivatives. -/
structure DifferentialLeg (G : CompactSimpleGaugeGroup) where
  field : BasicField G
  derivatives : List (Fin 4)

structure PositionedLeg (G : CompactSimpleGaugeGroup) extends DifferentialLeg G where
  position : Spacetime

def euclideanPair (p x : Spacetime) : ℝ := ∑ μ : Fin 4, p μ * x μ

/-- The fixed Fourier integrand for derivatives at both ends of a propagator. -/
def contractionIntegrand (s : CutoffScales) (a b : PositionedLeg G) (p : Spacetime) : ℂ :=
  (Complex.I ^ a.derivatives.length) * ((-Complex.I) ^ b.derivatives.length) *
    ((a.derivatives.map (fun μ => (p μ : ℂ))).prod) *
    ((b.derivatives.map (fun μ => (p μ : ℂ))).prod) *
    Complex.exp (Complex.I * (euclideanPair p (a.position - b.position) : ℂ)) *
    (basicCovariance s a.field b.field p : ℂ) / (2 * Real.pi : ℂ) ^ 4

def contraction (s : CutoffScales) (a b : PositionedLeg G) : ℂ :=
  ∫ p : Spacetime, contractionIntegrand s a b p

/-- Moving the first odd leg past the intermediate odd legs gives this
Koszul sign. Even fields commute with both species. -/
def wickCrossingSign (a : PositionedLeg G) (between : List (PositionedLeg G)) : ℂ :=
  if a.field.fermionic then
    (-1 : ℂ) ^ (between.filter (fun b => b.field.fermionic)).length else 1

/-- Deterministic graded Wick expansion: sum over the possible partner of
the first leg, remove that pair, and recurse. Ghost signs are fixed by the
ordered field list and the fixed oriented ghost covariance. -/
def wickKernel (s : CutoffScales) : List (PositionedLeg G) → ℂ
  | [] => 1
  | a :: rest => ∑ j : Fin rest.length,
      wickCrossingSign a (rest.take j.val) * contraction s a (rest.get j) *
        wickKernel s (rest.take j.val ++ rest.drop (j.val + 1))
termination_by legs => legs.length
decreasing_by
  have hj := j.isLt
  simp only [List.length_append, List.length_take, List.length_drop, List.length_cons]
  omega

@[simp] theorem wickKernel_nil (s : CutoffScales) : wickKernel (G := G) s [] = 1 := by
  simp [wickKernel]

@[simp] theorem wickKernel_singleton (s : CutoffScales) (a : PositionedLeg G) :
    wickKernel s [a] = 0 := by
  simp [wickKernel]

theorem wickKernel_pair (s : CutoffScales) (a b : PositionedLeg G) :
    wickKernel s [a, b] = contraction s a b := by
  simp [wickKernel, wickCrossingSign]

/-- A local monomial derived by expansion of the fixed interaction action.
Its coefficient is a real color contraction; derivative ordering and ghost
ordering are retained for Wick contraction. -/
structure InteractionMonomial (G : CompactSimpleGaugeGroup) where
  coefficient : ℝ
  couplingOrder : ℕ
  legs : List (DifferentialLeg G)

def cubicMonomials {B : InvariantForm G} (e : ColorFrame B) :
    List (InteractionMonomial G) := do
  let μ ← List.finRange 4
  let ν ← List.finRange 4
  let a ← List.finRange G.dimension
  let b ← List.finRange G.dimension
  let c ← List.finRange G.dimension
  [ { coefficient := (1 / 2 : ℝ) * structureConstant e a b c,
      couplingOrder := 1,
      legs := [⟨.gauge ν a, [μ]⟩, ⟨.gauge μ b, []⟩, ⟨.gauge ν c, []⟩] },
    { coefficient := -(1 / 2 : ℝ) * structureConstant e a b c,
      couplingOrder := 1,
      legs := [⟨.gauge μ a, [ν]⟩, ⟨.gauge μ b, []⟩, ⟨.gauge ν c, []⟩] } ]

def quarticMonomials {B : InvariantForm G} (e : ColorFrame B) :
    List (InteractionMonomial G) := do
  let μ ← List.finRange 4
  let ν ← List.finRange 4
  let a ← List.finRange G.dimension
  let b ← List.finRange G.dimension
  let c ← List.finRange G.dimension
  let d ← List.finRange G.dimension
  [ { coefficient := (1 / 4 : ℝ) *
        fourColor B (e.basis a) (e.basis b) (e.basis c) (e.basis d),
      couplingOrder := 2,
      legs := [⟨.gauge μ a, []⟩, ⟨.gauge ν b, []⟩,
        ⟨.gauge μ c, []⟩, ⟨.gauge ν d, []⟩] } ]

def ghostMonomials {B : InvariantForm G} (e : ColorFrame B) :
    List (InteractionMonomial G) := do
  let μ ← List.finRange 4
  let a ← List.finRange G.dimension
  let b ← List.finRange G.dimension
  let c ← List.finRange G.dimension
  [ { coefficient := structureConstant e a b c,
      couplingOrder := 1,
      legs := [⟨.antighost a, [μ]⟩, ⟨.gauge μ b, []⟩, ⟨.ghost c, []⟩] } ]

def actionMonomials {B : InvariantForm G} (e : ColorFrame B) : List (InteractionMonomial G) :=
  cubicMonomials e ++ quarticMonomials e ++ ghostMonomials e

def atPosition (x : Spacetime) (a : DifferentialLeg G) : PositionedLeg G := ⟨a, x⟩

/-- A coupling polynomial of all action monomial choices and all graded
contractions at these vertices. All vacuum/disconnected contractions are
retained here; the vacuum quotient below performs the normalization. -/
def interactionKernel {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B) :
    List Spacetime → List (PositionedLeg G) → Polynomial ℂ
  | [], external => Polynomial.C (wickKernel s external)
  | x :: xs, external =>
      ((actionMonomials e).map (fun m =>
        Polynomial.C (m.coefficient : ℂ) * Polynomial.X ^ m.couplingOrder *
          interactionKernel s e xs (external ++ m.legs.map (atPosition x)))).sum

def bareCoefficientIntegrand {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B)
    (switching : SchwartzMap Spacetime ℝ) (external : List (PositionedLeg G))
    (order n : ℕ) (xs : Fin n → Spacetime) : ℂ :=
  (∏ i : Fin n, (switching (xs i) : ℂ)) *
    (interactionKernel s e (List.ofFn xs) external).coeff order

/-- Unnormalized, fixed finite-cutoff expansion coefficient of exp(-gV3-g²V4).
At order r only n≤r vertices contribute because each vertex carries a positive
coupling power. Analytic legitimacy is a separate, concrete obligation below. -/
def bareUnnormalizedCoefficient {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B)
    (switching : SchwartzMap Spacetime ℝ) (external : List (PositionedLeg G))
    (order : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (order + 1), ((-1 : ℂ) ^ n / Nat.factorial n) *
    ∫ xs : Fin n → Spacetime, bareCoefficientIntegrand s e switching external order n xs

theorem bareUnnormalizedCoefficient_zero {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (external : List (PositionedLeg G)) :
    bareUnnormalizedCoefficient s e switching external 0 = wickKernel s external := by
  have hv : volume (Set.univ : Set (Fin 0 → Spacetime)) = 1 := by
    simpa using (volume_pi_pi (fun _ : Fin 0 => (Set.univ : Set Spacetime)))
  simp [bareUnnormalizedCoefficient, bareCoefficientIntegrand, interactionKernel,
    Measure.real, hv]

/-- Every integral used in the finite-cutoff coefficient construction has
to exist. No totalized zero integral can qualify as a coefficient prescription. -/
structure BareCoefficientIntegrability {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ) : Prop where
  propagators : ∀ a b : PositionedLeg G, Integrable (contractionIntegrand s a b)
  coefficients : ∀ external order n,
    Integrable (bareCoefficientIntegrand s e switching external order n)

/-- Formal division by the vacuum series, coefficient by coefficient.
The recursion is triangular and no free coefficient data are supplied. -/
def bareNormalizedCoefficient {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B)
    (switching : SchwartzMap Spacetime ℝ) (external : List (PositionedLeg G))
    (order : ℕ) : ℂ :=
  bareUnnormalizedCoefficient s e switching external order -
    ∑ j : Fin order,
      bareUnnormalizedCoefficient s e switching [] (order - j.val) *
        bareNormalizedCoefficient s e switching external j.val
termination_by order

theorem bareNormalizedCoefficient_zero {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (external : List (PositionedLeg G)) :
    bareNormalizedCoefficient s e switching external 0 = wickKernel s external := by
  rw [bareNormalizedCoefficient]
  simp [bareUnnormalizedCoefficient_zero]

/-- The recursion is exactly formal vacuum-series division, not merely
an arbitrary modification of the unnormalized coefficients. -/
theorem bare_normalization_identity {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (external : List (PositionedLeg G)) (order : ℕ) :
    bareNormalizedCoefficient s e switching external order +
      (∑ j : Fin order, bareUnnormalizedCoefficient s e switching [] (order - j.val) *
        bareNormalizedCoefficient s e switching external j.val) =
      bareUnnormalizedCoefficient s e switching external order := by
  rw [bareNormalizedCoefficient]
  exact sub_add_cancel _ _

theorem bareNormalizedCoefficient_vacuum {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ) (order : ℕ) :
    bareNormalizedCoefficient s e switching [] order = if order = 0 then 1 else 0 := by
  induction order using Nat.strong_induction_on with
  | h order ih =>
    by_cases hz : order = 0
    · subst order
      simp [bareNormalizedCoefficient_zero]
    · have hp : 0 < order := Nat.pos_of_ne_zero hz
      have hsum : (∑ j : Fin order,
          bareUnnormalizedCoefficient s e switching [] (order - j.val) *
            bareNormalizedCoefficient s e switching [] j.val) =
          bareUnnormalizedCoefficient s e switching [] order := by
        rw [Finset.sum_eq_single (⟨0, hp⟩ : Fin order)]
        · simp [bareNormalizedCoefficient_zero]
        · intro j _ hne
          have hj : j.val ≠ 0 := by
            intro heq
            apply hne
            exact Fin.ext heq
          rw [ih j.val j.isLt, if_neg hj, mul_zero]
        · simp
      rw [bareNormalizedCoefficient, hsum, sub_self, if_neg hz]

/-- Public coefficient construction requires the analytic side conditions.
It is still a bare finite-cutoff coefficient, not a renormalized UV limit. -/
def bareCoefficient {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B)
    (switching : SchwartzMap Spacetime ℝ) (_finite : BareCoefficientIntegrability s e switching)
    (external : List (PositionedLeg G)) (order : ℕ) : ℂ :=
  bareNormalizedCoefficient s e switching external order

/-- Fixed differential operator on Schwartz tests, with actual continuous
linearity rather than an arbitrary operation called a distribution derivative. -/
def orderedTestDerivative : List (Fin 4) → TestFunction →L[ℂ] TestFunction
  | [] => ContinuousLinearMap.id ℂ TestFunction
  | μ :: rest => (LineDeriv.lineDerivOpCLM (V := Spacetime) ℂ TestFunction (Pi.single μ 1)).comp (orderedTestDerivative rest)

/-- A derivative of delta at the origin, including the distributional sign. -/
def contactDerivative (directions : List (Fin 4)) : TestFunction →L[ℂ] ℂ :=
  ((-1 : ℂ) ^ directions.length) •
    ((TemperedDistribution.delta (0 : Spacetime)).comp (orderedTestDerivative directions))

@[simp] theorem contactDerivative_nil :
    contactDerivative [] = TemperedDistribution.delta (0 : Spacetime) := by
  simp [contactDerivative, orderedTestDerivative]

/-- Finite, explicitly local renormalization ambiguity of bounded derivative
order. Coefficients are scheme data only; they cannot select arbitrary nonlocal
correlators. Ward identities and action/composite normalization still have to
constrain their allowed occurrence in a complete renormalization prescription. -/
structure LocalCounterterm (degree : ℕ) where
  coefficient : List (Fin 4) →₀ ℂ
  order_bound : ∀ directions ∈ coefficient.support, directions.length ≤ degree

def LocalCounterterm.distribution {degree : ℕ} (c : LocalCounterterm degree) :
    TestFunction →L[ℂ] ℂ :=
  c.coefficient.sum (fun directions a => a • contactDerivative directions)

theorem LocalCounterterm.distribution_apply {degree : ℕ} (c : LocalCounterterm degree)
    (f : TestFunction) :
    c.distribution f = c.coefficient.sum (fun directions a => a * contactDerivative directions f) := by
  classical
  simp [LocalCounterterm.distribution, Finsupp.sum]

/-- Commuting partial-derivative multiindices for canonical gauge potentials.
The distinguished left variable is the coupling g, which has zero derivative. -/
abbrev PotentialVariable (G : CompactSimpleGaugeGroup) :=
  Unit ⊕ ((Fin 4 → ℕ) × Fin 4 × Fin G.dimension)
abbrev PotentialPolynomial (G : CompactSimpleGaugeGroup) := MvPolynomial (PotentialVariable G) ℝ

def couplingPolynomial : PotentialPolynomial G := MvPolynomial.X (.inl ())

def potentialPolynomial (μ : Fin 4) (a : Fin G.dimension) : PotentialPolynomial G :=
  MvPolynomial.X (.inr (0, μ, a))

/-- The total derivative is the unique algebraic derivation with the fixed
action on potential jets. Partial-derivative multiindices commute by construction. -/
def totalDerivative (μ : Fin 4) :
    Derivation ℝ (PotentialPolynomial G) (PotentialPolynomial G) :=
  MvPolynomial.mkDerivation ℝ (fun v => match v with
    | .inl _ => 0
    | .inr (d, ν, a) => MvPolynomial.X (.inr (d + Pi.single μ 1, ν, a)))

@[simp] theorem totalDerivative_coupling (μ : Fin 4) :
    totalDerivative (G := G) μ couplingPolynomial = 0 := by
  simp [totalDerivative, couplingPolynomial]

@[simp] theorem totalDerivative_potential (μ ν : Fin 4) (a : Fin G.dimension) :
    totalDerivative μ (potentialPolynomial (G := G) ν a) =
      MvPolynomial.X (.inr (Pi.single μ 1, ν, a)) := by
  simp [totalDerivative, potentialPolynomial]

def polynomialBracket {B : InvariantForm G} (e : ColorFrame B)
    (P Q : Fin G.dimension → PotentialPolynomial G) (c : Fin G.dimension) :
    PotentialPolynomial G :=
  ∑ a : Fin G.dimension, ∑ b : Fin G.dimension,
    MvPolynomial.C (structureConstant e c a b) * P a * Q b

/-- Fcanonical=dA+g[A,A] in the same orthonormal color frame as the Wick vertices. -/
def canonicalCurvaturePolynomial {B : InvariantForm G} (e : ColorFrame B)
    (μ ν : Fin 4) (c : Fin G.dimension) : PotentialPolynomial G :=
  totalDerivative μ (potentialPolynomial ν c) - totalDerivative ν (potentialPolynomial μ c) +
    couplingPolynomial * polynomialBracket e (potentialPolynomial μ) (potentialPolynomial ν) c

/-- Source normalization A_source=g A_canonical, hence F_source=g F_canonical.
This extra g is retained in observable insertions rather than silently changing
the source's curvature normalization. -/
def sourceCurvaturePolynomial {B : InvariantForm G} (e : ColorFrame B)
    (μ ν : Fin 4) (c : Fin G.dimension) : PotentialPolynomial G :=
  couplingPolynomial * canonicalCurvaturePolynomial e μ ν c

/-- D_source=∂+g[A_canonical,·], including every derivative descendant. -/
def polynomialCovariantDerivative {B : InvariantForm G} (e : ColorFrame B)
    (μ : Fin 4) (P : Fin G.dimension → PotentialPolynomial G)
    (c : Fin G.dimension) : PotentialPolynomial G :=
  totalDerivative μ (P c) + couplingPolynomial * polynomialBracket e (potentialPolynomial μ) P c

def curvatureJetPolynomial {B : InvariantForm G} (e : ColorFrame B)
    (j : CurvatureJet) : Fin G.dimension → PotentialPolynomial G :=
  j.derivatives.foldr (fun μ P => polynomialCovariantDerivative e μ P)
    (sourceCurvaturePolynomial e j.mu j.nu)

/-- Convert the frame components to the fixed tangent-model coordinates used
by the invariant classical polynomial algebra. The frame is never substituted
for the actual gauge Lie algebra. -/
def classicalJetCoordinatePolynomial {B : InvariantForm G} (e : ColorFrame B)
    (j : CurvatureJetCoordinate G) : PotentialPolynomial G :=
  ∑ c : Fin G.dimension,
    MvPolynomial.C (e.basis c j.2) * curvatureJetPolynomial e j.1 c

/-- A fixed, G-dependent algebraic insertion map from *all* classical
curvature-jet polynomials. Its coefficients cannot be chosen independently
of the gauge bracket, the classical observable, or the YM action vertices.
Descent through the quotient by differential identities and correspondence
to renormalized physical Wightman fields remain distinct obligations. -/
def classicalInsertionPolynomial {B : InvariantForm G} (e : ColorFrame B) :
    CurvatureJetPolynomial G →ₐ[ℝ] PotentialPolynomial G :=
  MvPolynomial.bind₁ (classicalJetCoordinatePolynomial e)

@[simp] theorem classicalInsertionPolynomial_variable {B : InvariantForm G} (e : ColorFrame B)
    (j : CurvatureJetCoordinate G) :
    classicalInsertionPolynomial e (MvPolynomial.X j) = classicalJetCoordinatePolynomial e j := by
  simp [classicalInsertionPolynomial]

@[simp] theorem classicalInsertionPolynomial_constant {B : InvariantForm G} (e : ColorFrame B)
    (r : ℝ) :
    classicalInsertionPolynomial e (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [classicalInsertionPolynomial]

/-- A fixed ordering of commuting partial derivatives for a multiindex. -/
def orderedMultiindex (d : Fin 4 → ℕ) : List (Fin 4) :=
  (List.finRange 4).flatMap (fun μ => List.replicate (d μ) μ)

def potentialMonomialLegs (m : PotentialVariable G →₀ ℕ) : List (DifferentialLeg G) :=
  m.support.toList.flatMap (fun v => match v with
    | .inl _ => []
    | .inr (d, μ, a) => List.replicate (m v) ⟨.gauge μ a, orderedMultiindex d⟩)

/-- Fixed monomial extraction for a classical gauge-invariant observable.
All legs are bosonic. Independence of the support enumeration follows from
bosonic Wick permutation symmetry; that presentation-equivalence proof is
not asserted here. -/
def observableMonomials {B : InvariantForm G} (e : ColorFrame B)
    (p : CurvatureJetPolynomial G) : List (InteractionMonomial G) :=
  let P := classicalInsertionPolynomial e p
  P.support.toList.map (fun m =>
    { coefficient := P.coeff m,
      couplingOrder := m (.inl ()),
      legs := potentialMonomialLegs m })

/-- All local composite insertions use the fixed classical polynomial map,
the same group/color form, and the same Wick covariance and action vertices. -/
def compositeKernel {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B) :
    List (CurvatureJetPolynomial G × Spacetime) → List Spacetime →
      List (PositionedLeg G) → Polynomial ℂ
  | [], vertices, external => interactionKernel s e vertices external
  | (p, x) :: rest, vertices, external =>
      ((observableMonomials e p).map (fun m =>
        Polynomial.C (m.coefficient : ℂ) * Polynomial.X ^ m.couplingOrder *
          compositeKernel s e rest vertices (external ++ m.legs.map (atPosition x)))).sum

def bareCompositeIntegrand {B : InvariantForm G} (s : CutoffScales) (e : ColorFrame B)
    (switching : SchwartzMap Spacetime ℝ)
    (insertions : List (CurvatureJetPolynomial G × Spacetime))
    (external : List (PositionedLeg G)) (order n : ℕ) (xs : Fin n → Spacetime) : ℂ :=
  (∏ i : Fin n, (switching (xs i) : ℂ)) *
    (compositeKernel s e insertions (List.ofFn xs) external).coeff order

def bareCompositeUnnormalizedCoefficient {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (insertions : List (CurvatureJetPolynomial G × Spacetime))
    (external : List (PositionedLeg G)) (order : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (order + 1), ((-1 : ℂ) ^ n / Nat.factorial n) *
    ∫ xs : Fin n → Spacetime, bareCompositeIntegrand s e switching insertions external order n xs

def bareCompositeNormalizedCoefficient {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (insertions : List (CurvatureJetPolynomial G × Spacetime))
    (external : List (PositionedLeg G)) (order : ℕ) : ℂ :=
  bareCompositeUnnormalizedCoefficient s e switching insertions external order -
    ∑ j : Fin order, bareUnnormalizedCoefficient s e switching [] (order - j.val) *
      bareCompositeNormalizedCoefficient s e switching insertions external j.val
termination_by order

structure BareCompositeIntegrability {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ) : Prop where
  bare : BareCoefficientIntegrability s e switching
  composites : ∀ insertions external order n,
    Integrable (bareCompositeIntegrand s e switching insertions external order n)

/-- These all-order finite-cutoff composite coefficients are a fixed output
of G and the classical labels, not coefficient data chosen by an existence
proof. Counterterm limits, mixing and quantum BRST identities are still needed
before they may be interpreted as renormalized ultraviolet/OPE predictions. -/
def bareCompositeCoefficient {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (_finite : BareCompositeIntegrability s e switching)
    (insertions : List (CurvatureJetPolynomial G × Spacetime))
    (external : List (PositionedLeg G)) (order : ℕ) : ℂ :=
  bareCompositeNormalizedCoefficient s e switching insertions external order

end YangMills.Perturbative
