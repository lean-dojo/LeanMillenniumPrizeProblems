import YangMills.InvariantJetPolynomials
import YangMills.QFT.Wightman
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Renormalized composite fields in the given Wightman theory

All operators below are finite linear combinations of actual fields of `Q`,
on its original common invariant domain. Classical labels belong to the full
invariant curvature-jet algebra. Renormalized correspondence is linear and
respects identities on smooth connections; no classical/quantum bijection,
product-preservation, or fixed renormalization scheme is imposed.

These definitions fix correspondence and finite operator mixing. They do not
by themselves identify Yang--Mills: the group-dependent perturbative/OPE
conditions must constrain this very correspondence.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace YangMills

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance (G : CompactSimpleGaugeGroup) : NormedAddCommGroup G.Algebra :=
  inferInstanceAs (NormedAddCommGroup (Fin G.dimension → ℝ))
local instance (G : CompactSimpleGaugeGroup) : NormedSpace ℝ G.Algebra :=
  inferInstanceAs (NormedSpace ℝ (Fin G.dimension → ℝ))

namespace Connection
/-- Actual pullback of a connection one-form by an affine Poincare map.
The finite matrix coefficients are those of the specified Lorentz map. -/
def poincarePullback {G : CompactSimpleGaugeGroup} (A : Connection G)
    (g : PoincareTransform) : Connection G where
  potential := fun x μ => ∑ ν : Fin 4,
    g.lorentz.linear (Pi.single μ 1) ν • A.potential (g.act x) ν
  smooth := by
    have hact : ContDiff ℝ ∞ g.act := contDiff_const.add g.lorentz.linear.contDiff
    apply contDiff_pi.mpr
    intro μ
    apply ContDiff.sum
    intro ν _
    exact contDiff_const.smul ((contDiff_apply ℝ G.Algebra ν).comp (A.smooth.comp hact))
end Connection

abbrev FiniteFieldCombination (Q : WightmanData H) := Q.FieldIndex →₀ ℂ

namespace FiniteFieldCombination

/-- A smeared composite is an operator on the original common domain. -/
def field {Q : WightmanData H} (c : FiniteFieldCombination Q) :
    TestFunction →ₗ[ℂ] Q.domain →ₗ[ℂ] Q.domain :=
  Finsupp.linearCombination ℂ Q.field c

@[simp] theorem single_field (Q : WightmanData H) (i : Q.FieldIndex) (a : ℂ) :
    field (Finsupp.single i a) = a • Q.field i := by
  simp [field]

@[simp] theorem zero_field (Q : WightmanData H) :
    field (0 : FiniteFieldCombination Q) = 0 := by
  exact map_zero _

/-- Composite expectations use the original vacuum and operator domain. -/
def vacuumOnePoint {Q : WightmanData H} (c : FiniteFieldCombination Q)
    (f : TestFunction) : ℂ :=
  inner ℂ (Q.vacuum : H) (c.field f Q.vacuum : H)

/-- Finite linear combinations remain operator-valued tempered distributions. -/
theorem continuous_field {Q : WightmanData H} (hQ : WightmanAxioms H Q)
    (c : FiniteFieldCombination Q) (v : Q.domain) :
    Continuous (fun f : TestFunction => (c.field f v : H)) := by
  classical
  have heq : (fun f : TestFunction => (c.field f v : H)) =
      (fun f => ∑ i ∈ c.support, c i • (Q.field i f v : H)) := by
    funext f
    simp [field, Finsupp.linearCombination_apply, Finsupp.sum,
      LinearMap.sum_apply, LinearMap.smul_apply]
  rw [heq]
  exact continuous_finset_sum _ (fun i _ => (hQ.field_continuous i v).const_smul (c i))

/-- Locality is inherited from the same Q fields, on their same domain. -/
theorem locality {Q : WightmanData H} (hQ : WightmanAxioms H Q)
    (c d : FiniteFieldCombination Q) (f g : TestFunction)
    (hfg : TestFunctionsSpacelike f g) (v : Q.domain) :
    c.field f (d.field g v) = d.field g (c.field f v) := by
  classical
  simp only [field, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hQ.locality j i f g hfg v, mul_comm]

end FiniteFieldCombination

/-- Renormalization scales are strictly positive real numbers. -/
abbrev RenormalizationScale := {μ : ℝ // 0 < μ}

/-- Least engineering-dimension bound modulo identities on smooth
connections. Caller-selected overestimates cannot weaken scaling conditions. -/
def intrinsicEngineeringDimension {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial.invariantAlgebra G) : ℕ := by
  classical
  exact Nat.find (CurvatureJetPolynomial.ConnectionObservable.finite_dimension
    (Quotient.mk (CurvatureJetPolynomial.connectionSetoid G) p))

/-- The intrinsic degree is exactly the minimum quotient filtration bound. -/
theorem intrinsicEngineeringDimension_le_iff {G : CompactSimpleGaugeGroup}
    (p : CurvatureJetPolynomial.invariantAlgebra G) (d : ℕ) :
    intrinsicEngineeringDimension p ≤ d ↔
      CurvatureJetPolynomial.ConnectionObservable.HasDimensionAtMost d
        (Quotient.mk (CurvatureJetPolynomial.connectionSetoid G) p) := by
  classical
  unfold intrinsicEngineeringDimension
  constructor
  · intro h
    exact CurvatureJetPolynomial.ConnectionObservable.monotone h _
      (Nat.find_spec (CurvatureJetPolynomial.ConnectionObservable.finite_dimension _))
  · intro h
    exact Nat.find_min' _ h

/-- Classical ordinary derivative relation on actual smooth connections.
The meaning of a descendant is fixed by a directional derivative, not by a
label chosen independently of the curvature-polynomial evaluation. -/
def IsClassicalDerivative {G : CompactSimpleGaugeGroup}
    (p q : CurvatureJetPolynomial.invariantAlgebra G) (μ : Fin 4) : Prop :=
  ∀ (A : Connection G) x,
    (q : CurvatureJetPolynomial G).onConnection A x =
      fderiv ℝ (fun y => (p : CurvatureJetPolynomial G).onConnection A y)
        x (Pi.single μ 1)

/-- Fixed action on observable labels, characterized on actual pulled-back
connections. For tensor components this produces the corresponding finite
Lorentz-index mixing; translations cancel between pullback and inverse point.
The quantum covariance axiom requires an actual transformed polynomial,
rather than relying on an implication with a possibly empty premise. -/
def IsClassicalPoincareTransform {G : CompactSimpleGaugeGroup}
    (g : PoincareTransform) (p q : CurvatureJetPolynomial.invariantAlgebra G) : Prop :=
  ∀ (A : Connection G) x,
    (q : CurvatureJetPolynomial G).onConnection A x =
      (p : CurvatureJetPolynomial G).onConnection (A.poincarePullback g) (g.inverseAct x)

/-- Transformed labels have unique meaning modulo actual connection
identities; choosing a polynomial witness cannot redefine the symmetry. -/
theorem classicalPoincareTransform_unique {G : CompactSimpleGaugeGroup}
    (g : PoincareTransform) (p q r : CurvatureJetPolynomial.invariantAlgebra G)
    (hq : IsClassicalPoincareTransform g p q)
    (hr : IsClassicalPoincareTransform g p r) :
    CurvatureJetPolynomial.sameOnConnections (q : CurvatureJetPolynomial G)
      (r : CurvatureJetPolynomial G) := by
  intro A x
  exact (hq A x).trans (hr A x).symm

/-- Data only: each invariant polynomial has a renormalized smeared operator
in the *same* QFT. A change of scale can mix operators. -/
structure RenormalizedCompositeMap (Q : WightmanData H) (G : CompactSimpleGaugeGroup) where
  coefficients : RenormalizationScale →
    CurvatureJetPolynomial.invariantAlgebra G →ₗ[ℝ] FiniteFieldCombination Q

namespace RenormalizedCompositeMap

variable {Q : WightmanData H} {G : CompactSimpleGaugeGroup}

/-- The actual field, as a specified finite combination of Q's components. -/
def field (C : RenormalizedCompositeMap Q G) (μ : RenormalizationScale)
    (p : CurvatureJetPolynomial.invariantAlgebra G) :
    TestFunction →ₗ[ℂ] Q.domain →ₗ[ℂ] Q.domain :=
  (C.coefficients μ p).field

/-- Words of the *identified* Yang--Mills composites acting on Q's vacuum. -/
def word (C : RenormalizedCompositeMap Q G) (μ : RenormalizationScale) :
    List (CurvatureJetPolynomial.invariantAlgebra G × TestFunction) → Q.domain
  | [] => Q.vacuum
  | (p, f) :: rest => C.field μ p f (C.word μ rest)

/-- Fixed necessary correspondence conditions. These do not assume
multiplicativity of renormalization or prohibit operator mixing. -/
structure Compatible (C : RenormalizedCompositeMap Q G) : Prop where
  /-- Classical identities are respected at the level of actual operators;
  coefficient vectors need not be equal when Q has redundant field labels. -/
  relations : ∀ μ (p q : CurvatureJetPolynomial.invariantAlgebra G),
    CurvatureJetPolynomial.sameOnConnections (p : CurvatureJetPolynomial G) (q : CurvatureJetPolynomial G) →
      C.field μ p = C.field μ q
  /-- Quantum descendants are distributional derivatives of the *same*
  renormalized fields. Translation-compatible renormalization cannot relabel
  them as independent operators. -/
  descendant : ∀ μ p q direction, IsClassicalDerivative p q direction → ∀ f v,
    C.field μ q f v =
      -C.field μ p (SchwartzMap.pderivCLM ℂ (Pi.single direction 1) f) v
  /-- The correspondence intertwines the actual classical action on
  curvature labels with the same QFT's spacetime symmetries. -/
  covariance : ∀ μ g p, ∃ q, IsClassicalPoincareTransform g p q ∧ ∀ f v,
    Q.domainAction g (C.field μ p f v) =
      C.field μ q (Q.pullback g f) (Q.domainAction g v)
  /-- The constant polynomial is the identity operator-valued distribution. -/
  unit : ∀ μ f v,
    C.field μ 1 f v = (∫ x : Spacetime, f x) • v
  /-- The identified composite fields generate the physical Hilbert space.
  A decoupled spectator theory cannot contribute unobserved lower energies. -/
  cyclic : ∀ μ, Dense ((Submodule.span ℂ
    (Set.range (fun w => (C.word μ w : H)))) : Set H)
  /-- Real invariant polynomials correspond to Hermitian composite fields. -/
  hermitian : ∀ μ p f (v w : Q.domain),
    inner ℂ (C.field μ p f v : H) (w : H) =
      inner ℂ (v : H) (C.field μ p (Q.conjugateTest f) w : H)

/-- Exact fixed meaning of a dimension-filtered finite mixing transformation.
The matrix is invertible on its finite label space, while the actual quantum
fields may obey relations; no bijection with classical polynomials follows. -/
structure FiniteMixing (C C' : RenormalizedCompositeMap Q G)
    (n : ℕ) (labels : Fin n → CurvatureJetPolynomial.invariantAlgebra G)
    (μ : RenormalizationScale) where
  matrix : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)
  /-- The i-th transformed operator cannot use a larger-degree label. -/
  filtered : ∀ i j, intrinsicEngineeringDimension (labels i) < intrinsicEngineeringDimension (labels j) → matrix (Pi.single j 1) i = 0
  /-- The matrix acts on the quantum operators, not merely on their names. -/
  operator_identity : ∀ i f v,
    C'.field μ (labels i) f v =
      ∑ j : Fin n, ((((μ.val ^ (intrinsicEngineeringDimension (labels i) - intrinsicEngineeringDimension (labels j)) : ℝ) : ℂ) *
        matrix (Pi.single j 1) i)) • C.field μ (labels j) f v

/-- Polynomial equality on smooth connections already forces equality of
all smeared composite matrix elements in a compatible correspondence. -/
theorem matrix_element_eq_of_sameOnConnections
    (C : RenormalizedCompositeMap Q G) (hC : C.Compatible)
    (μ : RenormalizationScale) (p q : CurvatureJetPolynomial.invariantAlgebra G)
    (hpq : CurvatureJetPolynomial.sameOnConnections (p : CurvatureJetPolynomial G) (q : CurvatureJetPolynomial G))
    (f : TestFunction) (v w : Q.domain) :
    inner ℂ (v : H) (C.field μ p f w : H) =
      inner ℂ (v : H) (C.field μ q f w : H) := by
  rw [hC.relations μ p q hpq]

end RenormalizedCompositeMap
end YangMills
