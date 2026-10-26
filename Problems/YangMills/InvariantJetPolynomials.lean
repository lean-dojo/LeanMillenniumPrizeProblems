import Problems.YangMills.LocalObservables
import Mathlib.Algebra.MvPolynomial.Eval

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Group-specific invariant polynomials in curvature jets

This classical algebra includes arbitrary invariant tensors, rather than only
quadratic trace pairs. Invariance uses the derivative of conjugation by the
actual group. It does not identify quantum fields or prove the transformation
law of connection jets.
-/
noncomputable section
open scoped Manifold ContDiff
namespace YangMills

namespace CompactSimpleGaugeGroup
/-- The adjoint map is fixed by differentiation of actual group conjugation. -/
def adjoint (G : CompactSimpleGaugeGroup) (g : G.Carrier) :
    G.Algebra →L[ℝ] G.Algebra :=
  mfderiv (𝓘(ℝ, Fin G.dimension → ℝ)) (𝓘(ℝ, Fin G.dimension → ℝ))
    (fun h : G.Carrier => g * h * g⁻¹) (1 : G.Carrier)

@[simp] theorem adjoint_one (G : CompactSimpleGaugeGroup) :
    G.adjoint 1 = ContinuousLinearMap.id ℝ G.Algebra := by
  unfold adjoint
  have heq : (fun h : G.Carrier => 1 * h * 1⁻¹) = id := by
    funext h
    simp
  rw [heq]
  exact mfderiv_id

theorem adjoint_mul (G : CompactSimpleGaugeGroup) (g h : G.Carrier) :
    G.adjoint (g * h) = (G.adjoint g).comp (G.adjoint h) := by
  let I := 𝓘(ℝ, Fin G.dimension → ℝ)
  have hdiff (a : G.Carrier) : MDifferentiable I I
      (fun x : G.Carrier => a * x * a⁻¹) := by
    have hc : ContMDiff I I ∞ (fun x : G.Carrier => a * x * a⁻¹) :=
      contMDiff_mul_left.mul contMDiff_const
    exact hc.mdifferentiable (by norm_num)
  have heq : (fun x : G.Carrier => (g * h) * x * (g * h)⁻¹) =
      (fun x : G.Carrier => g * x * g⁻¹) ∘
        (fun x : G.Carrier => h * x * h⁻¹) := by
    funext x
    simp [mul_assoc]
  unfold adjoint
  rw [heq, mfderiv_comp _ (hdiff g _) (hdiff h _)]
  have hh : h * 1 * h⁻¹ = 1 := by group
  rw [hh]
end CompactSimpleGaugeGroup

/-- Every ordered curvature jet has the coordinates of the actual Lie algebra. -/
abbrev CurvatureJetCoordinate (G : CompactSimpleGaugeGroup) :=
  CurvatureJet × Fin G.dimension
abbrev CurvatureJetAssignment (G : CompactSimpleGaugeGroup) :=
  CurvatureJet → G.Algebra
abbrev CurvatureJetPolynomial (G : CompactSimpleGaugeGroup) :=
  MvPolynomial (CurvatureJetCoordinate G) ℝ

namespace CurvatureJetPolynomial
variable {G : CompactSimpleGaugeGroup}

def evaluate (p : CurvatureJetPolynomial G) (j : CurvatureJetAssignment G) : ℝ :=
  MvPolynomial.eval (fun c => j c.1 c.2) p

def transform (g : G.Carrier) (j : CurvatureJetAssignment G) : CurvatureJetAssignment G :=
  fun k => G.adjoint g (j k)

@[simp] theorem transform_one (j : CurvatureJetAssignment G) : transform 1 j = j := by
  funext k
  simp [transform]

theorem transform_mul (g h : G.Carrier) (j : CurvatureJetAssignment G) :
    transform (g * h) j = transform g (transform h j) := by
  funext k
  simp [transform, CompactSimpleGaugeGroup.adjoint_mul]

/-- Fixed condition on coefficients, tested on every Lie-algebra jet assignment. -/
def IsInvariant (p : CurvatureJetPolynomial G) : Prop :=
  ∀ g j, p.evaluate (transform g j) = p.evaluate j

/-- The fixed ring of invariant jet polynomials. Every polynomial has finite
support; no finite generating set or degree-two tensor restriction is imposed. -/
def invariantAlgebra (G : CompactSimpleGaugeGroup) : Subalgebra ℝ (CurvatureJetPolynomial G) where
  carrier := {p | p.IsInvariant}
  zero_mem' := by simp [IsInvariant, evaluate]
  one_mem' := by simp [IsInvariant, evaluate]
  add_mem' := by
    intro p q hp hq g j
    simp only [evaluate, map_add]
    exact congrArg₂ (· + ·) (hp g j) (hq g j)
  mul_mem' := by
    intro p q hp hq g j
    simp only [evaluate, map_mul]
    exact congrArg₂ (· * ·) (hp g j) (hq g j)
  algebraMap_mem' := by
    intro r g j
    simp [evaluate]

/-- Engineering weight: [F]=2 and [D]=1, counted with monomial multiplicity. -/
def monomialDimension (m : CurvatureJetCoordinate G →₀ ℕ) : ℕ :=
  m.sum (fun c n => n * c.1.dimension)

/-- Dimension bound on all nonzero monomials, after algebraic cancellation. -/
def HasDimensionAtMost (d : ℕ) (p : CurvatureJetPolynomial G) : Prop :=
  ∀ m ∈ p.support, monomialDimension m ≤ d

theorem dimension_add {d : ℕ} {p q : CurvatureJetPolynomial G}
    (hp : HasDimensionAtMost d p) (hq : HasDimensionAtMost d q) :
    HasDimensionAtMost d (p + q) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h
  · exact hq m h

theorem monomialDimension_add (m n : CurvatureJetCoordinate G →₀ ℕ) :
    monomialDimension (m + n) = monomialDimension m + monomialDimension n := by
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => Nat.add_mul _ _ _)

theorem dimension_mul {d e : ℕ} {p q : CurvatureJetPolynomial G}
    (hp : HasDimensionAtMost d p) (hq : HasDimensionAtMost e q) :
    HasDimensionAtMost (d + e) (p * q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  subst m
  rw [monomialDimension_add]
  exact Nat.add_le_add (hp a ha) (hq b hb)

/-- Evaluate on the actual connection's curvature and covariant derivatives. -/
def onConnection (p : CurvatureJetPolynomial G) (A : Connection G) (x : Spacetime) : ℝ :=
  p.evaluate (fun j => j.evaluate A x)

/-- Differential identities (including antisymmetry and Bianchi identities)
are identified by evaluation on all actual smooth connections. The formal
jet variables are intentionally independent before this relation is applied. -/
def sameOnConnections (p q : CurvatureJetPolynomial G) : Prop :=
  ∀ (A : Connection G) x, p.onConnection A x = q.onConnection A x

def connectionSetoid (G : CompactSimpleGaugeGroup) : Setoid (invariantAlgebra G) :=
  Setoid.ker (fun p : invariantAlgebra G =>
    fun (A : Connection G) (x : Spacetime) => (p : CurvatureJetPolynomial G).onConnection A x)

/-- Actual invariant polynomial observables, modulo identities on connections.
No assertion about a quantum renormalization map follows from this quotient. -/
def ConnectionObservable (G : CompactSimpleGaugeGroup) := Quotient (connectionSetoid G)

namespace ConnectionObservable

/-- Evaluation descends to the quotient precisely because equality there is
equality of evaluations on all smooth connections, rather than formal syntax. -/
def evaluate (o : ConnectionObservable G) : Connection G → Spacetime → ℝ :=
  Quotient.lift (fun p : invariantAlgebra G =>
    fun (A : Connection G) (x : Spacetime) => (p : CurvatureJetPolynomial G).onConnection A x)
    (fun _ _ h => h) o

@[simp] theorem evaluate_mk (p : invariantAlgebra G) (A : Connection G) (x : Spacetime) :
    evaluate (Quotient.mk (connectionSetoid G) p) A x =
      (p : CurvatureJetPolynomial G).onConnection A x := rfl

/-- The quotient filtration permits any equivalent representative, so a
formal expression's redundant high-dimension terms do not raise its bound. -/
def HasDimensionAtMost (d : ℕ) (o : ConnectionObservable G) : Prop :=
  ∃ p : invariantAlgebra G,
    Quotient.mk (connectionSetoid G) p = o ∧
      CurvatureJetPolynomial.HasDimensionAtMost d (p : CurvatureJetPolynomial G)

theorem finite_dimension (o : ConnectionObservable G) :
    ∃ d : ℕ, HasDimensionAtMost d o := by
  classical
  induction o using Quotient.inductionOn with
  | _ p =>
    refine ⟨(p : CurvatureJetPolynomial G).support.sup monomialDimension, p, rfl, ?_⟩
    intro m hm
    exact Finset.le_sup hm

theorem monotone {d e : ℕ} (hde : d ≤ e) (o : ConnectionObservable G)
    (h : HasDimensionAtMost d o) : HasDimensionAtMost e o := by
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, fun m hm => (hd m hm).trans hde⟩
end ConnectionObservable

/-- Pointwise invariance under local group-valued transformations of jets. -/
theorem invariant_under_local_transform (p : invariantAlgebra G)
    (u : Spacetime → G.Carrier) (j : Spacetime → CurvatureJetAssignment G)
    (x : Spacetime) :
    (p : CurvatureJetPolynomial G).evaluate (transform (u x) (j x)) =
      (p : CurvatureJetPolynomial G).evaluate (j x) :=
  p.property (u x) (j x)

/-- Gauge covariance of connection jets implies invariance on actual
connections. The explicit covariance premise is not yet proved geometrically. -/
theorem onConnection_eq_of_covariant_jets (p : invariantAlgebra G)
    (A A' : Connection G) (u : Spacetime → G.Carrier)
    (h : ∀ x (j : CurvatureJet), j.evaluate A' x = G.adjoint (u x) (j.evaluate A x))
    (x : Spacetime) :
    (p : CurvatureJetPolynomial G).onConnection A' x =
      (p : CurvatureJetPolynomial G).onConnection A x := by
  change (p : CurvatureJetPolynomial G).evaluate (fun j => j.evaluate A' x) = _
  have heq : (fun j => j.evaluate A' x) =
      transform (u x) (fun j => j.evaluate A x) := funext (h x)
  rw [heq]
  exact p.property (u x) _
end CurvatureJetPolynomial
end YangMills
