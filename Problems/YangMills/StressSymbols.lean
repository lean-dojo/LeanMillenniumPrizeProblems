import Problems.YangMills.Renormalization
import Problems.YangMills.StressTensor

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed perturbative stress symbols
The canonical stress symbol uses the same curvature polynomials as the action.
F_source = g F_canonical cancels the stress factor 1/g² algebraically before
coefficient extraction. These tree symbols impose no exact quantum trace identity.
-/
noncomputable section
namespace YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def canonicalLorentzSquare {B : InvariantForm G} (e : ColorFrame B) :
    PotentialPolynomial G :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ a : Fin G.dimension,
    MvPolynomial.C (metricSign ρ * metricSign σ) *
      canonicalCurvaturePolynomial e ρ σ a * canonicalCurvaturePolynomial e ρ σ a

/-- Contravariant stress in canonical fields, polynomial in g. -/
def canonicalStressPolynomial {B : InvariantForm G} (e : ColorFrame B)
    (μ ν : Fin 4) : PotentialPolynomial G :=
  -MvPolynomial.C (metricSign μ * metricSign ν) *
    (∑ ρ : Fin 4, ∑ a : Fin G.dimension,
      MvPolynomial.C (metricSign ρ) *
        canonicalCurvaturePolynomial e μ ρ a * canonicalCurvaturePolynomial e ν ρ a) +
    (if μ = ν then MvPolynomial.C (metricSign μ / 4) * canonicalLorentzSquare e else 0)

/-- Source numerator, before division by g². -/
def sourceStressNumerator {B : InvariantForm G} (e : ColorFrame B)
    (μ ν : Fin 4) : PotentialPolynomial G :=
  -MvPolynomial.C (metricSign μ * metricSign ν) *
    (∑ ρ : Fin 4, ∑ a : Fin G.dimension,
      MvPolynomial.C (metricSign ρ) *
        sourceCurvaturePolynomial e μ ρ a * sourceCurvaturePolynomial e ν ρ a) +
    (if μ = ν then MvPolynomial.C (metricSign μ / 4) *
      (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ a : Fin G.dimension,
        MvPolynomial.C (metricSign ρ * metricSign σ) *
          sourceCurvaturePolynomial e ρ σ a * sourceCurvaturePolynomial e ρ σ a) else 0)

/-- Algebraic cancellation is valid at the formal expansion point too. -/
theorem sourceStressNumerator_eq {B : InvariantForm G} (e : ColorFrame B)
    (μ ν : Fin 4) :
    sourceStressNumerator e μ ν = couplingPolynomial ^ 2 * canonicalStressPolynomial e μ ν := by
  unfold sourceStressNumerator canonicalStressPolynomial canonicalLorentzSquare
  simp only [sourceCurvaturePolynomial]
  have h (r : ℝ) (P Q : PotentialPolynomial G) :
      MvPolynomial.C r * (couplingPolynomial * P) * (couplingPolynomial * Q) =
        couplingPolynomial ^ 2 * (MvPolynomial.C r * P * Q) := by ring
  simp_rw [h, ← Finset.mul_sum]
  split_ifs <;> ring

/-- Tensor symmetry is a polynomial identity. -/
theorem canonicalStressPolynomial_symmetric {B : InvariantForm G} (e : ColorFrame B)
    (μ ν : Fin 4) : canonicalStressPolynomial e μ ν = canonicalStressPolynomial e ν μ := by
  unfold canonicalStressPolynomial
  have h : (∑ ρ : Fin 4, ∑ a : Fin G.dimension,
      MvPolynomial.C (metricSign ρ) * canonicalCurvaturePolynomial e μ ρ a *
        canonicalCurvaturePolynomial e ν ρ a) =
      ∑ ρ : Fin 4, ∑ a : Fin G.dimension,
      MvPolynomial.C (metricSign ρ) * canonicalCurvaturePolynomial e ν ρ a *
        canonicalCurvaturePolynomial e μ ρ a := by
    apply Finset.sum_congr rfl
    intro ρ _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [h, mul_comm (metricSign μ) (metricSign ν)]
  by_cases hμν : μ = ν
  · subst ν; rfl
  · simp [hμν, Ne.symm hμν]

/-- Evaluation in the same actual Lie algebra coordinates, with g a scalar
and every potential jet an actual tangent-algebra element. -/
def evaluatePotential {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (jets : (Fin 4 → ℕ) → Fin 4 → G.Algebra) : PotentialPolynomial G →+* ℝ :=
  MvPolynomial.eval (fun v => match v with
    | .inl _ => g
    | .inr (d, μ, a) => e.basis.repr (jets d μ) a)

/-- Curvature extraction uses the actual G bracket, rather than merely an
array called structure constants. The total derivative jets occur in the
same order as the connection's first derivatives. -/
theorem evaluatePotential_curvature {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (jets : (Fin 4 → ℕ) → Fin 4 → G.Algebra)
    (μ ν : Fin 4) (c : Fin G.dimension) :
    evaluatePotential e g jets (canonicalCurvaturePolynomial e μ ν c) =
      e.basis.repr
        (jets (Pi.single μ 1) ν - jets (Pi.single ν 1) μ +
          g • ⁅jets 0 μ, jets 0 ν⁆) c := by
  unfold canonicalCurvaturePolynomial
  rw [totalDerivative_potential, totalDerivative_potential]
  simp only [map_add, map_sub, map_mul, polynomialBracket, map_sum,
    evaluatePotential, MvPolynomial.eval_X, MvPolynomial.eval_C,
    potentialPolynomial, couplingPolynomial]
  simp only [map_smul, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [bracket_coordinates]

/-- Polarized color contraction in the actual orthonormal frame. -/
theorem color_inner_product {B : InvariantForm G} (e : ColorFrame B)
    (X Y : G.Algebra) :
    B.bilinear X Y = ∑ a : Fin G.dimension, e.basis.repr X a * e.basis.repr Y a := by
  conv_lhs => rw [← e.basis.sum_repr X]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [color_coordinate]

/-- Actual Lie-algebra evaluation of the canonical stress symbol. -/
def canonicalStressValue (B : InvariantForm G) (g : ℝ) (j : FieldJet G)
    (μ ν : Fin 4) : ℝ :=
  -(metricSign μ * metricSign ν) *
    (∑ ρ : Fin 4, metricSign ρ * B.bilinear (curvature g j μ ρ) (curvature g j ν ρ)) +
    (if μ = ν then metricSign μ / 4 else 0) *
      (∑ ρ : Fin 4, ∑ σ : Fin 4, metricSign ρ * metricSign σ *
        B.bilinear (curvature g j ρ σ) (curvature g j ρ σ))

/-- Polynomial stress extraction and geometric stress use the same G, B,
connection values and first derivatives. Higher jets cannot affect this symbol. -/
theorem evaluatePotential_stress {B : InvariantForm G} (e : ColorFrame B)
    (g : ℝ) (jets : (Fin 4 → ℕ) → Fin 4 → G.Algebra) (j : FieldJet G)
    (hzero : jets 0 = j.1)
    (hfirst : ∀ μ ν, jets (Pi.single μ 1) ν = j.2 μ ν)
    (μ ν : Fin 4) :
    evaluatePotential e g jets (canonicalStressPolynomial e μ ν) =
      canonicalStressValue B g j μ ν := by
  have hc (ρ σ : Fin 4) (a : Fin G.dimension) :
      evaluatePotential e g jets (canonicalCurvaturePolynomial e ρ σ a) =
        e.basis.repr (curvature g j ρ σ) a := by
    rw [evaluatePotential_curvature, hfirst, hfirst, hzero]
    rfl
  have hconst (r : ℝ) : evaluatePotential e g jets (MvPolynomial.C r) = r := by
    simp [evaluatePotential]
  unfold canonicalStressPolynomial canonicalLorentzSquare canonicalStressValue
  split_ifs <;>
    simp only [map_add, map_mul, map_neg, map_sum, map_zero, hconst, hc] <;>
    simp_rw [color_inner_product e, Finset.mul_sum] <;> simp [mul_assoc]

/-- The pre-existing geometric tensor and the fixed symbol share exactly
the same ordered contraction convention. -/
theorem classicalStress_eq_canonical (B : InvariantForm G) (g : ℝ)
    (A : Connection G) (x : Spacetime) (μ ν : Fin 4) :
    classicalStress B g A x μ ν =
      g⁻¹ ^ 2 * canonicalStressValue B 1 (connectionJet A x) μ ν := by
  simp only [classicalStress, canonicalStressValue, curvature_connectionJet]

/-- Source-field rescaling fixes the normalization at every nonzero g;
the polynomial identity itself also holds at g=0. -/
theorem canonicalStressValue_rescale (B : InvariantForm G) (g : ℝ)
    (j : FieldJet G) (μ ν : Fin 4) :
    canonicalStressValue B 1 (rescaleJet g j) μ ν =
      g ^ 2 * canonicalStressValue B g j μ ν := by
  unfold canonicalStressValue
  have hb (X Y : G.Algebra) :
      B.bilinear (g • X) (g • Y) = g ^ 2 * B.bilinear X Y := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hm (a b : ℝ) : a * (g ^ 2 * b) = g ^ 2 * (a * b) := by ring
  simp_rw [rescaled_curvature, hb, hm, ← Finset.mul_sum]
  ring

end YangMills.Perturbative
