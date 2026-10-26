import YangMills.RegulatedWardInsertion
import YangMills.MultiContact

/-!
# The fixed classical point-insertion BV contact term

Local insertions are not first integrated modulo divergences. Their jet
variational derivatives produce derivatives of delta(x-y). With output at
x, move the y-dependent polynomial to x by the exact finite Leibniz rule:
B(y) d_x^gamma delta = sum_(nu<=gamma) choose(gamma,nu)
  (d^nu B)(x) d_x^(gamma-nu) delta.
The sign (-1)^|beta| comes from d_y^beta delta = (-d_x)^beta delta.
This fixes the classical contact seed in FHH (335), including descendants.
-/
noncomputable section
open MeasureTheory
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- Every bounded multiindex, with no dependence on a selected field basis. -/
def subMultiindices (gamma : Fin 4 → ℕ) : Finset (Fin 4 → ℕ) := by
  classical
  exact (Finset.univ : Finset ((mu : Fin 4) → Fin (gamma mu + 1))).image
    (fun nu mu => (nu mu).val)

def multiBinomial (gamma nu : Fin 4 → ℕ) : ℕ :=
  ∏ mu : Fin 4, Nat.choose (gamma mu) (nu mu)

structure ClassicalContactTerm (G : CompactSimpleGaugeGroup) where
  coefficient : ℂ
  density : FullBV.JetAlgebra G
  derivatives : List (Fin 4)

/-- All classical channels are computed from actual ordered right/left jet
partials of P and Q. No coefficient tensor called a classical bracket is
supplied independently. The field coefficient is at the FIRST input point. -/
def classicalPointContact (P Q : FullBV.JetAlgebra G) : List (ClassicalContactTerm G) :=
  (FullBV.jetSupport P).toList.flatMap fun j =>
    (FullBV.jetSupport Q).toList.flatMap fun k =>
      if k.field = bvPartner j.field then
        (subMultiindices (j.derivative + k.derivative)).toList.map fun nu =>
          { coefficient := (if j.field.isLeft then 1 else -1) *
              (-1 : ℂ) ^ (∑ mu : Fin 4, k.derivative mu) *
              (multiBinomial (j.derivative + k.derivative) nu : ℂ),
            density := FullBV.rightPartialJet j P *
              FullBV.totalDerivatives nu (FullBV.leftPartialJet k Q),
            derivatives := orderedMultiindex (fun mu => j.derivative mu + k.derivative mu - nu mu) }
      else []

/-- Coefficient density of the specified ordinary delta multiindex, with
all coincident jet channels combined before further normalization. -/
def classicalPointContactDensity (P Q : FullBV.JetAlgebra G) (w : Fin 4 → ℕ) :
    FullBV.JetAlgebra G :=
  ((classicalPointContact P Q).map fun term =>
    if term.derivatives = orderedMultiindex w then term.coefficient • term.density else 0).sum

def classicalPointContactFlow (L : InsertedFlowFamily G)
    (A B : LocalMonomial G) (w : Fin 4 → ℕ) (x : Spacetime) : FlowFamily G :=
  boundedDensityInsertion L (A.dimension + B.dimension - 3 + 1)
    (classicalPointContactDensity (normalizedMonomialDensity A) (normalizedMonomialDensity B) w) x

/-- d_x^alpha delta(x-y) with its local field at x acts on f by
(d_y^alpha f)(x,x). This differs from the last-centered delta convention
in MultiContact; the coordinate meaning below is explicit. -/
def firstContactTest (directions : List (Fin 4)) : OPE.PairTestFunction →L[ℂ] TestFunction :=
  let diagonal : Spacetime →L[ℝ] (Spacetime × Spacetime) :=
    (ContinuousLinearMap.id ℝ Spacetime).prod (ContinuousLinearMap.id ℝ Spacetime)
  let restrict : OPE.PairTestFunction →L[ℂ] TestFunction :=
    SchwartzMap.compCLM ℂ diagonal.hasTemperateGrowth
      ⟨1, 1, by intro x; simp [diagonal, Prod.norm_def]⟩
  let rec derivative : List (Fin 4) → OPE.PairTestFunction →L[ℂ] OPE.PairTestFunction
    | [] => ContinuousLinearMap.id ℂ _
    | mu :: rest => (SchwartzMap.pderivCLM ℂ (0, Pi.single mu 1)).comp (derivative rest)
  restrict.comp (derivative directions)

/-- Apply the same renormalized local insertion amplitudes to every density
channel of the computed contact term. Only a finite local degree bound is
used, fixed from the input dimensions by the source bracket degree -3. -/
def classicalContactInsertion (L : InsertedFlowFamily G)
    (P Q : FullBV.JetAlgebra G) (degreeBound : ℕ) (test : OPE.PairTestFunction)
    (loop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : ℂ :=
  ((classicalPointContact P Q).map fun term => term.coefficient *
    ∫ x : Spacetime, firstContactTest term.derivatives test x *
      boundedDensityInsertion L (degreeBound + 1) term.density x loop Λ Λ0 legs q).sum

/-- The center integral is part of the definition's meaning, so it is guarded
before the contact insertion may enter a Ward identity. -/
def ClassicalContactIntegrability (L : InsertedFlowFamily G)
    (P Q : FullBV.JetAlgebra G) (degreeBound : ℕ) (test : OPE.PairTestFunction)
    (loop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : Prop :=
  ∀ term ∈ classicalPointContact P Q,
    Integrable (fun x : Spacetime => firstContactTest term.derivatives test x *
      boundedDensityInsertion L (degreeBound + 1) term.density x loop Λ Λ0 legs q)

end YangMills.PerturbativeFlow
